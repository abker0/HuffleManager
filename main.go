package main

import (
	"bytes"
	"container/heap"
	"encoding/binary"
	"fmt"
	"io"
	"log"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"

	"github.com/charmbracelet/bubbles/progress"
	"github.com/charmbracelet/bubbles/textinput"
	tea "github.com/charmbracelet/bubbletea"
	"github.com/charmbracelet/lipgloss"
)

const (
	magicOriginal       = "HUFF"
	magicChunked        = "HCHK"
	chunkSize           = 1 * 1024 * 1024
	minChunkableSize    = chunkSize * 2
	windowSize          = 4096
	lookaheadSize       = 64
	minMatchLength      = 3
	progressUpdateChunk = 64 * 1024
	maxLazySearchDepth  = 24

	maxMapPositions = 32
)

type compressedChunk struct {
	Index        int
	OriginalSize uint32
	CompSize     uint32
	TableSize    uint32
	HuffmanTable []CanonicalCode
	Data         []byte
	Err          error
}

type decompressedChunk struct {
	Index int
	Data  []byte
	Err   error
}

type tickMsg struct{}

type chunkMetadata struct {
	OriginalSize     uint32
	CompressedSize   uint32
	HuffmanTableSize uint32
	PayloadOffset    uint64
}

type model struct {
	choices        []string
	cursor         int
	selected       map[int]struct{}
	input          textinput.Model
	dirInput       textinput.Model
	mode           string
	progress       progress.Model
	percent        float64
	result         string
	done           bool
	activeInput    int
	startTime      time.Time
	bytesProcessed int64
	totalBytes     int64
	processingOp   string
	width          int
}

var (
	titleStyle = lipgloss.NewStyle().
			Bold(true).
			Foreground(lipgloss.Color("#FFCF40")).
			Align(lipgloss.Center)

	itemStyle = lipgloss.NewStyle().
			Align(lipgloss.Center)
	selectedItemStyle = lipgloss.NewStyle().
				Foreground(lipgloss.Color("#00FF00")).
				Align(lipgloss.Center)
	resultStyle = lipgloss.NewStyle().
			Italic(true).
			Foreground(lipgloss.Color("#1E90FF")).
			Align(lipgloss.Center)
	inputLabelStyle = lipgloss.NewStyle().
			Align(lipgloss.Center)
	activeInputLabelStyle = lipgloss.NewStyle().
				Foreground(lipgloss.Color("#00FF00")).
				Align(lipgloss.Center)
	helpTextStyle = lipgloss.NewStyle().
			Faint(true).
			Align(lipgloss.Center)

	inputBoxStyle = lipgloss.NewStyle().
			Border(lipgloss.NormalBorder(), true).
			Padding(0, 1)

	aboutBoxStyle = lipgloss.NewStyle().
			Border(lipgloss.NormalBorder(), true).
			BorderForeground(lipgloss.Color("#00FF00")).
			Padding(1, 2).
			Align(lipgloss.Center)
)

func initialModel() model {
	ti := textinput.New()
	ti.Placeholder = "Enter file path (any file)"
	ti.Focus()
	ti.CharLimit = 256
	ti.Width = 50

	di := textinput.New()
	di.Placeholder = "Enter output directory name (optional)"
	di.CharLimit = 100
	di.Width = 50

	p := progress.New(progress.WithDefaultGradient())
	p.Width = 50

	return model{
		choices: []string{
			"Compress a file",
			"Decompress a file",
			"About",
			"Quit",
		},
		selected:    make(map[int]struct{}),
		input:       ti,
		dirInput:    di,
		progress:    p,
		percent:     0.0,
		mode:        "menu",
		activeInput: 0,
	}
}

type huffmanNode struct {
	frequency int
	char      int
	left      *huffmanNode
	right     *huffmanNode
}

type ByFrequency []*huffmanNode

func (bf ByFrequency) Len() int           { return len(bf) }
func (bf ByFrequency) Less(i, j int) bool { return bf[i].frequency < bf[j].frequency }
func (bf ByFrequency) Swap(i, j int)      { bf[i], bf[j] = bf[j], bf[i] }

type huffmanHeap []*huffmanNode

func (h huffmanHeap) Len() int           { return len(h) }
func (h huffmanHeap) Less(i, j int) bool { return h[i].frequency < h[j].frequency }
func (h huffmanHeap) Swap(i, j int)      { h[i], h[j] = h[j], h[i] }

func (h *huffmanHeap) Push(x interface{}) {
	*h = append(*h, x.(*huffmanNode))
}

func (h *huffmanHeap) Pop() interface{} {
	old := *h
	n := len(old)
	x := old[n-1]
	*h = old[0 : n-1]
	return x
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func min64(a, b int64) int64 {
	if a < b {
		return a
	}
	return b
}

func findMatch(window []byte, lookahead []byte) (length int, offset int) {

	if len(lookahead) < minMatchLength || len(window) == 0 {
		return 0, -1
	}

	maxLength := 0
	maxOffset := -1
	maxMatchLen := min(len(lookahead), lookaheadSize)

	limitScanDepth := min(len(window), 512)

	for i := len(window) - 1; i >= len(window)-limitScanDepth && i >= 0; i-- {

		if i < 0 || i >= len(window) || 0 >= len(lookahead) || window[i] != lookahead[0] {
			continue
		}

		j := 0
		for j < maxMatchLen && i+j < len(window) && j < len(lookahead) && window[i+j] == lookahead[j] {
			j++
		}
		if j >= minMatchLength && j > maxLength {
			maxLength = j
			maxOffset = i

		}
	}

	if maxLength >= minMatchLength && (maxOffset < 0 || maxOffset >= len(window)) {
		log.Printf("findMatch internal warning: Invalid maxOffset %d for window size %d, length %d. Resetting.", maxOffset, len(window), maxLength)
		return 0, -1
	}

	if maxLength < minMatchLength {
		return 0, -1
	}

	return maxLength, maxOffset
}

func buildHuffmanTree(frequencies map[int]int) *huffmanNode {
	h := &huffmanHeap{}
	heap.Init(h)

	for char, freq := range frequencies {
		heap.Push(h, &huffmanNode{frequency: freq, char: char})
	}

	if h.Len() == 0 {
		return nil
	}
	if h.Len() == 1 {
		singleNode := heap.Pop(h).(*huffmanNode)
		return &huffmanNode{frequency: singleNode.frequency, left: singleNode, right: nil, char: -1}
	}

	for h.Len() > 1 {
		left := heap.Pop(h).(*huffmanNode)
		right := heap.Pop(h).(*huffmanNode)
		merged := &huffmanNode{frequency: left.frequency + right.frequency, left: left, right: right, char: -1}
		heap.Push(h, merged)
	}
	return heap.Pop(h).(*huffmanNode)
}

func generateHuffmanCodes(node *huffmanNode, currentCode string, codes map[int]string) {
	if node == nil {
		return
	}
	if node.left == nil && node.right == nil {
		if currentCode == "" {
			codes[node.char] = "0"
		} else {
			codes[node.char] = currentCode
		}
		return
	}
	generateHuffmanCodes(node.left, currentCode+"0", codes)
	generateHuffmanCodes(node.right, currentCode+"1", codes)
}

type BitWriter struct {
	buffer      bytes.Buffer
	currentByte byte
	bitCount    uint8
}

func NewBitWriter() *BitWriter {
	return &BitWriter{}
}

func (bw *BitWriter) WriteBit(bit uint8) {
	bw.currentByte = (bw.currentByte << 1) | (bit & 1)
	bw.bitCount++
	if bw.bitCount == 8 {
		bw.buffer.WriteByte(bw.currentByte)
		bw.currentByte = 0
		bw.bitCount = 0
	}
}

func (bw *BitWriter) WriteBits(bits string) {
	for _, bit := range bits {
		if bit == '1' {
			bw.WriteBit(1)
		} else {
			bw.WriteBit(0)
		}
	}
}

func (bw *BitWriter) Flush() {
	if bw.bitCount > 0 {
		bw.currentByte <<= (8 - bw.bitCount)
		bw.buffer.WriteByte(bw.currentByte)
		bw.currentByte = 0
		bw.bitCount = 0
	}
}

func (bw *BitWriter) Bytes() []byte {
	return bw.buffer.Bytes()
}

type BitReader struct {
	data    []byte
	bytePos int
	bitPos  uint8
	eofOk   bool
}

func NewBitReader(data []byte) *BitReader {
	return &BitReader{
		data:    data,
		bytePos: 0,
		bitPos:  0,
		eofOk:   false,
	}
}

func (br *BitReader) AllowEOF(allow bool) {
	br.eofOk = allow
}

func (br *BitReader) ReadBit() (uint8, error) {
	if br.bytePos >= len(br.data) {
		if br.eofOk {
			return 0, io.EOF
		}
		return 0, fmt.Errorf("unexpected end of data")
	}

	bit := (br.data[br.bytePos] >> (7 - br.bitPos)) & 1

	br.bitPos++
	if br.bitPos == 8 {
		br.bytePos++
		br.bitPos = 0
	}

	return bit, nil
}

func (br *BitReader) IsEOF() bool {
	return br.bytePos >= len(br.data)
}

type ProgressMsg struct {
	Processed int64
	Total     int64
}

type FileOperationFinishedMsg struct {
	Result string
	Err    error
}

type CanonicalCode struct {
	Symbol int
	Length int
}

func SendProgress(processed, total int64) tea.Msg {
	return ProgressMsg{Processed: processed, Total: total}
}

func tickCmd() tea.Cmd {
	return tea.Tick(5*time.Second, func(t time.Time) tea.Msg {
		return tickMsg{}
	})
}

func compressChunk(chunkData []byte, chunkIndex int) compressedChunk {
	if len(chunkData) == 0 {
		return compressedChunk{Index: chunkIndex, OriginalSize: 0, TableSize: 0, CompSize: 0, HuffmanTable: []CanonicalCode{}, Data: []byte{}, Err: nil}
	}

	var tokens []int
	position := 0

	windowMap := make(map[[3]byte][]int)

	for position < len(chunkData) {

		if position > 0 && position+2 < len(chunkData) {
			var prevKey [3]byte
			copy(prevKey[:], chunkData[position-1:position+2])
			windowMap[prevKey] = append(windowMap[prevKey], position-1)

			if len(windowMap[prevKey]) > maxMapPositions {

				windowMap[prevKey] = windowMap[prevKey][len(windowMap[prevKey])-maxMapPositions:]
			}
		}

		windowStart := max(0, position-windowSize)

		window := chunkData[windowStart:position]

		if position >= len(chunkData) {
			break
		}

		remainingBytes := len(chunkData) - position
		lookAheadSizeActual := min(remainingBytes, lookaheadSize)
		lookahead := chunkData[position : position+lookAheadSizeActual]

		matchLength, matchPosInWindow := findMatch(window, lookahead)

		lazyMatch := false
		if matchLength >= minMatchLength && position+1 < len(chunkData) && remainingBytes > 1 {
			nextLookahead := chunkData[position+1 : min(position+1+lookaheadSize, len(chunkData))]

			nextMatchLengthLazy, _ := findMatch(window, nextLookahead)

			if nextMatchLengthLazy > matchLength && (nextMatchLengthLazy-matchLength) > 1 {
				tokens = append(tokens, int(chunkData[position]))
				position++
				lazyMatch = true
				continue
			}
		}

		if matchLength >= minMatchLength && !lazyMatch {
			distance := len(window) - matchPosInWindow

			if distance <= 0 || matchPosInWindow < 0 {
				log.Printf("Chunk Compress Warning: Invalid distance/offset at chunk pos %d (matchPos %d, windowLen %d)", position, matchPosInWindow, len(window))
				tokens = append(tokens, int(chunkData[position]))
				position++
				continue
			}

			if distance > windowSize {
				log.Printf("Chunk Compress Warning: Calculated distance %d > windowSize %d", distance, windowSize)
				tokens = append(tokens, int(chunkData[position]))
				position++
				continue
			}

			distance = max(1, distance&0xFFF)
			length := min(matchLength, 1023)
			token := 256 + (length << 12) + distance
			tokens = append(tokens, token)
			position += length
		} else {
			tokens = append(tokens, int(chunkData[position]))
			position++
		}
	}

	frequencies := make(map[int]int)
	for _, token := range tokens {
		frequencies[token]++
	}

	huffmanTree := buildHuffmanTree(frequencies)
	if huffmanTree == nil && len(tokens) > 0 {
		return compressedChunk{Index: chunkIndex, Err: fmt.Errorf("failed to build Huffman tree for non-empty chunk %d tokens", chunkIndex)}
	} else if huffmanTree == nil && len(tokens) == 0 {
		return compressedChunk{Index: chunkIndex, OriginalSize: uint32(len(chunkData)), TableSize: 0, CompSize: 0, HuffmanTable: []CanonicalCode{}, Data: []byte{}, Err: nil}
	}

	initialCodes := make(map[int]string)
	generateHuffmanCodes(huffmanTree, "", initialCodes)
	canonicalCodes := generateCanonicalCodes(initialCodes)
	codes := canonicalToStringCodes(canonicalCodes)

	payloadWriter := NewBitWriter()
	for _, token := range tokens {
		code, ok := codes[token]
		if !ok {
			return compressedChunk{Index: chunkIndex, Err: fmt.Errorf("no Huffman code found for token %d in chunk %d", token, chunkIndex)}
		}
		payloadWriter.WriteBits(code)
	}
	payloadWriter.Flush()
	compressedPayload := payloadWriter.Bytes()

	return compressedChunk{
		Index:        chunkIndex,
		OriginalSize: uint32(len(chunkData)),
		HuffmanTable: canonicalCodes,
		Data:         compressedPayload,
		TableSize:    uint32(len(canonicalCodes)),
		CompSize:     uint32(len(compressedPayload)),
		Err:          nil,
	}
}

func compressFileLogic(inputPath string, outputDir string, p *tea.Program) FileOperationFinishedMsg {
	log.Printf("--- Compress Start (Chunked): %s ---", inputPath)

	startTime := time.Now()

	if outputDir != "" {
		err := os.MkdirAll(outputDir, 0755)
		if err != nil {
			log.Printf("Compress Error: Failed to create output directory %s: %v", outputDir, err)
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error creating output directory: %v", err), Err: err}
		}
	}

	inputFile, err := os.Open(inputPath)
	if err != nil {
		log.Printf("Compress Error: Failed to open input file: %v", err)
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error opening input file: %v", err), Err: err}
	}
	defer inputFile.Close()

	fileInfo, err := inputFile.Stat()
	if err != nil {
		log.Printf("Compress Error: Failed to get file stats: %v", err)
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading file info: %v", err), Err: err}
	}

	inputSize := fileInfo.Size()
	originalFilename := filepath.Base(inputPath)
	log.Printf("Compress Info: Original filename: %s, Size: %d bytes", originalFilename, inputSize)

	if inputSize == 0 {
		log.Printf("Compress Info: Empty file detected, writing empty chunked file with .huff extension")

		baseName := filepath.Base(inputPath)
		ext := filepath.Ext(baseName)
		baseNameNoExt := strings.TrimSuffix(baseName, ext)
		outputBaseName := baseNameNoExt + ".huff"
		outputPath := filepath.Join(outputDir, outputBaseName)
		if outputDir == "" {

			inputDir := filepath.Dir(inputPath)
			outputPath = filepath.Join(inputDir, outputBaseName)
		}
		outFile, err := os.Create(outputPath)
		if err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error creating empty output file: %v", err), Err: err}
		}
		defer outFile.Close()

		if _, err = outFile.WriteString(magicChunked); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing magic (empty): %v", err), Err: err}
		}
		if err = binary.Write(outFile, binary.LittleEndian, uint16(len(originalFilename))); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing fname len (empty): %v", err), Err: err}
		}
		if _, err = outFile.WriteString(originalFilename); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing fname (empty): %v", err), Err: err}
		}
		if err = binary.Write(outFile, binary.LittleEndian, uint64(0)); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing total size (empty): %v", err), Err: err}
		}
		if err = binary.Write(outFile, binary.LittleEndian, uint32(0)); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing chunk count (empty): %v", err), Err: err}
		}

		if p != nil {
			p.Send(SendProgress(0, 0))
		}
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Compression complete (empty file): %s", outputPath), Err: nil}
	}

	numWorkers := runtime.NumCPU()
	numChunks := int(inputSize / chunkSize)
	if inputSize%chunkSize != 0 {
		numChunks++
	}
	log.Printf("Compress Info: Input size %d, Chunk size %d, Num chunks %d, Workers %d", inputSize, chunkSize, numChunks, numWorkers)

	inputBytes, err := io.ReadAll(inputFile)
	if err != nil {
		log.Printf("Compress Error: Failed to read file data: %v", err)
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading file data: %v", err), Err: err}
	}
	inputFile.Close()

	if p != nil {
		p.Send(SendProgress(0, inputSize))
	}

	chunkJobs := make(chan int, numChunks)
	chunkResults := make(chan compressedChunk, numChunks)
	var wg sync.WaitGroup

	for i := 0; i < numWorkers; i++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()
			for chunkIndex := range chunkJobs {
				start := int64(chunkIndex) * chunkSize
				end := min64(start+chunkSize, inputSize)
				chunkData := inputBytes[start:end]

				result := compressChunk(chunkData, chunkIndex)
				chunkResults <- result
			}
		}(i)
	}

	for i := 0; i < numChunks; i++ {
		chunkJobs <- i
	}
	close(chunkJobs)

	results := make([]compressedChunk, numChunks)
	var firstErr error
	chunksProcessed := 0
	for i := 0; i < numChunks; i++ {
		result := <-chunkResults
		if result.Err != nil {
			log.Printf("Error in chunk %d: %v", result.Index, result.Err)
			if firstErr == nil {
				firstErr = result.Err
			}
		}

		if result.Index >= 0 && result.Index < numChunks {
			results[result.Index] = result
		} else {
			log.Printf("Error: Received result with invalid index %d", result.Index)
			if firstErr == nil {
				firstErr = fmt.Errorf("invalid chunk index received: %d", result.Index)
			}
		}
		chunksProcessed++
		if p != nil {
			var processedBytes int64
			for _, r := range results[:chunksProcessed] {
				if r.Index != 0 || r.OriginalSize != 0 {
					processedBytes += int64(r.OriginalSize)
				}
			}
			displayBytes := min64(processedBytes, inputSize)
			p.Send(SendProgress(displayBytes, inputSize))
		}
	}
	wg.Wait()
	log.Printf("All results collected.")

	if firstErr != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error during chunk compression: %v", firstErr), Err: firstErr}
	}

	baseName := filepath.Base(inputPath)
	ext := filepath.Ext(baseName)
	baseNameNoExt := strings.TrimSuffix(baseName, ext)
	outputBaseName := baseNameNoExt + ".huff"
	outputPath := filepath.Join(outputDir, outputBaseName)
	if outputDir == "" {

		inputDir := filepath.Dir(inputPath)
		outputPath = filepath.Join(inputDir, outputBaseName)
	}

	outFile, err := os.Create(outputPath)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error creating output file: %v", err), Err: err}
	}
	defer outFile.Close()

	if _, err = outFile.WriteString(magicChunked); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing magic: %v", err), Err: err}
	}
	if err = binary.Write(outFile, binary.LittleEndian, uint16(len(originalFilename))); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing fname len: %v", err), Err: err}
	}
	if _, err = outFile.WriteString(originalFilename); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing fname: %v", err), Err: err}
	}
	if err = binary.Write(outFile, binary.LittleEndian, uint64(inputSize)); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing total size: %v", err), Err: err}
	}
	if err = binary.Write(outFile, binary.LittleEndian, uint32(numChunks)); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing chunk count: %v", err), Err: err}
	}

	metadataIndex := make([]chunkMetadata, numChunks)
	headerSize, _ := outFile.Seek(0, io.SeekCurrent)
	indexSize := int64(binary.Size(chunkMetadata{})) * int64(numChunks)
	offsetAfterIndex := headerSize + indexSize
	currentTableAndDataOffset := uint64(offsetAfterIndex)

	for i, res := range results {
		tableByteSize := uint64(res.TableSize) * uint64(binary.Size(uint32(0))+binary.Size(uint8(0)))
		payloadOffset := currentTableAndDataOffset + tableByteSize

		meta := chunkMetadata{
			OriginalSize:     res.OriginalSize,
			CompressedSize:   res.CompSize,
			HuffmanTableSize: res.TableSize,
			PayloadOffset:    payloadOffset,
		}
		metadataIndex[i] = meta
		currentTableAndDataOffset += tableByteSize + uint64(res.CompSize)
	}

	for _, meta := range metadataIndex {
		if err = binary.Write(outFile, binary.LittleEndian, meta); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing metadata index: %v", err), Err: err}
		}
	}

	for i, res := range results {
		for _, codeEntry := range res.HuffmanTable {
			if err = binary.Write(outFile, binary.LittleEndian, uint32(codeEntry.Symbol)); err != nil {
				return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing table symbol %d: %v", i, err), Err: err}
			}
			if err = binary.Write(outFile, binary.LittleEndian, uint8(codeEntry.Length)); err != nil {
				return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing table length %d: %v", i, err), Err: err}
			}
		}

		nWritten, err := outFile.Write(res.Data)
		if err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing chunk %d data: %v", i, err), Err: err}
		}
		if nWritten != int(res.CompSize) {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Short write for chunk %d data", i), Err: io.ErrShortWrite}
		}
	}

	finalCompressedSize, _ := outFile.Seek(0, io.SeekCurrent)
	outFile.Close()

	if p != nil {
		p.Send(SendProgress(inputSize, inputSize))
	}

	var reduction float64
	if inputSize > 0 {
		reduction = 100.0 * (1.0 - float64(finalCompressedSize)/float64(inputSize))
	}

	duration := time.Since(startTime)
	resultMsg := fmt.Sprintf("Compression complete: %s (%.2f%% reduction, %s)", outputPath, reduction, duration)
	log.Printf("--- Compress Success (Chunked): %s --- Size: %d bytes (%.2f%% reduction) in %s", inputPath, finalCompressedSize, reduction, duration)
	return FileOperationFinishedMsg{Result: resultMsg, Err: nil}
}

func decompressFileLogic(inputPath string, outputDir string, p *tea.Program) FileOperationFinishedMsg {
	log.Printf("--- Decompress Start: %s ---", inputPath)
	startTime := time.Now()

	compressedFile, err := os.Open(inputPath)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error opening file: %v", err), Err: err}
	}
	defer compressedFile.Close()

	magicBytes := make([]byte, 4)
	if _, err := io.ReadFull(compressedFile, magicBytes); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading magic number: %v", err), Err: err}
	}
	magic := string(magicBytes)

	if magic == magicOriginal {
		log.Printf("Decompress Info: Detected original HUFF format.")
		if _, err := compressedFile.Seek(0, io.SeekStart); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error seeking file: %v", err), Err: err}
		}
		return decompressOriginalFormat(compressedFile, inputPath, outputDir, p)
	}

	if magic != magicChunked {
		return FileOperationFinishedMsg{Result: "Error: Unknown file format", Err: fmt.Errorf("unknown magic number: %s", magic)}
	}
	log.Printf("Decompress Info: Detected chunked HCHK format.")

	var filenameLen uint16
	if err := binary.Read(compressedFile, binary.LittleEndian, &filenameLen); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading chunked fname len: %v", err), Err: err}
	}

	filenameBytes := make([]byte, filenameLen)
	if _, err := io.ReadFull(compressedFile, filenameBytes); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading chunked fname: %v", err), Err: err}
	}
	originalFilename := string(filenameBytes)

	var originalTotalSize uint64
	if err := binary.Read(compressedFile, binary.LittleEndian, &originalTotalSize); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading chunked total size: %v", err), Err: err}
	}

	var numChunks uint32
	if err := binary.Read(compressedFile, binary.LittleEndian, &numChunks); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading chunked count: %v", err), Err: err}
	}

	log.Printf("Decompress Chunked Info: Filename: %s, Total Size: %d, Chunks: %d", originalFilename, originalTotalSize, numChunks)

	if originalTotalSize == 0 {
		log.Printf("Decompress Info: Original file was empty (chunked format)")
		outputPath := determineOutputPath(inputPath, outputDir, originalFilename)
		outFile, err := os.Create(outputPath)
		if err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error creating empty output: %v", err), Err: err}
		}
		outFile.Close()
		if p != nil {
			p.Send(SendProgress(0, 0))
		}
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Decompression complete (empty file): %s", outputPath), Err: nil}
	}

	log.Printf("Reading chunk metadata index...")
	metadataIndex := make([]chunkMetadata, numChunks)
	if err := binary.Read(compressedFile, binary.LittleEndian, &metadataIndex); err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading metadata index: %v", err), Err: err}
	}
	offsetAfterIndex, _ := compressedFile.Seek(0, io.SeekCurrent)

	if p != nil {
		p.Send(SendProgress(0, int64(originalTotalSize)))
	}

	numWorkers := runtime.NumCPU()
	decompJobs := make(chan int, numChunks)
	decompResults := make(chan decompressedChunk, numChunks)
	var wg sync.WaitGroup
	outputChunks := make([][]byte, numChunks)
	var firstErr error
	var mu sync.Mutex

	log.Printf("Launching %d decompression workers...", numWorkers)
	for i := 0; i < numWorkers; i++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()

			var nRead int
			var err error
			for chunkIndex := range decompJobs {
				meta := metadataIndex[chunkIndex]

				chunkTableStartOffset := offsetAfterIndex
				for k := 0; k < chunkIndex; k++ {
					prevMeta := metadataIndex[k]
					tableByteSize := uint64(prevMeta.HuffmanTableSize) * uint64(binary.Size(uint32(0))+binary.Size(uint8(0)))
					chunkTableStartOffset += int64(tableByteSize + uint64(prevMeta.CompressedSize))
				}

				tableBytesSize := uint64(meta.HuffmanTableSize) * uint64(binary.Size(uint32(0))+binary.Size(uint8(0)))
				tableBytes := make([]byte, tableBytesSize)

				nRead, err = compressedFile.ReadAt(tableBytes, chunkTableStartOffset)
				if err != nil && err != io.EOF {
					log.Printf("Worker %d ERROR reading table for chunk %d: %v", workerID, chunkIndex, err)
					decompResults <- decompressedChunk{Index: chunkIndex, Err: fmt.Errorf("read table failed: %v", err)}
					continue
				}
				if uint64(nRead) != tableBytesSize {
					log.Printf("Worker %d ERROR short read table for chunk %d (%d != %d)", workerID, chunkIndex, nRead, tableBytesSize)
					decompResults <- decompressedChunk{Index: chunkIndex, Err: fmt.Errorf("short read table")}
					continue
				}

				payloadBytes := make([]byte, meta.CompressedSize)
				payloadReadOffset := int64(meta.PayloadOffset)

				nRead, err = compressedFile.ReadAt(payloadBytes, payloadReadOffset)
				if err != nil && err != io.EOF {
					log.Printf("Worker %d ERROR reading payload for chunk %d at offset %d: %v", workerID, chunkIndex, payloadReadOffset, err)
					decompResults <- decompressedChunk{Index: chunkIndex, Err: fmt.Errorf("read payload failed: %v", err)}
					continue
				}
				if nRead != int(meta.CompressedSize) {
					log.Printf("Worker %d ERROR short read payload for chunk %d (%d != %d)", workerID, chunkIndex, nRead, meta.CompressedSize)
					decompResults <- decompressedChunk{Index: chunkIndex, Err: fmt.Errorf("short read payload")}
					continue
				}

				decompData, decompErr := decompressChunk(tableBytes, payloadBytes, meta.OriginalSize)
				if decompErr != nil {
					log.Printf("Worker %d ERROR decompressing chunk %d: %v", workerID, chunkIndex, decompErr)
					decompResults <- decompressedChunk{Index: chunkIndex, Err: fmt.Errorf("decompression failed: %v", decompErr)}
					continue
				}

				decompResults <- decompressedChunk{Index: chunkIndex, Data: decompData, Err: nil}
			}
		}(i)
	}

	for i := 0; i < int(numChunks); i++ {
		decompJobs <- i
	}
	close(decompJobs)

	chunksProcessed := 0
	var totalOriginalBytesCollected int64
	for i := 0; i < int(numChunks); i++ {
		result := <-decompResults
		if result.Err != nil {
			mu.Lock()
			if firstErr == nil {
				firstErr = result.Err
			}
			mu.Unlock()
		}
		if result.Index >= 0 && result.Index < int(numChunks) {
			outputChunks[result.Index] = result.Data
			totalOriginalBytesCollected += int64(len(result.Data))
		} else {
			mu.Lock()
			if firstErr == nil {
				firstErr = fmt.Errorf("invalid chunk index %d received", result.Index)
			}
			mu.Unlock()
		}
		chunksProcessed++
		if p != nil {
			p.Send(SendProgress(totalOriginalBytesCollected, int64(originalTotalSize)))
		}
	}
	wg.Wait()
	log.Printf("All decompression workers finished.")

	if firstErr != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error during chunk decompression: %v", firstErr), Err: firstErr}
	}

	outputPath := determineOutputPath(inputPath, outputDir, originalFilename)
	outFile, err := os.Create(outputPath)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error creating output file: %v", err), Err: err}
	}
	defer outFile.Close()

	log.Printf("Assembling and writing final output to %s...", outputPath)
	var totalBytesWritten int64
	for i, chunkData := range outputChunks {
		nWritten, err := outFile.Write(chunkData)
		if err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing chunk %d to output: %v", i, err), Err: err}
		}
		totalBytesWritten += int64(nWritten)
	}

	if uint64(totalBytesWritten) != originalTotalSize {
		log.Printf("Decompress Warning: Final size %d does not match expected size %d", totalBytesWritten, originalTotalSize)
	}

	if p != nil {
		p.Send(SendProgress(int64(originalTotalSize), int64(originalTotalSize)))
	}

	duration := time.Since(startTime)
	resultMsg := fmt.Sprintf("Decompression complete: %s (%s)", outputPath, duration)
	log.Printf("--- Decompress Success (Chunked): %s --- Wrote %d bytes in %s", inputPath, totalBytesWritten, duration)
	return FileOperationFinishedMsg{Result: resultMsg, Err: nil}
}

func decompressChunk(tableBytes, payloadBytes []byte, originalChunkSize uint32) ([]byte, error) {
	if originalChunkSize == 0 {
		return []byte{}, nil
	}

	tableReader := bytes.NewReader(tableBytes)
	var canonicalCodes []CanonicalCode
	tableEntrySize := binary.Size(uint32(0)) + binary.Size(uint8(0))
	if len(tableBytes)%tableEntrySize != 0 {
		return nil, fmt.Errorf("invalid table byte size %d", len(tableBytes))
	}
	numCodesInTable := len(tableBytes) / tableEntrySize

	for i := 0; i < numCodesInTable; i++ {
		var symbol uint32
		var codeLength uint8
		if err := binary.Read(tableReader, binary.LittleEndian, &symbol); err != nil {
			return nil, fmt.Errorf("parse table symbol failed: %v", err)
		}
		if err := binary.Read(tableReader, binary.LittleEndian, &codeLength); err != nil {
			return nil, fmt.Errorf("parse table length failed: %v", err)
		}
		if codeLength == 0 || codeLength > 64 {
			return nil, fmt.Errorf("invalid code length %d in table", codeLength)
		}
		canonicalCodes = append(canonicalCodes, CanonicalCode{Symbol: int(symbol), Length: int(codeLength)})
	}

	if len(canonicalCodes) == 0 && originalChunkSize > 0 {
		return nil, fmt.Errorf("no huffman codes found for non-empty chunk")
	}

	huffmanRoot, err := rebuildHuffmanTree(canonicalCodes)
	if err != nil {
		return nil, fmt.Errorf("rebuild tree failed: %v", err)
	}
	if huffmanRoot == nil && originalChunkSize > 0 {
		return nil, fmt.Errorf("rebuild tree failed (nil root) for non-empty file")
	}

	var tokens []int
	bitReader := NewBitReader(payloadBytes)
	bitReader.AllowEOF(true)
	currentNode := huffmanRoot
	eofReached := false
	estimatedSize := 0

	for uint32(estimatedSize) < originalChunkSize && !eofReached {
		if currentNode == nil {
			return nil, fmt.Errorf("huffman traversal error in chunk")
		}
		if currentNode.left == nil && currentNode.right == nil {
			if currentNode.char == -1 {
				return nil, fmt.Errorf("invalid huffman sequence in chunk")
			}
			token := currentNode.char
			tokens = append(tokens, token)

			if token < 256 {
				estimatedSize++
			} else {
				tokenVal := token - 256
				length := (tokenVal >> 12) & 0x3FF
				estimatedSize += length
			}
			currentNode = huffmanRoot
			if uint32(estimatedSize) >= originalChunkSize {
				break
			}
			if bitReader.IsEOF() {
				eofReached = true
			}
			continue
		}
		bit, err := bitReader.ReadBit()
		if err == io.EOF {
			if currentNode != huffmanRoot {
				if currentNode.left == nil && currentNode.right == nil && currentNode.char != -1 {
					token := currentNode.char
					tokens = append(tokens, token)

					if token < 256 {
						estimatedSize++
					} else {
						tokenVal := token - 256
						length := (tokenVal >> 12) & 0x3FF
						estimatedSize += length
					}
				} else {
					log.Printf("Chunk Decompress Warning: EOF reached with incomplete Huffman code sequence.")
				}
			}
			eofReached = true
			break
		} else if err != nil {
			return nil, fmt.Errorf("bit read error in chunk: %v", err)
		}
		if bit == 1 {
			currentNode = currentNode.right
		} else {
			currentNode = currentNode.left
		}
		if currentNode == nil {
			return nil, fmt.Errorf("invalid huffman bits in chunk")
		}
	}

	outputBuffer := make([]byte, originalChunkSize)

	writePos := 0

	decompressedBytes := 0

	for i, token := range tokens {

		if writePos >= int(originalChunkSize) {
			log.Printf("Chunk Decompress Warning: Attempted to write past originalChunkSize at token %d", i)
			break
		}

		if token < 256 {

			outputBuffer[writePos] = byte(token)
			writePos++
			decompressedBytes++
		} else {
			tokenVal := token - 256
			length := (tokenVal >> 12) & 0x3FF
			distance := tokenVal & 0xFFF
			if distance <= 0 || length <= 0 {
				log.Printf("Chunk Decompress Warning: Skipping invalid LZ77 token (%d, %d) at index %d", length, distance, i)
				continue
			}

			startPos := writePos - distance
			if startPos < 0 {
				return nil, fmt.Errorf("invalid LZ77 distance %d results in negative startPos %d at writePos %d", distance, startPos, writePos)
			}

			bytesToCopy := length
			if writePos+bytesToCopy > int(originalChunkSize) {
				log.Printf("Chunk Decompress Warning: LZ77 copy length %d truncated to %d at writePos %d", length, int(originalChunkSize)-writePos, writePos)
				bytesToCopy = int(originalChunkSize) - writePos
			}

			if bytesToCopy <= 0 {
				continue
			}

			bytesCopied := 0
			for i := 0; i < bytesToCopy; i++ {
				srcIdx := startPos + i
				dstIdx := writePos + i

				if srcIdx < 0 || srcIdx >= len(outputBuffer) {
					return nil, fmt.Errorf("LZ77 copy source index %d out of bounds", srcIdx)
				}
				if dstIdx < 0 || dstIdx >= len(outputBuffer) {
					log.Printf("Chunk Decompress Warning: LZ77 destination index %d out of bounds, copy truncated", dstIdx)
					break
				}

				outputBuffer[dstIdx] = outputBuffer[srcIdx]
				bytesCopied++
			}

			writePos += bytesCopied
			decompressedBytes += bytesCopied
		}
	}

	if writePos != int(originalChunkSize) {
		log.Printf("Chunk Decompress Warning: Final write position %d does not match expected original size %d", writePos, originalChunkSize)

		return outputBuffer[:writePos], nil
	}

	return outputBuffer, nil
}

func decompressOriginalFormat(f *os.File, inputPath string, outputDir string, p *tea.Program) FileOperationFinishedMsg {
	log.Printf("--- Decompress Start (Original HUFF Format): %s ---", inputPath)

	_, err := f.Seek(0, io.SeekCurrent)
	if err != nil {
		log.Printf("Warning: Seek failed before ReadAll in original format: %v", err)
	}
	compressedDataFromRead, err := io.ReadAll(f)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading original format data: %v", err), Err: err}
	}
	fullCompressedData := append([]byte(magicOriginal), compressedDataFromRead...)

	reader := bytes.NewReader(fullCompressedData[4:])

	var filenameLen uint16
	err = binary.Read(reader, binary.LittleEndian, &filenameLen)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error: Invalid header (filename length): %v", err), Err: err}
	}

	filenameBytes := make([]byte, filenameLen)
	n, err := io.ReadFull(reader, filenameBytes)
	if err != nil || n != int(filenameLen) {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error: Invalid header (filename): %v", err), Err: err}
	}
	originalFilename := string(filenameBytes)

	var originalSize uint32
	err = binary.Read(reader, binary.LittleEndian, &originalSize)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error: Invalid header (original size): %v", err), Err: err}
	}

	if originalSize == 0 {
		log.Printf("Decompress Info: Original file was empty (HUFF format)")
		outputPath := determineOutputPath(inputPath, outputDir, originalFilename)
		outFile, err := os.Create(outputPath)
		if err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error creating empty output: %v", err), Err: err}
		}
		outFile.Close()
		if p != nil {
			p.Send(SendProgress(0, 0))
		}
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Decompression complete (empty file): %s", outputPath), Err: nil}
	}

	var numCodes uint32
	err = binary.Read(reader, binary.LittleEndian, &numCodes)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error: Invalid header (code count): %v", err), Err: err}
	}

	if numCodes > 65536 {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error: Too many Huffman codes (%d)", numCodes), Err: fmt.Errorf("too many codes")}
	}
	if numCodes == 0 && originalSize > 0 {
		return FileOperationFinishedMsg{Result: "Error: Invalid header (zero codes for non-empty file)", Err: fmt.Errorf("invalid header: zero codes")}
	}

	if p != nil {
		p.Send(SendProgress(0, int64(originalSize)))
	}

	var canonicalCodes []CanonicalCode
	for count := uint32(0); count < numCodes; count++ {
		var symbol uint32
		var codeLength uint8
		if err := binary.Read(reader, binary.LittleEndian, &symbol); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading Huffman table (symbol): %v", err), Err: err}
		}
		if err := binary.Read(reader, binary.LittleEndian, &codeLength); err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading Huffman table (length): %v", err), Err: err}
		}
		if codeLength == 0 || codeLength > 64 {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error: Invalid code length %d", codeLength), Err: fmt.Errorf("invalid code length")}
		}
		canonicalCodes = append(canonicalCodes, CanonicalCode{Symbol: int(symbol), Length: int(codeLength)})
	}

	huffmanRoot, err := rebuildHuffmanTree(canonicalCodes)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error rebuilding Huffman tree: %v", err), Err: err}
	}
	if huffmanRoot == nil && originalSize > 0 {
		return FileOperationFinishedMsg{Result: "Error: Failed to build Huffman tree for non-empty file", Err: fmt.Errorf("huffman tree build failed")}
	}

	payloadBytesOriginal := make([]byte, reader.Len())
	nReadOriginal, err := io.ReadFull(reader, payloadBytesOriginal)
	if err != nil && err != io.ErrUnexpectedEOF && err != io.EOF {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading original payload: %v", err), Err: err}
	}
	payloadBytesOriginal = payloadBytesOriginal[:nReadOriginal]

	var tokens []int
	bitReader := NewBitReader(payloadBytesOriginal)
	bitReader.AllowEOF(true)
	currentNode := huffmanRoot
	eofReached := false
	estimatedSize := 0

	for uint32(estimatedSize) < originalSize && !eofReached {
		if currentNode == nil {
			return FileOperationFinishedMsg{Result: "Error: Invalid state during Huffman decoding (orig)", Err: fmt.Errorf("huffman traversal error")}
		}
		if currentNode.left == nil && currentNode.right == nil {
			if currentNode.char == -1 {
				return FileOperationFinishedMsg{Result: "Error: Invalid Huffman code sequence (orig)", Err: fmt.Errorf("invalid huffman sequence")}
			}
			token := currentNode.char
			tokens = append(tokens, token)

			if token < 256 {
				estimatedSize++
			} else {
				tokenVal := token - 256
				length := (tokenVal >> 12) & 0x3FF
				estimatedSize += length
			}

			currentNode = huffmanRoot
			if uint32(estimatedSize) >= originalSize {
				break
			}
			if bitReader.IsEOF() {
				eofReached = true
			}
			continue
		}
		bit, err := bitReader.ReadBit()
		if err == io.EOF {
			if currentNode != huffmanRoot {
				if currentNode.left == nil && currentNode.right == nil && currentNode.char != -1 {
					token := currentNode.char
					tokens = append(tokens, token)

					if token < 256 {
						estimatedSize++
					} else {
						tokenVal := token - 256
						length := (tokenVal >> 12) & 0x3FF
						estimatedSize += length
					}

				} else {
					log.Printf("Original Format Decompress Warning: EOF reached with incomplete Huffman code sequence.")
				}
			}
			eofReached = true
			break
		} else if err != nil {
			return FileOperationFinishedMsg{Result: fmt.Sprintf("Error reading compressed data (orig): %v", err), Err: err}
		}
		if bit == 1 {
			currentNode = currentNode.right
		} else {
			currentNode = currentNode.left
		}
		if currentNode == nil {
			return FileOperationFinishedMsg{Result: "Error: Invalid Huffman bit sequence (orig)", Err: fmt.Errorf("invalid huffman bits")}
		}
	}

	outputBuffer := make([]byte, 0, originalSize)
	decompressedBytes := 0

	for i, token := range tokens {
		if uint32(decompressedBytes) >= originalSize {
			break
		}
		if token < 256 {
			outputBuffer = append(outputBuffer, byte(token))
			decompressedBytes++
		} else {
			tokenVal := token - 256
			length := (tokenVal >> 12) & 0x3FF
			distance := tokenVal & 0xFFF
			if distance <= 0 || length <= 0 {
				log.Printf("Original Format Decompress Warning: Skipping invalid LZ77 token (%d, %d) at index %d", length, distance, i)
				continue
			}
			startPos := len(outputBuffer) - distance
			if startPos < 0 {
				return FileOperationFinishedMsg{Result: fmt.Sprintf("Error: Invalid LZ77 distance %d (orig)", distance), Err: fmt.Errorf("invalid LZ77 distance")}
			}
			bytesToCopy := length
			if decompressedBytes+bytesToCopy > int(originalSize) {
				bytesToCopy = int(originalSize) - decompressedBytes
			}
			if bytesToCopy <= 0 {
				continue
			}

			copySourceStart := startPos
			bytesAppended := 0
			for bytesAppended < bytesToCopy {
				chunkCopySize := min(bytesToCopy-bytesAppended, len(outputBuffer)-copySourceStart)
				if chunkCopySize <= 0 {
					if distance == 1 && bytesAppended < bytesToCopy {
						outputBuffer = append(outputBuffer, outputBuffer[startPos])
						bytesAppended++
						continue
					}
					return FileOperationFinishedMsg{Result: "Error: Invalid LZ77 copy state (orig)", Err: fmt.Errorf("invalid LZ77 copy")}
				}
				outputBuffer = append(outputBuffer, outputBuffer[copySourceStart:copySourceStart+chunkCopySize]...)
				bytesAppended += chunkCopySize
				copySourceStart += chunkCopySize
			}
			decompressedBytes += bytesAppended
		}
	}

	outputPath := determineOutputPath(inputPath, outputDir, originalFilename)
	finalBytesToWrite := outputBuffer
	if len(finalBytesToWrite) > int(originalSize) {
		log.Printf("Original Format Decompress Warning: Truncating output from %d to %d bytes", len(finalBytesToWrite), originalSize)
		finalBytesToWrite = finalBytesToWrite[:originalSize]
	}
	err = os.WriteFile(outputPath, finalBytesToWrite, 0644)
	if err != nil {
		return FileOperationFinishedMsg{Result: fmt.Sprintf("Error writing decompressed file (orig): %v", err), Err: err}
	}

	if p != nil {
		p.Send(SendProgress(int64(len(finalBytesToWrite)), int64(originalSize)))
	}

	finalWrittenSize := len(finalBytesToWrite)
	if uint32(finalWrittenSize) == originalSize {
		resultMsg := fmt.Sprintf("Decompression complete: %s", outputPath)
		log.Printf("--- Decompress Success (Original HUFF): %s --- Wrote %d bytes", inputPath, finalWrittenSize)
		return FileOperationFinishedMsg{Result: resultMsg, Err: nil}
	} else {
		warningMsg := fmt.Sprintf("Decompression complete with warning: %s (expected %d bytes, got %d bytes)", outputPath, originalSize, finalWrittenSize)
		log.Printf("--- Decompress Warning (Original HUFF): %s --- Expected %d bytes, wrote %d bytes", inputPath, originalSize, finalWrittenSize)
		return FileOperationFinishedMsg{Result: warningMsg, Err: nil}
	}
}

func compressFileAndSendMessages(inputPath string, outputDir string, p *tea.Program) {
	if p == nil {
		log.Println("Error: compressFileAndSendMessages called with nil tea.Program instance")
		return
	}
	finalMsg := compressFileLogic(inputPath, outputDir, p)
	p.Send(finalMsg)
}

func decompressFileAndSendMessages(inputPath string, outputDir string, p *tea.Program) {
	if p == nil {
		log.Println("Error: decompressFileAndSendMessages called with nil tea.Program instance")
		return
	}
	finalMsg := decompressFileLogic(inputPath, outputDir, p)
	p.Send(finalMsg)
}

func generateCanonicalCodes(initialCodes map[int]string) []CanonicalCode {
	var codeInfo []CanonicalCode
	for symbol, code := range initialCodes {
		codeInfo = append(codeInfo, CanonicalCode{
			Symbol: symbol,
			Length: len(code),
		})
	}

	sort.Slice(codeInfo, func(i, j int) bool {
		if codeInfo[i].Length == codeInfo[j].Length {
			return codeInfo[i].Symbol < codeInfo[j].Symbol
		}
		return codeInfo[i].Length < codeInfo[j].Length
	})

	return codeInfo
}

func canonicalToStringCodes(canonicalCodes []CanonicalCode) map[int]string {
	if len(canonicalCodes) == 0 {
		return map[int]string{}
	}

	sort.Slice(canonicalCodes, func(i, j int) bool {
		if canonicalCodes[i].Length == canonicalCodes[j].Length {
			return canonicalCodes[i].Symbol < canonicalCodes[j].Symbol
		}
		return canonicalCodes[i].Length < canonicalCodes[j].Length
	})

	code := 0
	prevLen := 0
	if len(canonicalCodes) > 0 {
		prevLen = canonicalCodes[0].Length
	}

	result := make(map[int]string)

	for _, c := range canonicalCodes {
		if c.Length > prevLen {
			code <<= (c.Length - prevLen)
			prevLen = c.Length
		}

		binStr := strings.Builder{}
		binStr.Grow(c.Length)
		for i := c.Length - 1; i >= 0; i-- {
			if (code & (1 << i)) != 0 {
				binStr.WriteByte('1')
			} else {
				binStr.WriteByte('0')
			}
		}

		result[c.Symbol] = binStr.String()
		code++
	}

	return result
}

func rebuildHuffmanTree(canonicalCodes []CanonicalCode) (*huffmanNode, error) {
	if len(canonicalCodes) == 0 {
		return nil, nil
	}

	sort.Slice(canonicalCodes, func(i, j int) bool {
		if canonicalCodes[i].Length == canonicalCodes[j].Length {
			return canonicalCodes[i].Symbol < canonicalCodes[j].Symbol
		}
		return canonicalCodes[i].Length < canonicalCodes[j].Length
	})

	root := &huffmanNode{char: -1}
	code := 0
	prevLen := 0
	if len(canonicalCodes) > 0 {
		prevLen = canonicalCodes[0].Length
	}

	for _, c := range canonicalCodes {
		if c.Length > prevLen {
			code <<= (c.Length - prevLen)
			prevLen = c.Length
		}

		if c.Length <= 0 || c.Length > 64 {
			return nil, fmt.Errorf("invalid code length %d for symbol %d during tree rebuild", c.Length, c.Symbol)
		}

		currentNode := root
		for i := c.Length - 1; i >= 0; i-- {
			isRight := (code & (1 << i)) != 0

			if isRight {
				if currentNode.right == nil {
					if i > 0 {
						currentNode.right = &huffmanNode{char: -1}
					} else {
						currentNode.right = &huffmanNode{char: c.Symbol}
					}
				} else if i == 0 && currentNode.right.char != -1 {
					return nil, fmt.Errorf("huffman tree build conflict: trying to assign symbol %d where symbol %d already exists", c.Symbol, currentNode.right.char)
				} else if i == 0 && currentNode.right.char == -1 {
					currentNode.right.char = c.Symbol
				}
				currentNode = currentNode.right
			} else {
				if currentNode.left == nil {
					if i > 0 {
						currentNode.left = &huffmanNode{char: -1}
					} else {
						currentNode.left = &huffmanNode{char: c.Symbol}
					}
				} else if i == 0 && currentNode.left.char != -1 {
					return nil, fmt.Errorf("huffman tree build conflict: trying to assign symbol %d where symbol %d already exists", c.Symbol, currentNode.left.char)
				} else if i == 0 && currentNode.left.char == -1 {
					currentNode.left.char = c.Symbol
				}
				currentNode = currentNode.left
			}

			if i > 0 && currentNode != nil && currentNode.left == nil && currentNode.right == nil && currentNode.char != -1 {
				return nil, fmt.Errorf("huffman tree build conflict: path requires traversing through a leaf node (symbol %d)", currentNode.char)
			}
		}

		code++
	}

	return root, nil
}

func determineOutputPath(inputPath, outputDir, originalFilename string) string {
	var targetDir string
	if outputDir != "" {
		targetDir = outputDir
	} else {
		targetDir = filepath.Dir(inputPath)
	}

	baseName := originalFilename

	outputPath := filepath.Join(targetDir, baseName)

	if _, err := os.Stat(outputPath); err == nil {
		ext := filepath.Ext(baseName)
		baseNameNoExt := strings.TrimSuffix(baseName, ext)
		counter := 1
		for {
			newName := fmt.Sprintf("%s_decompressed", baseNameNoExt)
			if counter > 1 {
				newName = fmt.Sprintf("%s_decompressed(%d)", baseNameNoExt, counter)
			}
			newPath := filepath.Join(targetDir, newName+ext)
			if _, err := os.Stat(newPath); os.IsNotExist(err) {
				outputPath = newPath
				break
			}
			counter++
			if counter > 1000 {
				log.Printf("Warning: Could not find unique output name for %s after 1000 attempts. Overwriting.", originalFilename)
				outputPath = filepath.Join(targetDir, fmt.Sprintf("%s_decompressed_overwrite%s", baseNameNoExt, ext))
				break
			}
		}
	}
	return outputPath
}

func (m model) Init() tea.Cmd {
	return textinput.Blink
}

func (m model) Update(msg tea.Msg) (tea.Model, tea.Cmd) {
	var cmd tea.Cmd
	var cmds []tea.Cmd

	switch msg := msg.(type) {
	case tea.WindowSizeMsg:
		m.width = msg.Width

		progWidth := msg.Width - 6
		if progWidth < 10 {
			progWidth = 10
		}
		m.progress.Width = progWidth

		m.input.Width = msg.Width - 10
		m.dirInput.Width = msg.Width - 10
		return m, nil

	case tea.KeyMsg:
		switch m.mode {
		case "menu":
			switch msg.String() {
			case "ctrl+c", "q":
				return m, tea.Quit
			case "up", "k":
				if m.cursor > 0 {
					m.cursor--
				} else {
					m.cursor = len(m.choices) - 1
				}
			case "down", "j":
				if m.cursor < len(m.choices)-1 {
					m.cursor++
				} else {
					m.cursor = 0
				}
			case "enter":
				switch m.cursor {
				case 0:
					m.mode = "compress"
					m.input.Focus()
					m.dirInput.Blur()
					m.activeInput = 0
					m.input.Reset()
					m.dirInput.Reset()
					m.result = ""
					cmd = textinput.Blink
				case 1:
					m.mode = "decompress"
					m.input.Focus()
					m.dirInput.Blur()
					m.activeInput = 0
					m.input.Reset()
					m.dirInput.Reset()
					m.result = ""
					cmd = textinput.Blink
				case 2:
					m.mode = "about"

					m.result = ""
					cmd = nil
				case 3:
					return m, tea.Quit
				}
				return m, cmd
			}
		case "compress", "decompress":
			switch msg.String() {
			case "ctrl+c":
				return m, tea.Quit
			case "esc":
				m.mode = "menu"
				m.input.Reset()
				m.dirInput.Reset()
				m.result = ""
				m.percent = 0
				m.done = false
				return m, nil
			case "tab":
				if m.activeInput == 0 {
					m.input.Blur()
					m.dirInput.Focus()
					m.activeInput = 1
				} else {
					m.dirInput.Blur()
					m.input.Focus()
					m.activeInput = 0
				}
				cmd = textinput.Blink
				return m, cmd
			case "enter":
				filePath := m.input.Value()
				if filePath == "" {
					return m, nil
				}
				if _, err := os.Stat(filePath); os.IsNotExist(err) {
					m.result = fmt.Sprintf("Error: File not found: %s", filePath)
					return m, nil
				}

				m.processingOp = m.mode
				outputDir := m.dirInput.Value()
				m.mode = "processing"
				m.startTime = time.Now()
				m.percent = 0
				m.bytesProcessed = 0
				m.totalBytes = 0
				m.done = false
				m.result = ""

				if m.processingOp == "compress" {
					fileInfo, err := os.Stat(filePath)
					if err == nil {
						m.totalBytes = fileInfo.Size()
					}
					cmd = startCompression(filePath, outputDir)
				} else {
					compressedFile, err := os.Open(filePath)
					if err == nil {
						magicBytes := make([]byte, 4)
						if _, err := io.ReadFull(compressedFile, magicBytes); err == nil {
							magic := string(magicBytes)
							if magic == magicChunked {
								var filenameLen uint16
								if binary.Read(compressedFile, binary.LittleEndian, &filenameLen) == nil {
									filenameBytes := make([]byte, filenameLen)
									if _, err := io.ReadFull(compressedFile, filenameBytes); err == nil {
										var originalTotalSize uint64
										if binary.Read(compressedFile, binary.LittleEndian, &originalTotalSize) == nil {
											m.totalBytes = int64(originalTotalSize)
										}
									}
								}
							} else if magic == magicOriginal {
								var filenameLen uint16
								if binary.Read(compressedFile, binary.LittleEndian, &filenameLen) == nil {
									filenameBytes := make([]byte, filenameLen)
									if _, err := io.ReadFull(compressedFile, filenameBytes); err == nil {
										var originalSize uint32
										if binary.Read(compressedFile, binary.LittleEndian, &originalSize) == nil {
											m.totalBytes = int64(originalSize)
										}
									}
								}
							}
						}
						compressedFile.Close()
					}
					cmd = startDecompression(filePath, outputDir)
				}

				cmds = append(cmds, func() tea.Msg { return SendProgress(0, m.totalBytes) })
				cmds = append(cmds, cmd)

				cmds = append(cmds, tickCmd())
				return m, tea.Batch(cmds...)
			}

			var inputCmd tea.Cmd
			if m.activeInput == 0 {
				m.input, inputCmd = m.input.Update(msg)
			} else {
				m.dirInput, inputCmd = m.dirInput.Update(msg)
			}
			cmds = append(cmds, inputCmd)

			return m, tea.Batch(cmds...)

		case "about":
			switch msg.String() {
			case "esc", "enter":
				m.mode = "menu"
				return m, nil
			}
		case "processing":
			if msg.String() == "ctrl+c" {
				return m, tea.Quit
			}
			if m.done && msg.String() == "enter" {
				m.mode = "menu"
				m.input.Reset()
				m.dirInput.Reset()
				m.percent = 0
				m.result = ""
				m.done = false
				m.bytesProcessed = 0
				m.totalBytes = 0
				return m, nil
			}
		}

	case FileOperationFinishedMsg:
		m.result = msg.Result
		if msg.Err != nil {
			log.Printf("Operation failed: %v", msg.Err)
		}
		m.done = true

		if m.totalBytes == 0 && msg.Err == nil {
			m.percent = 1.0
		} else if m.totalBytes > 0 {

			m.bytesProcessed = m.totalBytes
			m.percent = 1.0
		} else {
			m.percent = 1.0
		}
		cmd = m.progress.SetPercent(m.percent)
		return m, cmd

	case ProgressMsg:

		if msg.Total > 0 && m.totalBytes != msg.Total {
			m.totalBytes = msg.Total
		}
		m.bytesProcessed = msg.Processed

		if m.totalBytes > 0 {
			m.percent = float64(m.bytesProcessed) / float64(m.totalBytes)
		} else {

			if m.bytesProcessed == 0 && m.done {
				m.percent = 1.0
			} else {
				m.percent = 0
			}
		}

		if m.percent < 0 {
			m.percent = 0
		}
		if m.percent > 1 {
			m.percent = 1
		}

		cmd = m.progress.SetPercent(m.percent)
		return m, cmd

	case tickMsg:
		if m.mode == "processing" && !m.done {

			cmd = tickCmd()
			return m, cmd
		}

		return m, nil

	}

	return m, tea.Batch(cmds...)
}

func formatDuration(d time.Duration) string {
	d = d.Round(time.Second)
	m := d / time.Minute
	d -= m * time.Minute
	s := d / time.Second
	if m > 0 {
		return fmt.Sprintf("%dm%ds", m, s)
	}
	return fmt.Sprintf("%ds", s)
}

func (m model) View() string {
	var s strings.Builder

	contentWidth := m.width - 4
	if contentWidth < 40 {
		contentWidth = 40
	}

	switch m.mode {
	case "menu":
		menuContent := []string{
			titleStyle.Width(contentWidth).Render("📦 File Compression Tool\nBy Adam"),
			"",
			helpTextStyle.Width(contentWidth).Render("Select an option:"),
			"",
		}

		for i, choice := range m.choices {
			cursor := " "
			style := itemStyle.Width(contentWidth)
			if m.cursor == i {
				cursor = ">"
				style = selectedItemStyle.Width(contentWidth)
			}
			menuContent = append(menuContent, style.Render(fmt.Sprintf("%s %s", cursor, choice)))
		}
		menuContent = append(menuContent, "")
		menuContent = append(menuContent, helpTextStyle.Width(contentWidth).Render("(Use ↑/↓ arrows, Enter to select, Q or Ctrl+C to quit)"))

		s.WriteString(lipgloss.Place(m.width, 0,
			lipgloss.Center, lipgloss.Top,
			lipgloss.JoinVertical(lipgloss.Center, menuContent...),
		))

	case "compress", "decompress":
		titleText := "Compress a File"
		if m.mode == "decompress" {
			titleText = "Decompress a File"
		}

		fileLabelStyled := inputLabelStyle.Width(contentWidth)
		dirLabelStyled := inputLabelStyle.Width(contentWidth)
		if m.activeInput == 0 {
			fileLabelStyled = activeInputLabelStyle.Width(contentWidth)
		} else {
			dirLabelStyled = activeInputLabelStyle.Width(contentWidth)
		}

		fileInputView := inputBoxStyle.Render(m.input.View())
		dirInputView := inputBoxStyle.Render(m.dirInput.View())

		inputContent := []string{
			titleStyle.Width(contentWidth).Render(titleText),
			"",
			fileLabelStyled.Render(fmt.Sprintf("File to %s:", m.mode)),
			fileInputView,
			"",
			dirLabelStyled.Render("Output directory (optional):"),
			dirInputView,
			"",
		}

		if m.result != "" {
			resultStyled := resultStyle.Width(contentWidth).Render(m.result)
			inputContent = append(inputContent, resultStyled, "")
		}

		inputContent = append(inputContent, helpTextStyle.Width(contentWidth).Render("Tab: switch fields | Enter: start | Esc: back"))

		s.WriteString(lipgloss.Place(m.width, 0,
			lipgloss.Center, lipgloss.Top,
			lipgloss.JoinVertical(lipgloss.Center, inputContent...),
		))

	case "processing":
		titleText := "Compressing..."
		if m.processingOp == "decompress" {
			titleText = "Decompressing..."
		}

		prog := m.progress.ViewAs(m.percent)

		etaText := ""

		if !m.done && m.totalBytes > 0 && m.percent > 0 && m.percent < 1.0 {
			elapsed := time.Since(m.startTime)
			if elapsed > time.Second {
				if m.percent > 1e-9 {
					estimatedTotalDuration := time.Duration(float64(elapsed) / m.percent)
					remainingDuration := estimatedTotalDuration - elapsed
					if remainingDuration < 0 {
						remainingDuration = 0
					}

					if remainingDuration < time.Second {
						etaText = " (< 1s remaining)"
					} else {
						etaText = fmt.Sprintf(" (ETA: %s)", formatDuration(remainingDuration))
					}
				}
			}
		} else if !m.done && m.totalBytes == 0 && m.startTime != (time.Time{}) {
			etaText = " (Processing...)"
		} else if !m.done {
			etaText = " (Initializing...)"
		}
		etaStyled := helpTextStyle.Width(contentWidth).Render(etaText)

		processingContent := []string{
			titleStyle.Width(contentWidth).Render(titleText),
			"",
			prog,
			etaStyled,
			"",
		}

		if m.done {
			finalMsgStyle := resultStyle.Width(contentWidth)
			if strings.Contains(m.result, "Error") || strings.Contains(m.result, "failed") || strings.Contains(m.result, "Invalid") || strings.Contains(m.result, "warning") {
				finalMsgStyle = lipgloss.NewStyle().Foreground(lipgloss.Color("#FF0000")).Width(contentWidth).Align(lipgloss.Center)
			}
			processingContent = append(processingContent,
				finalMsgStyle.Render(m.result),
				"",
				helpTextStyle.Width(contentWidth).Render("Press Enter to return to menu"),
			)
		} else {
			processingContent = append(processingContent, helpTextStyle.Width(contentWidth).Render("(Ctrl+C to Quit)"))
		}

		s.WriteString(lipgloss.Place(m.width, 0,
			lipgloss.Center, lipgloss.Top,
			lipgloss.JoinVertical(lipgloss.Center, processingContent...),
		))

	case "about":
		aboutText := `HuffleManager (huffleman) - Huffman-based file compression
A minimal tool for compressing and decompressing files using Huffman coding.
The name combines "Huffman" and "file manager" – reflecting its role in managing
compressed data with efficient binary encoding.

Source: https://github.com/abker0
Author: Adam Baker (2025)
`

		aboutBoxWidth := contentWidth - 4
		if aboutBoxWidth < 10 {
			aboutBoxWidth = 10
		}

		aboutContent := []string{
			titleStyle.Width(contentWidth).Render("ℹ️\nAbout HuffleManager Binary file compressor"),
			"",
			aboutBoxStyle.Width(aboutBoxWidth).Render(aboutText),
			"",
			helpTextStyle.Width(contentWidth).Render("(Press Esc or Enter to go back)"),
		}

		s.WriteString(lipgloss.Place(m.width, 0,
			lipgloss.Center, lipgloss.Top,
			lipgloss.JoinVertical(lipgloss.Center, aboutContent...),
		))
	}

	return s.String()
}

func main() {
	logFile, err := os.OpenFile("compression_tool.log", os.O_CREATE|os.O_WRONLY|os.O_TRUNC, 0644)
	if err != nil {
		log.SetOutput(os.Stderr)
		log.Println("CRITICAL: Could not open log file 'compression_tool.log':", err, ". Logging to stderr.")
	} else {
		log.SetOutput(logFile)

		defer func() {
			log.Println("----- Closing log file ----- (", time.Now().Format(time.RFC3339), ")")
			err := logFile.Close()
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error closing log file: %v\n", err)
			}
		}()
		log.Println("----- Log file opened successfully ----- (", time.Now().Format(time.RFC3339), ")")
	}

	log.SetFlags(log.LstdFlags | log.Lshortfile)
	log.Println("----- Program Started ----- (", time.Now().Format(time.RFC3339), ")")

	p := tea.NewProgram(initialModel(), tea.WithAltScreen())

	programInstance = p

	if _, err := p.Run(); err != nil {
		log.Println("Error running program:", err)
		fmt.Printf("Error running program: %v\nCheck compression_tool.log for details.\n", err)
		os.Exit(1)
	}
	log.Println("----- Program Exited Normally -----")
}

var programInstance *tea.Program

func startCompression(inputPath, outputDir string) tea.Cmd {
	return func() tea.Msg {
		go compressFileAndSendMessages(inputPath, outputDir, programInstance)
		return nil
	}
}

func startDecompression(inputPath, outputDir string) tea.Cmd {
	return func() tea.Msg {
		go decompressFileAndSendMessages(inputPath, outputDir, programInstance)
		return nil
	}
}
