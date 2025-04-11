
# 🧙 HuffleManager

**HuffleManager** (also known as `huffleman`) is a terminal-based file compression and decompression tool using a custom hybrid of **Huffman coding** and **LZ77**. Built with Go and a rich TUI powered by Charmbracelet libraries, it's designed for handling general-purpose file compression in an interactive and user-friendly way.

## ✨ Features

- 📦 Compresses and decompresses files with `.huff` format
- 🧩 Chunk-based processing for large files
- 💻 Terminal UI with text inputs, progress bars, and status updates
- 🌈 Fully styled UI using [Lipgloss](https://github.com/charmbracelet/lipgloss)
- ⚡ Parallel compression using multiple CPU cores

## 🔧 Installation

```bash
git clone https://github.com/abker0/hufflemanager.git
cd hufflemanager
go build -o huffleman main.go
```

Make sure to run `go mod tidy` to install required dependencies.

## 🚀 Usage

Run the tool:

```bash
./huffleman
```

You’ll be presented with a terminal interface where you can:

- Select a file to compress or decompress
- Optionally set an output directory
- Track progress visually in real-time

Use:

- ↑ / ↓ or j / k to move
- Enter to select
- Tab to switch fields
- Esc to go back

## ⚠️ Limitations & Notes

- HuffleManager works best with text-heavy or repetitive files like logs, source code, or JSON data.
- It does not achieve strong compression on already compressed formats (like .jpg, .png, .zip, .mp4) and may even increase file size slightly due to metadata and Huffman tables.
- It's intended more as a learning tool and general-purpose compressor than a replacement for specialized tools like gzip or xz.

## 📦 Output

Compressed files are saved with a `.huff` extension. They include:

- Original filename and size metadata
- A per-chunk Huffman table for decompression
- Safe parallel processing compatibility

## 📚 Built With

- Go
- Bubbletea
- Bubbles
- Lipgloss

## 👨‍💻 Author

Created by Adam Baker in 2025  
GitHub: @abker0

"HUFF and PUFF, and save your bytes." — huffleman
