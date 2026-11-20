package source

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"image"
	"image/png"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"time"
)

const (
	editionPages = 940
	maxPDF       = 16 << 20
	maxPNG       = 2 << 20
)

// The rendered pages of interest have
// matching printed numbers and PDF
// ordinals (519, 520 and 522 in their
// running headers and 523 in its
// footer). Readers still have to report
// the printed numbers they see on every
// requested page.
var manuscript = edition{
	url:    "https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf",
	sha256: "e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5",
}

type edition struct {
	url, sha256 string
}

func (e edition) load(ctx context.Context, override string) ([]byte, error) {
	if override != "" {
		pdf, err := readFile(override, maxPDF)
		if err != nil {
			return nil, fmt.Errorf("source: read GRH_PDF: %w", err)
		}
		if !e.matches(pdf) {
			return nil, fmt.Errorf("source: GRH_PDF does not match pinned SHA-256 %s", e.sha256)
		}
		return pdf, nil
	}
	cache, err := os.UserCacheDir()
	if err != nil {
		return nil, fmt.Errorf("source: locate PDF cache: %w", err)
	}
	return e.cached(ctx, filepath.Join(cache, "grh", "source"))
}

func (e edition) cached(ctx context.Context, dir string) ([]byte, error) {
	path := filepath.Join(dir, e.sha256+".pdf")
	pdf, err := readFile(path, maxPDF)
	if err == nil && e.matches(pdf) {
		return pdf, nil
	}
	pdf, err = e.download(ctx)
	if err != nil {
		return nil, err
	}
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return nil, fmt.Errorf("source: create PDF cache: %w", err)
	}
	f, err := os.CreateTemp(dir, "download-*.pdf")
	if err != nil {
		return nil, fmt.Errorf("source: stage verified PDF cache entry: %w", err)
	}
	defer os.Remove(f.Name())
	_, err = f.Write(pdf)
	closeErr := f.Close()
	if err != nil {
		return nil, fmt.Errorf("source: write verified PDF: %w", err)
	}
	if closeErr != nil {
		return nil, fmt.Errorf("source: close verified PDF: %w", closeErr)
	}
	if err := os.Rename(f.Name(), path); err != nil {
		return nil, fmt.Errorf("source: publish verified PDF cache entry: %w", err)
	}
	return pdf, nil
}

func (e edition) download(ctx context.Context) ([]byte, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, e.url, nil)
	if err != nil {
		return nil, fmt.Errorf("source: create PDF request: %w", err)
	}
	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("source: download PDF: %w", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("source: download PDF: HTTP %d", resp.StatusCode)
	}
	pdf, err := readLimited(resp.Body, maxPDF)
	if err != nil {
		return nil, fmt.Errorf("source: read PDF response: %w", err)
	}
	if !e.matches(pdf) {
		return nil, fmt.Errorf("source: downloaded PDF does not match pinned SHA-256 %s", e.sha256)
	}
	return pdf, nil
}

func (e edition) matches(pdf []byte) bool {
	digest := sha256.Sum256(pdf)
	return bytes.HasPrefix(pdf, []byte("%PDF-")) && hex.EncodeToString(digest[:]) == e.sha256
}

func render(ctx context.Context, dir string, pdf []byte, target Passage) ([]*image.RGBA, error) {
	// Render a private copy of the actual verified
	// bytes, not a mutable override or cache path
	// whose contents could have changed since
	// verification.
	filename := filepath.Join(dir, "edition.pdf")
	if err := os.WriteFile(filename, pdf, 0o600); err != nil {
		return nil, fmt.Errorf("source: stage verified PDF for rendering: %w", err)
	}
	var pages []*image.RGBA
	for printed := target.First; printed <= target.Last; printed++ {
		ordinal := fmt.Sprint(printed)
		prefix := fmt.Sprintf("image-%d", printed-target.First+1)
		pageCtx, cancel := context.WithTimeout(ctx, 20*time.Second)
		cmd := exec.CommandContext(pageCtx, "pdftoppm", "-png", "-r", "175", "-singlefile", "-f", ordinal, "-l", ordinal, filename, prefix)
		cmd.Dir = dir
		cmd.WaitDelay = time.Second
		_, err := run(pageCtx, cmd, 64<<10)
		cancel()
		if err != nil {
			return nil, fmt.Errorf("source: render printed page %d (PDF ordinal %s): %w", printed, ordinal, err)
		}
		path := filepath.Join(dir, prefix+".png")
		data, err := readFile(path, maxPNG)
		if err != nil {
			return nil, fmt.Errorf("source: read rendered page %d: %w", printed, err)
		}
		config, err := png.DecodeConfig(bytes.NewReader(data))
		// 612 × 792 pt (letter), rendered at 175 dpi and rounded up.
		if err != nil || image.Pt(config.Width, config.Height) != image.Pt(1488, 1925) {
			return nil, fmt.Errorf("source: page %d is not a full-size rendered PNG", printed)
		}
		img, err := png.Decode(bytes.NewReader(data))
		if err != nil {
			return nil, fmt.Errorf("source: malformed rendered PNG for page %d: %w", printed, err)
		}
		// Poppler emits opaque RGB8 here.
		// Enforce that format so copying into
		// the challenged RGB8 PNG cannot reduce
		// color precision.
		page, ok := img.(*image.RGBA)
		if !ok || !page.Opaque() {
			return nil, fmt.Errorf("source: rendered page %d is not opaque RGB8", printed)
		}
		pages = append(pages, page)
	}
	return pages, nil
}

func readFile(path string, limit int64) ([]byte, error) {
	st, err := os.Stat(path)
	if err != nil {
		return nil, err
	}
	if !st.Mode().IsRegular() || st.Size() > limit {
		return nil, fmt.Errorf("expected regular file of at most %d bytes", limit)
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	return readLimited(f, limit)
}

func readLimited(r io.Reader, limit int64) ([]byte, error) {
	data, err := io.ReadAll(io.LimitReader(r, limit+1))
	if err != nil {
		return nil, err
	}
	if int64(len(data)) > limit {
		return nil, fmt.Errorf("input exceeds %d bytes", limit)
	}
	return data, nil
}
