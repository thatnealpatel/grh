package source

import (
	"bytes"
	"context"
	"crypto/sha256"
	"errors"
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

func writeFixture(t *testing.T, path string, contents []byte) {
	t.Helper()
	if err := os.WriteFile(path, contents, 0o600); err != nil {
		t.Fatal(err)
	}
}

func fixtureEdition(url string, data []byte) edition {
	return edition{url, fmt.Sprintf("%x", sha256.Sum256(data))}
}

func fixturePDF() []byte {
	stream := func(rgb string) string {
		body := rgb + " rg 0 710 82 82 re f\n"
		return fmt.Sprintf("<< /Length %d >>\nstream\n%sendstream", len(body), body)
	}
	objects := []string{
		"<< /Type /Catalog /Pages 2 0 R >>",
		"<< /Type /Pages /MediaBox [0 0 612 792] /Kids [3 0 R 4 0 R] /Count 2 >>",
		"<< /Type /Page /Parent 2 0 R /Resources << >> /Contents 5 0 R >>",
		"<< /Type /Page /Parent 2 0 R /Resources << >> /Contents 6 0 R >>",
		stream("1 0 0"), stream("0 0 1"),
	}
	var pdf strings.Builder
	pdf.WriteString("%PDF-1.4\n")
	var xref []int
	for i, obj := range objects {
		xref = append(xref, pdf.Len())
		fmt.Fprintf(&pdf, "%d 0 obj\n%s\nendobj\n", i+1, obj)
	}
	start := pdf.Len()
	fmt.Fprintf(&pdf, "xref\n0 %d\n0000000000 65535 f \n", len(objects)+1)
	for _, offset := range xref {
		fmt.Fprintf(&pdf, "%010d 00000 n \n", offset)
	}
	fmt.Fprintf(&pdf, "trailer\n<< /Size %d /Root 1 0 R >>\nstartxref\n%d\n%%%%EOF\n", len(objects)+1, start)
	return []byte(pdf.String())
}

func TestDownloadCacheAndOverride(t *testing.T) {
	data := fixturePDF()
	var requests atomic.Int32
	s := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		n := requests.Add(1)
		if n == 1 {
			w.Write([]byte("%PDF- wrong edition"))
			return
		}
		w.Write(data)
	}))
	defer s.Close()
	e := fixtureEdition(s.URL, data)
	t.Setenv("XDG_CACHE_HOME", t.TempDir())
	ctx := context.Background()
	if _, err := e.load(ctx, ""); err == nil || !strings.Contains(err.Error(), "SHA-256") {
		t.Fatalf("wrong first download accepted: %v", err)
	}
	for range 2 {
		if got, err := e.load(ctx, ""); err != nil || !bytes.Equal(got, data) {
			t.Fatalf("verified PDF not loaded: %v", err)
		}
	}
	bad := filepath.Join(t.TempDir(), "bad.pdf")
	writeFixture(t, bad, []byte("%PDF- wrong override"))
	if _, err := e.load(ctx, bad); err == nil || !strings.Contains(err.Error(), "GRH_PDF") {
		t.Fatalf("invalid override silently fell back: %v", err)
	}
	if got := requests.Load(); got != 2 {
		t.Fatalf("expected one rejected download and one cache fill, got %d requests", got)
	}
	writeFixture(t, filepath.Join(os.Getenv("XDG_CACHE_HOME"), "grh", "source", e.sha256+".pdf"), []byte("%PDF- corrupt cache"))
	if got, err := e.load(ctx, ""); err != nil || !bytes.Equal(got, data) || requests.Load() != 3 {
		t.Fatalf("corrupt cache entry not repaired, requests=%d error=%v", requests.Load(), err)
	}
}

func TestCancelDownload(t *testing.T) {
	entered := make(chan struct{})
	s := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		close(entered)
		<-r.Context().Done()
	}))
	defer s.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	e := fixtureEdition(s.URL, fixturePDF())
	errCh := make(chan error, 1)
	dir := t.TempDir()
	go func() { _, err := e.cached(ctx, dir); errCh <- err }()
	select {
	case <-entered:
		cancel()
	case <-ctx.Done():
		t.Fatal("download did not reach fixture")
	}
	if err := <-errCh; !errors.Is(err, context.Canceled) {
		t.Fatalf("got %v, want context cancellation", err)
	}
	if _, err := os.Stat(filepath.Join(dir, e.sha256+".pdf")); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("canceled download left cache entry: %v", err)
	}
}

func TestRunRejectsProcessAndOutputFailures(t *testing.T) {
	dir := t.TempDir()
	execute := func(ctx context.Context, script string) ([]byte, error) {
		ctx, cancel := context.WithTimeout(ctx, time.Second)
		defer cancel()
		cmd := exec.CommandContext(ctx, "sh", "-c", script)
		cmd.Dir = dir
		return run(ctx, cmd, 16)
	}
	ctx := context.Background()
	if got, err := execute(ctx, "printf '0123456789abcdef'"); err != nil || string(got) != "0123456789abcdef" {
		t.Fatalf("small output lost: %q, %v", got, err)
	}
	if got, err := execute(ctx, "printf '0123456789abcdefg'"); err == nil || got != nil {
		t.Fatalf("excess output accepted: %q, %v", got, err)
	}
	_, err := execute(ctx, "printf 'credible answer'; printf 'private diagnostics' >&2; exit 7")
	var exit *exec.ExitError
	if !errors.As(err, &exit) || exit.ExitCode() != 7 || strings.Contains(err.Error(), "private diagnostics") {
		t.Fatalf("process failure or sanitization lost: %v", err)
	}
	ctx, cancel := context.WithCancel(ctx)
	cancel()
	if got, err := execute(ctx, "exit 0"); !errors.Is(err, context.Canceled) || got != nil {
		t.Fatalf("cancellation not preserved: %q, %v", got, err)
	}
}
