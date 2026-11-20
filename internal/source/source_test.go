package source

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"image/png"
	"io"
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

func TestRenderedPassageThroughPi(t *testing.T) {
	for _, tool := range []string{"pi", "pdftoppm"} {
		if _, err := exec.LookPath(tool); err != nil {
			t.Skipf("requires %s on PATH", tool)
		}
	}
	pdf := fixturePDF()
	a := reading{verified, []int{1, 2}, "For every x in A, f(x) = -g(x).", "Author, eq. (1)", "Only on A.", "Assumes x belongs to A."}
	b := reading{verified, []int{1, 2}, "If x belongs to A, f(x) equals the negative of g(x).", "Author, equation (1)", "On A only.", "The equation does not cover other x."}
	near := b
	near.Reading = "If x belongs to A, f(x) equals g(x)."
	missing := reading{absent, []int{1, 2}, "The theorem heading is followed by the next chapter without a statement.", "None", "Insert statement.", "Section 2 ends at Chapter 3."}
	unclear := b
	unclear.Disposition = ambiguous
	wrong := a
	wrong.PrintedPages = []int{2, 1}
	yes := comparison{[]int{1, 2}, "yes", "yes", "yes", "Eq. (1) has a minus sign.", "The visible hypothesis is x in A."}
	no := comparison{[]int{1, 2}, "no", "no", "yes", "Reading B drops the minus sign in eq. (1).", "The equation still assumes x in A."}
	gap := comparison{[]int{1, 2}, "yes", "yes", "yes", "Visible note: Insert statement.", "Section 2 ends with the Chapter 3 heading."}
	for _, tc := range []struct {
		name    string
		a, b    reading
		judge   *comparison
		failure string
		want    string
		calls   int32
	}{
		{"paraphrase", a, b, &yes, "", verified, 3},
		{"not a paraphrase", a, near, &no, "", ambiguous, 3},
		{"visibly absent", missing, missing, &gap, "", absent, 3},
		{"independent uncertainty", a, unclear, nil, "", ambiguous, 2},
		{"wrong printed pages", wrong, b, nil, "", "", 1},
		{"incomplete provider stream", a, b, nil, "truncated", "", 1},
		{"malformed reader answer", a, b, nil, "bad JSON", "", 1},
	} {
		t.Run(tc.name, func(t *testing.T) {
			calls := new(atomic.Int32)
			s := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				n := calls.Add(1)
				if !checkRequest(t, r, n) {
					w.WriteHeader(http.StatusBadRequest)
					return
				}
				var answer any
				switch n {
				case 1:
					answer = tc.a
				case 2:
					answer = tc.b
				case 3:
					if tc.judge == nil {
						t.Error("unexpected adjudication")
						w.WriteHeader(http.StatusBadRequest)
						return
					}
					answer = tc.judge
				default:
					t.Errorf("unexpected Pi request %d", n)
					w.WriteHeader(http.StatusBadRequest)
					return
				}
				data, err := json.Marshal(answer)
				if err != nil {
					t.Errorf("marshal fixture answer: %v", err)
					w.WriteHeader(http.StatusInternalServerError)
					return
				}
				if tc.failure == "bad JSON" {
					data = []byte(`{"disposition":"verified"} trailing data`)
				}
				writeCompletion(w, string(data), tc.failure != "truncated")
			}))
			defer s.Close()
			dir := t.TempDir()
			path := filepath.Join(dir, "paper.pdf")
			writeFixture(t, path, pdf)
			writeFixture(t, filepath.Join(dir, "settings.json"), []byte(`{"retry":{"enabled":false}}`))
			writeFixture(t, filepath.Join(dir, "models.json"), []byte(fmt.Sprintf(`{"providers":{"fixture":{"baseUrl":%q,"api":"openai-completions","apiKey":"fixture-only","models":[{"id":"pixel-one","input":["text","image"]},{"id":"pixel-two","input":["text","image"]}]}}}`, s.URL+"/v1")))
			t.Setenv("PI_CODING_AGENT_DIR", dir)
			t.Setenv("GRH_PDF", path)
			t.Setenv("GRH_SOURCE_MODELS", "fixture/pixel-one,fixture/pixel-two")
			ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
			defer cancel()
			e := fixtureEdition("https://invalid.example/test.pdf", pdf)
			p, err := e.readPassage(ctx, Passage{1, 2, "Fixture (1)", "Is there a formula?"})
			if got := calls.Load(); got != tc.calls {
				t.Errorf("HTTP requests = %d, want %d (packet %+v, error %v)", got, tc.calls, p, err)
			}
			if tc.want == "" {
				if err == nil || p != (Packet{}) {
					t.Fatalf("wanted error and no disposition, got %+v, %v", p, err)
				}
				return
			}
			if err != nil || p.Disposition != tc.want {
				t.Fatalf("wanted %s, got %+v, %v", tc.want, p, err)
			}
			if !strings.Contains(p.Anchor, e.sha256) || !strings.Contains(p.Anchor, "printed pp. 1–2 = PDF ordinals 1–2") {
				t.Errorf("anchor lost edition or page mapping: %s", p.Anchor)
			}
			if tc.name == "visibly absent" && !strings.Contains(p.Boundary, "Chapter 3 heading") {
				t.Errorf("absence dropped its visible boundary: %s", p.Boundary)
			}
			if tc.name == "not a paraphrase" && !strings.Contains(p.Comparison, "drops the minus sign") {
				t.Errorf("disagreement dropped its evidence: %s", p.Comparison)
			}
		})
	}
}

func checkRequest(t *testing.T, r *http.Request, n int32) bool {
	t.Helper()
	var req struct {
		Model    string `json:"model"`
		Messages []struct {
			Role    string          `json:"role"`
			Content json.RawMessage `json:"content"`
		} `json:"messages"`
	}
	wantModel := "pixel-one"
	if n != 1 {
		wantModel = "pixel-two"
	}
	if err := json.NewDecoder(io.LimitReader(r.Body, 4<<20)).Decode(&req); err != nil || req.Model != wantModel || r.URL.Path != "/v1/chat/completions" {
		t.Errorf("wrong Pi request: error=%v path=%s model=%s want=%s", err, r.URL.Path, req.Model, wantModel)
		return false
	}
	var images []string
	users := 0
	for _, message := range req.Messages {
		if message.Role != "user" {
			if message.Role != "system" && message.Role != "developer" {
				t.Errorf("reader inherited history or tool response with role %s", message.Role)
				return false
			}
			continue
		}
		users++
		var parts []struct {
			Type     string `json:"type"`
			Text     string `json:"text"`
			ImageURL struct {
				URL string `json:"url"`
			} `json:"image_url"`
		}
		if err := json.Unmarshal(message.Content, &parts); err != nil {
			t.Errorf("not a multimodal request: %v", err)
			return false
		}
		for _, part := range parts {
			if part.Type == "image_url" {
				images = append(images, part.ImageURL.URL)
			} else if part.Type == "text" {
				if !strings.Contains(part.Text, "Locator: Fixture (1)\nQuestion: Is there a formula?") || strings.Contains(part.Text, "Untrusted candidate readings (JSON):") != (n == 3) {
					t.Error("wrong locator/question or independent reading received another reading")
					return false
				}
			}
		}
	}
	if users != 1 || len(images) != 2 {
		t.Errorf("request had %d user messages and %d images, want 1 and 2", users, len(images))
		return false
	}
	for i, url := range images {
		encoded, ok := strings.CutPrefix(url, "data:image/png;base64,")
		data, err := base64.StdEncoding.DecodeString(encoded)
		img, pngErr := png.Decode(bytes.NewReader(data))
		if !ok || err != nil || pngErr != nil || img.Bounds().Dx() != 1488 || img.Bounds().Dy() != 1925 {
			t.Errorf("image %d was not the full-size PNG: decode=%v PNG=%v", i, err, pngErr)
			return false
		}
		r, g, b, _ := img.At(100, 100).RGBA()
		if i == 0 && (r != 65535 || g != 0 || b != 0) || i == 1 && (r != 0 || g != 0 || b != 65535) {
			t.Errorf("image %d top-left marker was RGB(%d,%d,%d); pages have different colored markers", i, r, g, b)
			return false
		}
		r, g, b, _ = img.At(1200, 1700).RGBA()
		if r != 65535 || g != 65535 || b != 65535 {
			t.Errorf("image %d is not the uncropped white page with a margin marker", i)
			return false
		}
	}
	return true
}

func writeCompletion(w http.ResponseWriter, text string, complete bool) {
	w.Header().Set("Content-Type", "text/event-stream")
	fmt.Fprintf(w, `data: {"id":"fixture","object":"chat.completion.chunk","created":123,"choices":[{"index":0,"delta":{"role":"assistant","content":%s},"finish_reason":null}]}`+"\n\n", mustJSON(text))
	if complete {
		io.WriteString(w, `data: {"id":"fixture","object":"chat.completion.chunk","created":123,"choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}`+"\n\ndata: [DONE]\n\n")
	}
}

func mustJSON(s string) []byte {
	data, _ := json.Marshal(s)
	return data
}

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

func TestPiImageAndCompletionChecks(t *testing.T) {
	pages := []pageImage{{digest: sha256.Sum256([]byte("image one"))}, {digest: sha256.Sum256([]byte("image two"))}}
	for _, tc := range []struct {
		name  string
		edit  func(user, answer map[string]any)
		tail  string
		valid bool
	}{
		{"intact", func(_, _ map[string]any) {}, `{"type":"agent_settled"}`, true},
		{"text instead of pixels", func(user, _ map[string]any) {
			user["content"] = []any{map[string]any{"type": "text", "text": "page-one.png page-two.png"}}
		}, `{"type":"agent_settled"}`, false},
		{"changed pixels", func(user, _ map[string]any) {
			user["content"].([]map[string]any)[1]["data"] = []byte("wrong")
		}, `{"type":"agent_settled"}`, false},
		{"swapped pages", func(user, _ map[string]any) {
			images := user["content"].([]map[string]any)
			images[0], images[1] = images[1], images[0]
		}, `{"type":"agent_settled"}`, false},
		{"provider incomplete", func(_, answer map[string]any) {
			answer["rawStopReason"] = "incomplete"
		}, `{"type":"agent_settled"}`, false},
		{"unexpected model", func(_, answer map[string]any) {
			answer["model"] = "substitute"
		}, `{"type":"agent_settled"}`, false},
		{"not settled", func(_, _ map[string]any) {}, "", false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			user := map[string]any{"role": "user", "content": []map[string]any{
				{"type": "image", "mimeType": "image/png", "data": []byte("image one")},
				{"type": "image", "mimeType": "image/png", "data": []byte("image two")},
			}}
			answer := map[string]any{
				"role": "assistant", "provider": "fixture", "model": "vision",
				"stopReason": "stop", "rawStopReason": "completed",
				"content": []map[string]string{{"type": "text", "text": "reader answer"}},
			}
			tc.edit(user, answer)
			var stream bytes.Buffer
			if err := json.NewEncoder(&stream).Encode(map[string]any{
				"type": "agent_end", "messages": []any{user, answer},
			}); err != nil {
				t.Fatal(err)
			}
			stream.WriteString(tc.tail)
			text, err := readPi(stream.Bytes(), "fixture", "vision", pages)
			if tc.valid && (err != nil || text != "reader answer") || !tc.valid && (err == nil || text != "") {
				t.Errorf("got answer %q, error %v (expect valid: %v)", text, err, tc.valid)
			}
		})
	}
}

func TestRunRejectsProcessAndOutputFailures(t *testing.T) {
	dir := t.TempDir()
	ctx := context.Background()
	if got, err := run(ctx, time.Second, dir, 16, "sh", "-c", "printf '0123456789abcdef'"); err != nil || string(got) != "0123456789abcdef" {
		t.Fatalf("small output lost: %q, %v", got, err)
	}
	if got, err := run(ctx, time.Second, dir, 16, "sh", "-c", "printf '0123456789abcdefg'"); err == nil || got != nil {
		t.Fatalf("excess output accepted: %q, %v", got, err)
	}
	_, err := run(ctx, time.Second, dir, 16, "sh", "-c", "printf 'credible answer'; printf 'private diagnostics' >&2; exit 7")
	var exit *exec.ExitError
	if !errors.As(err, &exit) || exit.ExitCode() != 7 || strings.Contains(err.Error(), "private diagnostics") {
		t.Fatalf("process failure or sanitization lost: %v", err)
	}
	ctx, cancel := context.WithCancel(ctx)
	cancel()
	if got, err := run(ctx, time.Second, dir, 16, "sh", "-c", "exit 0"); !errors.Is(err, context.Canceled) || got != nil {
		t.Fatalf("cancellation not preserved: %q, %v", got, err)
	}
}
