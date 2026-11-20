package mathlane

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestPiTextTransport(t *testing.T) {
	if _, err := exec.LookPath("pi"); err != nil {
		t.Skip("Pi executable not installed")
	}
	// Exercise Pi (not merely a fake executable) against a loopback streaming
	// provider; inspect what would actually be sent with the model request.
	input := []byte(`{"MathlibSources":[{"Source":"def complex := \"ℂ\"\n"}],"Request":{"Draft":{"Files":{"Proofs/Props/TraceAssembly.lean":"line one\nline two\n"}}}}`)
	const answer = `{"Accept":true,"Reason":"loopback fixture only"}`
	const instruction = "Review the exact file contents in the JSON data."
	for _, complete := range []bool{true, false} {
		t.Run(fmt.Sprintf("normal_finish=%t", complete), func(t *testing.T) {
			s := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				var req struct {
					Model    string
					Tools    []json.RawMessage
					Messages []struct {
						Role    string
						Content json.RawMessage
					}
				}
				if err := json.NewDecoder(io.LimitReader(r.Body, 1<<20)).Decode(&req); err != nil || len(req.Tools) != 0 || r.URL.Path != "/v1/chat/completions" || req.Model != "math-fixture" || len(req.Messages) != 2 {
					t.Errorf("Pi did not send the requested model, one fresh turn and no tools: path=%s model=%s tools=%d messages=%d err=%v", r.URL.Path, req.Model, len(req.Tools), len(req.Messages), err)
					w.WriteHeader(http.StatusBadRequest)
					return
				}
				var actual string
				u := req.Messages[1]
				if err := json.Unmarshal(u.Content, &actual); err != nil {
					var parts []struct{ Type, Text string }
					if err := json.Unmarshal(u.Content, &parts); err == nil && len(parts) == 1 && parts[0].Type == "text" {
						actual = parts[0].Text
					}
				}
				if u.Role != "user" || actual != string(input) || !strings.Contains(string(req.Messages[0].Content), instruction) {
					t.Errorf("Pi did not send the exact input and instructions: %q", actual)
					w.WriteHeader(http.StatusBadRequest)
					return
				}
				w.Header().Set("Content-Type", "text/event-stream")
				fmt.Fprintf(w, `data: {"id":"fixture","object":"chat.completion.chunk","created":123,"choices":[{"index":0,"delta":{"role":"assistant","content":%q},"finish_reason":null}]}`+"\n\n", answer)
				if complete {
					io.WriteString(w, `data: {"id":"fixture","object":"chat.completion.chunk","created":123,"choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}`+"\n\ndata: [DONE]\n\n")
				}
			}))
			defer s.Close()
			dir := t.TempDir()
			putFile(t, dir, "models.json", fmt.Sprintf(`{"providers":{"fixture":{"baseUrl":%q,"api":"openai-completions","apiKey":"fixture-only","models":[{"id":"math-fixture","input":["text"]}]}}}`, s.URL+"/v1"))
			putFile(t, dir, "settings.json", `{"retry":{"enabled":false}}`)
			t.Setenv("PI_CODING_AGENT_DIR", dir)
			t.Setenv("GRH_MATH_MODEL", "fixture/math-fixture")
			ctx, cancel := context.WithTimeout(t.Context(), 15*time.Second)
			defer cancel()
			out, err := askPi(ctx, instruction, input)
			if complete && (err != nil || string(out) != answer) || !complete && (err == nil || len(out) != 0) {
				t.Fatalf("Pi answer %q, %v (complete=%v)", out, err, complete)
			}
		})
	}
}

func TestMathlibPinAndSourceMismatch(t *testing.T) {
	root := t.TempDir()
	putFile(t, root, "lean-toolchain", leanToolchain+"\n")
	writeManifest := func(rev string) {
		putFile(t, root, "lake-manifest.json", fmt.Sprintf(`{"packages":[{"name":"mathlib","url":%q,"rev":%q}]}`, mathlibURL, rev))
	}
	writeManifest("not-the-pin")
	if _, err := pinnedSources(t.Context(), root, ""); err == nil || !strings.Contains(err.Error(), "unsupported Mathlib pin") {
		t.Fatalf("wrong manifest revision: %v", err)
	}
	writeManifest(mathlibRev)
	putFile(t, root, ".lake/packages/mathlib/Mathlib/Basic/Complex/Basic.lean", "edited source")
	if _, err := pinnedSources(t.Context(), root, ""); err == nil || !strings.Contains(err.Error(), "does not match Mathlib") {
		t.Fatalf("source with correct manifest but wrong content: %v", err)
	}
	if _, err := pinnedSources(t.Context(), root, filepath.Join("relative", "mathlib")); err == nil || !strings.Contains(err.Error(), "absolute path") {
		t.Fatalf("relative checkout override: %v", err)
	}
}
