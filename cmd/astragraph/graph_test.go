package main

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"sync"
	"testing"
)

const fixturePlan = `{"criteria":"validity","assignments":["A","B","C","D","E","F","G","H"]}`

func TestGraph(t *testing.T) {
	var mu sync.Mutex
	seen := map[string]packet{}
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		var body struct {
			Model, Instructions string
			Store, Stream       bool
			Input               []struct{ Role, Content string }
		}
		if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
			t.Error(err)
			w.WriteHeader(400)
			return
		}
		if r.URL.Path != "/v1/responses" || r.Method != "POST" || r.Header.Get("X-Backend") != "codex" || body.Model != "gpt-6.2-astra" || body.Store || !body.Stream || body.Instructions == "" || len(body.Input) != 1 || body.Input[0].Role != "user" {
			t.Error("wrong proxy request")
			w.WriteHeader(400)
			return
		}
		var p packet
		if err := json.Unmarshal([]byte(body.Input[0].Content), &p); err != nil {
			t.Error(err)
			w.WriteHeader(400)
			return
		}
		mu.Lock()
		if _, ok := seen[p.ID]; ok {
			t.Errorf("duplicate %s", p.ID)
		}
		seen[p.ID] = p
		mu.Unlock()
		answer := "output:" + p.ID
		if p.ID == "frame" {
			answer = fixturePlan
		}
		event, _ := json.Marshal(map[string]string{"type": "response.output_text.delta", "delta": answer})
		fmt.Fprintf(w, "data: %s\n\ndata: {\"type\":\"response.completed\"}\n\n", event)
	}))
	defer server.Close()
	result, err := graph(t.Context(), "original", func(ctx context.Context, instructions, input string) (string, error) {
		return infer(ctx, server.URL, instructions, input)
	})
	if err != nil || result != "output:synthesize" {
		t.Fatalf("%q, %v", result, err)
	}
	mu.Lock()
	defer mu.Unlock()
	if len(seen) != 34 {
		t.Fatalf("%d calls", len(seen))
	}
	id := func(stage string, i int) string { return fmt.Sprintf("%s/%d", stage, i%8) }
	check := func(key string, want ...string) {
		t.Helper()
		p := seen[key]
		if p.Task != "original" || (key != "frame" && p.Criteria != "validity") {
			t.Errorf("%s lost task or criteria", key)
		}
		var ids []string
		for _, s := range p.Sources {
			ids = append(ids, s.ID)
			if s.Text != "output:"+s.ID {
				t.Errorf("%s lost %s output", key, s.ID)
			}
		}
		if !slices.Equal(ids, want) {
			t.Errorf("%s got %v want %v", key, ids, want)
		}
	}
	check("frame")
	var final []string
	for i := range width {
		check(id("propose", i))
		if seen[id("propose", i)].Assignment != string(rune('A'+i)) {
			t.Errorf("wrong assignment at %d", i)
		}
		check(id("challenge", i), id("propose", i), id("propose", i+1))
		check(id("repair", i), id("propose", i), id("challenge", i+7), id("challenge", i))
		check(id("audit", i), id("repair", i), id("repair", i+3), id("challenge", i+7), id("challenge", i), id("challenge", i+2), id("challenge", i+3))
		final = append(final, id("audit", i))
	}
	for i := range width {
		final = append(final, id("repair", i))
	}
	check("synthesize", final...)
}

func TestInvalidFrame(t *testing.T) {
	calls := 0
	out, err := graph(t.Context(), "task", func(context.Context, string, string) (string, error) { calls++; return `{}`, nil })
	if calls != 1 || err == nil || out != "" {
		t.Fatalf("calls=%d out=%q err=%v", calls, out, err)
	}
}

func TestTruncatedStream(t *testing.T) {
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprintln(w, `data: {"type":"response.output_text.delta","delta":"partial"}`)
	}))
	defer srv.Close()
	out, err := infer(t.Context(), srv.URL, "answer", "task")
	if out != "" || err == nil || !strings.Contains(err.Error(), "without completion") {
		t.Fatalf("%q %v", out, err)
	}
}

func TestFailedLaneCancelsSiblings(t *testing.T) {
	var started sync.WaitGroup
	started.Add(width)
	out, err := graph(t.Context(), "task", func(ctx context.Context, role, input string) (string, error) {
		if role == frame {
			return fixturePlan, nil
		}
		if role != roles[0] {
			t.Errorf("unexpected later stage %s", role)
			return "", fmt.Errorf("unexpected stage")
		}
		var p packet
		if err := json.Unmarshal([]byte(input), &p); err != nil {
			return "", err
		}
		started.Done()
		started.Wait()
		if p.ID == "propose/4" {
			return "", fmt.Errorf("injected failure")
		}
		<-ctx.Done()
		return "", ctx.Err()
	})
	if out != "" || err == nil || !strings.Contains(err.Error(), "propose/4: injected failure") {
		t.Fatalf("%q %v", out, err)
	}
}
