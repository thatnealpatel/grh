package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"sync"
	"testing"
)

func TestRing(t *testing.T) {
	want := map[string]string{
		"A1": "", "A2": "", "A3": "", "A4": "",
		"B1": "A1 A2", "B2": "A2 A3", "B3": "A3 A4", "B4": "A4 A1",
		"C1": "A1 B4 B1", "C2": "A2 B1 B2", "C3": "A3 B2 B3", "C4": "A4 B3 B4",
		"D1": "C1 C2 C3 C4",
	}
	var mu sync.Mutex
	seen := map[string]string{}
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		var req struct {
			Instructions string
			Input        []struct{ Content string }
		}
		if err := json.NewDecoder(r.Body).Decode(&req); err != nil || len(req.Input) != 1 {
			t.Errorf("bad request: %v", err)
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		var p packet
		if err := json.Unmarshal([]byte(req.Input[0].Content), &p); err != nil {
			t.Error(err)
			w.WriteHeader(http.StatusBadRequest)
			return
		}
		var ids []string
		for _, src := range p.Sources {
			if src.Text != "reply:"+src.ID {
				t.Errorf("%s lost %s output", p.ID, src.ID)
			}
			ids = append(ids, src.ID)
		}
		inputs, ok := want[p.ID]
		if !ok || !slices.Equal(ids, strings.Fields(inputs)) || p.Task != "test task" {
			t.Errorf("unexpected packet: %+v", p)
		}
		mu.Lock()
		for id, role := range seen {
			if id == p.ID || role == req.Instructions {
				t.Errorf("%s duplicates %s or its role", p.ID, id)
			}
		}
		seen[p.ID] = req.Instructions
		mu.Unlock()
		fmt.Fprintf(w, "data: {\"type\":\"response.output_text.delta\",\"delta\":\"reply:%s\"}\n\ndata: {\"type\":\"response.completed\"}\n\n", p.ID)
	}))
	defer srv.Close()
	out, err := graph(t.Context(), "test task", func(ctx context.Context, role, input string) (string, error) {
		return infer(ctx, srv.URL, role, input)
	})
	mu.Lock()
	defer mu.Unlock()
	if err != nil || out != "reply:D1" || len(seen) != len(want) {
		t.Fatalf("out=%q err=%v nodes=%d", out, err, len(seen))
	}
}

func TestFailedChallengeStopsRing(t *testing.T) {
	failure := errors.New("challenge failed")
	out, err := graph(t.Context(), "task", func(ctx context.Context, role, input string) (string, error) {
		var p packet
		if err := json.Unmarshal([]byte(input), &p); err != nil {
			return "", err
		}
		switch p.ID[0] {
		case 'A':
			return "derivation", nil
		case 'B':
			if p.ID == "B3" {
				return "", failure
			}
			<-ctx.Done()
			return "", ctx.Err()
		default:
			t.Errorf("unexpected later call %s", p.ID)
			return "", failure
		}
	})
	if !errors.Is(err, failure) || out != "" {
		t.Fatalf("out=%q err=%v", out, err)
	}
}
