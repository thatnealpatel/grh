package main

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
	"time"
)

func infer(ctx context.Context, proxy, instructions, input string) (string, error) {
	if proxy == "" {
		return "", fmt.Errorf("set ASTRA_PROXY to the yah proxy base URL")
	}
	body, err := json.Marshal(map[string]any{"model": "gpt-6.2-astra", "instructions": instructions, "input": []any{map[string]any{"role": "user", "content": input}}, "store": false, "stream": true})
	if err != nil {
		return "", err
	}
	ctx, cancel := context.WithTimeout(ctx, 30*time.Minute)
	defer cancel()
	req, err := http.NewRequestWithContext(ctx, http.MethodPost, strings.TrimRight(proxy, "/")+"/v1/responses", bytes.NewReader(body))
	if err != nil {
		return "", err
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Accept", "text/event-stream")
	req.Header.Set("X-Backend", "codex")
	res, err := http.DefaultClient.Do(req)
	if err != nil {
		return "", err
	}
	defer res.Body.Close()
	if res.StatusCode != 200 {
		msg, _ := io.ReadAll(io.LimitReader(res.Body, 2048))
		return "", fmt.Errorf("proxy %s: %s", res.Status, msg)
	}
	var text strings.Builder
	s := bufio.NewScanner(res.Body)
	s.Buffer(make([]byte, 64*1024), 16<<20)
	for s.Scan() {
		line, ok := strings.CutPrefix(s.Text(), "data:")
		if !ok {
			continue
		}
		var ev struct{ Type, Delta string }
		if err := json.Unmarshal([]byte(line), &ev); err != nil {
			return "", fmt.Errorf("proxy event: %w", err)
		}
		switch ev.Type {
		case "response.output_text.delta":
			text.WriteString(ev.Delta)
		case "response.completed":
			if strings.TrimSpace(text.String()) == "" {
				return "", fmt.Errorf("empty completion")
			}
			return text.String(), nil
		case "error", "response.failed", "response.incomplete":
			return "", fmt.Errorf("proxy: %s", ev.Type)
		}
	}
	if err := s.Err(); err != nil {
		return "", err
	}
	return "", fmt.Errorf("proxy stream ended without completion")
}
