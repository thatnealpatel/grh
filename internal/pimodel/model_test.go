package pimodel

import "testing"

func TestReceipt(t *testing.T) {
	for _, tc := range []struct {
		p, id, rp, rid string
		ok             bool
	}{
		{"exe-dev-anthropic", "claude-opus-4-8@llm", "exe-dev-anthropic", "claude-opus-4-8", true},
		{"exe-dev-openai", "x@llm", "exe-dev-openai", "x@llm", true},
		{"exe-dev-anthropic", "x@llm", "exe-dev-openai", "x", false},
		{"exe-dev-anthropic", "x@llm", "exe-dev-anthropic", "y", false},
		{"exe-dev-anthropic", "x@llm", "exe-dev-anthropic", "x@other", false},
		{"other", "x@llm", "other", "x", false},
	} {
		if Matches(tc.p, tc.id, tc.rp, tc.rid) != tc.ok {
			t.Errorf("unexpected receipt match for %+v", tc)
		}
	}
}
