package main

import (
	"bytes"
	"path/filepath"
	"strings"
	"testing"
)

func TestCheckProofDoesNotReportUncheckedSuccess(t *testing.T) {
	for _, tc := range []struct {
		name, transport, revision, want string
	}{
		{"missing transport", "", strings.Repeat("a", 40), "GRH_PROOF_WORKER"},
		{"short revision", filepath.Join(t.TempDir(), "unused"), "abc", "full jj commit ID"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			t.Setenv("GRH_PROOF_WORKER", tc.transport)
			var out bytes.Buffer
			err := checkProof(t.Context(), &out, []string{tc.revision, "Example.result"})
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("want error containing %q, got %v", tc.want, err)
			}
			if out.Len() != 0 {
				t.Fatalf("reported a result without a worker receipt: %q", out.String())
			}
		})
	}
}
