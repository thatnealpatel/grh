package worker

import (
	"bytes"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestCheckLocal(t *testing.T) {
	for _, tc := range []struct{ name, want string }{
		{"matched", ""},
		{"multiple modules", ""},
		{"stale source", "workspace does not match"},
		{"extra source", "extra file"},
		{"outside module", "not a candidate module"},
		{"bad kernel check", "lake env leanchecker"},
		{"missing receipt", "missing project declaration audit"},
		{"missing signature", "no type signature for Example.ok"},
		{"changed during audit", "build inputs changed during audit"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var extra []string
			if tc.name == "multiple modules" {
				extra = []string{"Second"}
			}
			root, rev := repository(t, extra...)
			source := filepath.Join(root, "Proofs", "Props", "Example.lean")
			if tc.name != "stale source" {
				write(t, source, "theorem Example.ok : True := True.intro\n", 0644)
			}
			modules := []string{"Props.Example"}
			switch tc.name {
			case "multiple modules":
				modules = append(modules, "Props.Second")
			case "extra source":
				write(t, filepath.Join(root, "Proofs", "Props", "Extra.lean"), "", 0644)
			case "outside module":
				modules = []string{"Lean"}
			}
			bin := t.TempDir()
			t.Setenv("PATH", bin+string(os.PathListSeparator)+os.Getenv("PATH"))
			t.Setenv("SCENARIO", tc.name)
			write(t, filepath.Join(bin, "lake"), `#!/bin/sh
set -eu
case "$*" in
  '--wfail build Proofs') touch built ;;
  'env leanchecker -v Props.Example') test -f built; test "$SCENARIO" != 'bad kernel check'; touch replayed ;;
  'env leanchecker -v Props.Second') test -f replayed; touch second ;;
  'env lean --json --stdin')
    test -f replayed
    if [ "$SCENARIO" = 'multiple modules' ]; then test -f second; fi
    cat > audit.lean
    grep -q '^#print axioms Example.ok$' audit.lean
    grep -Fq 'endpoint signature' audit.lean
    grep -Fq '.signature d' audit.lean
    if [ "$SCENARIO" != 'missing signature' ]; then
      printf '%s\n' '{"severity":"information","data":"endpoint signature '"'"'Example.ok'"'"':\nExample.ok : True"}'
    fi
    if [ "$SCENARIO" != 'missing receipt' ]; then
      echo '{"severity":"information","data":"checked project declarations"}'
    fi
    echo '{"severity":"information","data":"'"'"'Example.ok'"'"' does not depend on any axioms"}'
    if [ "$SCENARIO" = 'changed during audit' ]; then
      echo '-- changed' >> Proofs/Props/Example.lean
    fi ;;
  *) exit 12 ;;
esac
`, 0700)
			var out bytes.Buffer
			err := CheckLocal(t.Context(), root, rev, modules, []string{"Example.ok"}, &out, io.Discard)
			if tc.want == "" {
				if err != nil || !strings.Contains(out.String(), "audit passed for "+rev) ||
					!strings.Contains(out.String(), "Example.ok : True") {
					t.Fatalf("expected scoped audit result, got %v and %q", err, out.String())
				}
				return
			}
			if err == nil || !strings.Contains(err.Error(), tc.want) || out.Len() != 0 {
				t.Fatalf("want failure containing %q and no receipt, got %v and %q", tc.want, err, out.String())
			}
			switch tc.name {
			case "stale source", "extra source", "outside module":
				if _, err := os.Stat(filepath.Join(root, "built")); !os.IsNotExist(err) {
					t.Fatalf("started a build from mismatched inputs: %v", err)
				}
			}
		})
	}
}
