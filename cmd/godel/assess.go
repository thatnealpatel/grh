package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"path/filepath"
	"strings"
)

// The improver is a constrained program, not an editor with
// access to the live Source. Its only possible proposal is a
// scheduler preference. It cannot adopt it.
func assess(in io.Reader, out io.Writer, args []string) error {
	if len(args) != 3 {
		return errors.New("invalid assessment paths")
	}
	raw, err := io.ReadAll(in)
	if err != nil {
		return err
	}
	_, s, ok := strings.Cut(string(raw), "\n# Run context\n\n")
	if !ok {
		return errors.New("missing Gödel run context")
	}
	var rc struct{ Goal, Input, Output, Failure string }
	if err = json.Unmarshal([]byte(s), &rc); err != nil {
		return err
	}
	w, err := load(args[0], args[1], args[2])
	if err != nil {
		return err
	}
	if rc.Goal != mission || !strings.Contains(rc.Input, w.plan.Goal) {
		return errors.New("improvement goal or task mismatch")
	}
	verdict := "No change: No repair is displacing a fresh eligible obligation."
	idx := choose(w.records, selection)
	if idx >= 0 && w.records[idx].Repairs > 0 {
		alt := choose(w.records, "fresh-before-repair")
		if alt >= 0 && w.records[alt].Repairs == 0 {
			control := []record{{Stage: "source", Block: "unresolved evidence"}, {Stage: "challenge"}}
			if choose(control, "fresh-before-repair") != 1 || choose(w.records, "fresh-before-repair") == idx {
				return errors.New("scheduler proposal failed replay or good control")
			}
			dir := filepath.Join(w.root, ".godel", "proposals", "fresh-before-repair")
			if err = atomicFile(filepath.Join(dir, "selection.txt"), []byte("fresh-before-repair\n")); err != nil {
				return err
			}
			verdict = fmt.Sprintf("Proposal only: On this replay prefer fresh obligation %s before retrying %s. Nearby control still skips an unchanged block. Review selection.txt for cmd/godel; no live policy or mathematics modified.", w.records[alt].Task.ID, w.records[idx].Task.ID)
		}
	}
	fmt.Fprintln(out, verdict)
	if strings.HasPrefix(verdict, "Proposal") {
		return atomicFile(filepath.Join(w.root, ".godel", "proposals", "fresh-before-repair", "rationale.md"), []byte(verdict+"\n"))
	}
	return nil
}
