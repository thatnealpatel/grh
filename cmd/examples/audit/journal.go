package main

import (
	"context"
	"crypto/sha256"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"

	"encoding/json/v2"
)

// Scope is one accepted parent-child
// edge, even if its patch is empty.
type scope struct {
	Base   string   `json:"base"`
	Target string   `json:"target"`
	Paths  []string `json:"paths"`
	Lean   bool     `json:"lean"`
}

type reply struct {
	Base     string `json:"base"`
	Target   string `json:"target"`
	Verdict  string `json:"verdict"`
	Evidence string `json:"evidence"`
	Lean     *lean  `json:"lean"`
	Finding  string `json:"finding"`
	Repair   string `json:"repair"`
}

type lean struct {
	Result    string `json:"result"` // pass or a verified source defect
	Build     string `json:"build"`
	Joint     string `json:"joint_import"`
	Replay    string `json:"kernel_replay"`
	Endpoints string `json:"endpoints"`
}

func (r reply) validate(s scope) error {
	if r.Base != s.Base || r.Target != s.Target {
		return errors.New("audit: reply does not bind the requested parent and child")
	}
	if !nonblank(r.Evidence) || (s.Lean && r.Lean == nil) || (r.Lean != nil &&
		(!nonblank(r.Lean.Build) || !nonblank(r.Lean.Joint) || !nonblank(r.Lean.Replay) || !nonblank(r.Lean.Endpoints))) {
		return errors.New("audit: missing review or Lean evidence")
	}
	if r.Lean != nil && r.Lean.Result != "pass" && (r.Lean.Result != "defect" || r.Verdict != "finding") {
		return errors.New("audit: invalid Lean result")
	}
	switch r.Verdict {
	case "clean":
		if r.Finding != "" || r.Repair != "" {
			return errors.New("audit: inconsistent clean review")
		}
	case "finding":
		if !nonblank(r.Finding) || !nonblank(r.Repair) {
			return errors.New("audit: missing finding or repair pointer")
		}
	default:
		return errors.New("audit: incomplete or invalid verdict")
	}
	return nil
}

func nonblank(s string) bool { return strings.TrimSpace(s) != "" }
func digest(b []byte) string { return fmt.Sprintf("%x", sha256.Sum256(b)) }

func encode(v any) []byte {
	b, err := json.Marshal(v)
	if err != nil {
		panic(err) // only used for our serializable, validated types
	}
	return b
}

func decode(b []byte, v any) error { return json.Unmarshal(b, v, json.RejectUnknownMembers(true)) }

type record struct {
	Scope scope `json:"scope"`
	Reply reply `json:"reply"`
}

func notePath(target string) string { return ".godel/audit/" + target + ".md" }

func (r record) note() []byte {
	var b strings.Builder
	fmt.Fprintf(&b, "# Independent audit finding\n\nAccepted parent `%s`, reviewed commit `%s`.\n\n", r.Scope.Base, r.Scope.Target)
	b.WriteString("This handoff records defects, not a proof repair or a verdict on RH/GRH.\n")
	e := r.Reply
	fmt.Fprintf(&b, "\n## Finding\n\n%s\n\n## Evidence\n\n%s\n", e.Finding, e.Evidence)
	if e.Lean != nil {
		fmt.Fprintf(&b, "\n- Full build: %s\n- Joint import: %s\n- Kernel replay: %s\n- Endpoints: %s\n", e.Lean.Build, e.Lean.Joint, e.Lean.Replay, e.Lean.Endpoints)
	}
	fmt.Fprintf(&b, "\n## Proposed repair or follow-up\n\n%s\n", e.Repair)
	return []byte(b.String())
}

type identity struct{ Source, Git, Target string }

type finding struct {
	Note    string `json:"accepted_revision"`
	Path    string `json:"path"`
	Covered bool   `json:"bookkeeping_examined"`
}

type journal struct {
	Version  int       `json:"version"`
	Identity identity  `json:"identity"`
	Baseline string    `json:"baseline"`
	Examined string    `json:"examined"`
	Latest   *record   `json:"latest_review,omitempty"`
	Pending  *record   `json:"pending_publication,omitempty"`
	Findings []finding `json:"findings,omitempty"`
}

type auditor struct {
	repo  history
	file  string
	wait  func(context.Context) error
	state journal
	fresh bool
}

func (a *auditor) load(id identity, baseline string) error {
	b, err := os.ReadFile(a.file)
	if errors.Is(err, fs.ErrNotExist) {
		if !commitID(baseline) {
			return errors.New("audit: new journal requires -baseline with a full accepted ancestor commit")
		}
		a.state = journal{Version: 1, Identity: id, Baseline: baseline, Examined: baseline}
		a.fresh = true
		return nil // persist only after confirming ancestry in prepare
	}
	if err != nil {
		return err
	}
	var j journal
	if err := decode(b, &j); err != nil {
		return fmt.Errorf("audit journal: %w", err)
	}
	if j.Version != 1 || j.Identity != id || !commitID(j.Baseline) || !commitID(j.Examined) ||
		(baseline != "" && baseline != j.Baseline) || (j.Latest == nil) != (j.Examined == j.Baseline) {
		return errors.New("audit: journal version, source, target, or baseline mismatch, or invalid checkpoint")
	}
	check := func(r *record) error {
		if !commitID(r.Scope.Base) || !commitID(r.Scope.Target) || r.Scope.Base == r.Scope.Target {
			return errors.New("audit: invalid journal scope")
		}
		return r.Reply.validate(r.Scope)
	}
	if j.Latest != nil {
		if err := check(j.Latest); err != nil {
			return err
		}
	}
	if p := j.Pending; p != nil {
		if p.Scope.Base != j.Examined || p.Reply.Verdict != "finding" {
			return errors.New("audit: invalid pending publication")
		}
		if err := check(p); err != nil {
			return err
		}
	}
	seen := make(map[string]bool)
	for _, f := range j.Findings {
		target, ok := strings.CutPrefix(strings.TrimSuffix(f.Path, ".md"), ".godel/audit/")
		if !commitID(f.Note) || !ok || !commitID(target) || f.Path != notePath(target) || seen[f.Note] {
			return errors.New("audit: invalid persisted finding pointer")
		}
		seen[f.Note] = true
	}
	a.state, a.fresh = j, false
	return nil
}

func (a *auditor) save(ctx context.Context, j journal) error {
	dir, err := os.Open(filepath.Dir(a.file))
	if err != nil {
		return err
	}
	defer dir.Close()
	f, err := os.CreateTemp(dir.Name(), ".grh-audit-*")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	defer f.Close()
	if _, err := f.Write(append(encode(j), '\n')); err != nil {
		return err
	}
	if err := f.Sync(); err != nil {
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	if err := ctx.Err(); err != nil {
		return err
	}
	// Rename is the checkpoint commit point;
	// cancellation before it leaves the old state
	// intact. Sync the directory to persist the
	// replacement.
	if err := os.Rename(f.Name(), a.file); err != nil {
		return err
	}
	if err := dir.Sync(); err != nil {
		return err
	}
	a.state, a.fresh = j, false
	return nil
}
