package main

import (
	"crypto/sha256"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"time"

	"patel.codes/grh/internal/mathlane"
	"patel.codes/grh/internal/source"
)

type item struct {
	ID string
	source.Passage
}
type plan struct {
	Goal     string
	Passages []item
}

// One record per obligation. The draft
// is proposed Lean, never evidence of a
// successful build.
type record struct {
	Goal              string
	Task              item
	Stage             string
	Source            *source.Packet    `json:",omitempty"`
	Draft             *mathlane.Draft   `json:",omitempty"`
	Fidelity          *mathlane.Verdict `json:",omitempty"`
	Revision          string            `json:",omitempty"`
	PendingAdoption   string            `json:",omitempty"`
	Challenge         *mathlane.Verdict `json:",omitempty"`
	Landed            *mathlane.Draft   `json:",omitempty"`
	Interface         *mathlane.Draft   `json:",omitempty"`
	InterfaceRevision string            `json:",omitempty"`
	ProofAttempt      bool              `json:",omitempty"`
	Critique          string            `json:",omitempty"`
	Repairs           int               `json:",omitempty"`
	Block             string            `json:",omitempty"`
	Capability        string            `json:",omitempty"`
}

type allowance struct {
	Goal, PlanHash string
	Limit, Used    int
	Duration       time.Duration
	Deadline       time.Time
	Active         string `json:",omitempty"`
}

type work struct {
	root, planPath, budgetPath string
	plan                       plan
	records                    []record
	budget                     allowance
}

var identifier = regexp.MustCompile(`^[a-z][a-z0-9-]{0,63}$`)

func load(root, planPath, budgetPath string) (*work, error) {
	w := &work{root: root, planPath: planPath, budgetPath: budgetPath}
	if err := read(planPath, &w.plan); err != nil {
		return nil, err
	}
	if w.plan.Goal == "" || len(w.plan.Passages) == 0 {
		return nil, errors.New("goal and at least one passage required")
	}
	seen := map[string]bool{}
	for _, t := range w.plan.Passages {
		if !identifier.MatchString(t.ID) || seen[t.ID] || t.Question == "" || t.Heading == "" || t.First < 1 || t.Last < t.First {
			return nil, fmt.Errorf("invalid task %q", t.ID)
		}
		seen[t.ID] = true
		var r record
		err := read(w.path(t.ID), &r)
		if os.IsNotExist(err) {
			r = record{Goal: w.plan.Goal, Task: t, Stage: "source"}
		} else if err != nil {
			return nil, err
		}
		if r.Task != t || r.Goal != w.plan.Goal {
			return nil, fmt.Errorf("goal or passage for %s changed; give the new obligation a new ID", t.ID)
		}
		w.records = append(w.records, r)
	}
	if err := read(budgetPath, &w.budget); err != nil && !os.IsNotExist(err) {
		return nil, err
	}
	return w, nil
}
func (w *work) path(id string) string {
	return filepath.Join(w.root, ".godel", "obligations", id+".json")
}
func read(path string, v any) error {
	b, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	return json.Unmarshal(b, v)
}
func save(path string, v any) error {
	b, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return err
	}
	return atomicFile(path, append(b, '\n'))
}
func atomicFile(path string, b []byte) error {
	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return err
	}
	f, err := os.CreateTemp(dir, ".writing-*")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	if _, err = f.Write(b); err == nil {
		err = f.Sync()
	}
	err = errors.Join(err, f.Close())
	if err != nil {
		return err
	}
	if err = os.Rename(f.Name(), path); err != nil {
		return err
	}
	d, err := os.Open(dir)
	if err != nil {
		return err
	}
	defer d.Close()
	return d.Sync()
}
func digest(v any) string {
	b, err := json.Marshal(v)
	if err != nil {
		panic(err)
	}
	return fmt.Sprintf("%x", sha256.Sum256(b))
}
func (w *work) initBudget(n int, d time.Duration) error {
	b := &w.budget
	if b.Limit != 0 {
		if b.PlanHash != digest(w.plan) || b.Goal != w.plan.Goal || b.Limit != n || b.Duration != d {
			return errors.New("budget ID already bound to a different plan or allowance")
		}
		return nil
	}
	*b = allowance{Goal: w.plan.Goal, PlanHash: digest(w.plan), Limit: n, Duration: d, Deadline: time.Now().Add(d).UTC()}
	return save(w.budgetPath, b)
}

// A mechanical capability failure is
// actionable when its inputs change.
// Source dispositions and semantic
// blocks have no capability key.
func capability(stage string) string {
	var keys []string
	switch stage {
	case "source":
		keys = []string{"GRH_PDF"}
	case "land":
		keys = []string{"GRH_PROOF_WORKER", "GRH_CAMPAIGN_ADAPTER"}
	case "challenge", "prove":
		keys = []string{"GRH_MATHLIB", "GRH_CAMPAIGN_ADAPTER"}
	default:
		keys = []string{"GRH_MATHLIB"}
	}
	v := []string{stage, os.Getenv("GRH_CAPABILITY_EPOCH")}
	for _, k := range keys {
		s := os.Getenv(k)
		v = append(v, s)
		if fi, e := os.Stat(s); e == nil {
			v = append(v, fi.ModTime().String())
		}
	}
	return digest(v)
}
func eligible(r record) bool {
	return r.Stage != "checkpoint" && (r.Block == "" || r.Capability != "" && r.Capability != capability(r.Stage))
}
func choose(rs []record, policy string) int {
	policy = strings.TrimSpace(policy)
	idx := -1
	for i, r := range rs {
		if !eligible(r) {
			continue
		}
		if idx < 0 {
			idx = i
		}
		if policy == "fresh-before-repair" && r.Repairs == 0 {
			return i
		}
		if policy == "passage-order" {
			break
		}
	}
	return idx
}
func (w *work) terminal() string {
	if w.budget.Used >= w.budget.Limit || !time.Now().Before(w.budget.Deadline) {
		return "budget exhausted"
	}
	if choose(w.records, selection) < 0 {
		for _, r := range w.records {
			if r.Block != "" {
				return "no actionable work"
			}
		}
		return "pilot checkpoint"
	}
	return ""
}
func (w *work) report(reason string) string {
	var b strings.Builder
	fmt.Fprintf(&b, "%s (%d/%d attempts)\nGoal: %s\n", reason, w.budget.Used, w.budget.Limit, w.plan.Goal)
	for _, r := range w.records {
		fmt.Fprintf(&b, "%s: %s", r.Task.ID, r.Stage)
		if r.Source != nil {
			fmt.Fprintf(&b, ", source %s", r.Source.Disposition)
		}
		if r.Revision != "" {
			fmt.Fprintf(&b, ", adopted %s", r.Revision)
		}
		if r.Block != "" {
			fmt.Fprintf(&b, ", blocked: %s", r.Block)
		}
		if r.Draft != nil {
			fmt.Fprintf(&b, ", premises: %v", r.Draft.Premises)
		}
		fmt.Fprintln(&b)
	}
	if i := choose(w.records, selection); i >= 0 {
		fmt.Fprintf(&b, "Next: %s for %s", w.records[i].Stage, w.records[i].Task.ID)
	} else {
		fmt.Fprint(&b, "Next: no eligible obligation on unchanged inputs")
	}
	return b.String()
}
