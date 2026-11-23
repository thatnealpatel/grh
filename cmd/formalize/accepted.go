package main

import (
	"context"
	"fmt"
	"log"
	"os/exec"
	"path"
	"path/filepath"
	"strconv"
	"strings"

	"encoding/json/v2"
)

type repository struct {
	root, gitDir, target string
}

func openRepository(ctx context.Context, root, target string) (repository, error) {
	if target == "" {
		target = "main"
	}
	r := repository{root: root, target: target}
	out, err := r.jj(ctx, "git", "root")
	if err != nil {
		return r, err
	}
	r.gitDir, err = filepath.EvalSymlinks(out)
	if err != nil {
		return r, err
	}
	if !filepath.IsAbs(r.gitDir) {
		return r, fmt.Errorf("expected an absolute backing Git path, got %q", r.gitDir)
	}
	return r, nil
}

func (r repository) command(ctx context.Context, name string, args ...string) ([]byte, error) {
	cmd := exec.CommandContext(ctx, name, args...)
	cmd.Dir = r.root
	out, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("%s %v: %w", name, args, err)
	}
	return out, nil
}

func (r repository) jj(ctx context.Context, args ...string) (string, error) {
	out, err := r.command(ctx, "jj", append([]string{"--ignore-working-copy", "--at-op=@"}, args...)...)
	return strings.TrimSuffix(string(out), "\n"), err
}

func (r repository) git(ctx context.Context, args ...string) ([]byte, error) {
	return r.command(ctx, "git", append([]string{"--no-replace-objects", "--literal-pathspecs", "--git-dir", r.gitDir}, args...)...)
}

func commitID(s string) bool {
	return (len(s) == 40 || len(s) == 64) && strings.Trim(s, "0123456789abcdef") == ""
}

func (r repository) tip(ctx context.Context) (string, error) {
	// Resolve the same exact local target as accepted.Enter, not the checkout.
	tip, err := r.jj(ctx, "bookmark", "list", "-T", `if(!remote && normal_target && !normal_target.conflict(), normal_target.commit_id() ++ "\n")`, "--", "exact:"+strconv.Quote(r.target))
	if err != nil {
		return "", err
	}
	if !commitID(tip) {
		return "", fmt.Errorf("no unambiguous local bookmark %q", r.target)
	}
	out, err := r.git(ctx, "rev-parse", "--verify", "refs/heads/"+r.target+"^{commit}")
	if err != nil {
		return "", err
	}
	if branch := strings.TrimSuffix(string(out), "\n"); branch != tip {
		return "", fmt.Errorf("accepted target %q disagrees: jj %s, Git %s", r.target, tip, branch)
	}
	return tip, nil
}

// A receipt is authoritative only in the
// accepted tree. A landed Lean artifact
// and its receipt are part of the same
// candidate.
type receipt struct {
	Key      string     `json:"key"`
	Revision string     `json:"revision"`
	Outcome  string     `json:"outcome"`
	Source   string     `json:"source"`
	Finding  string     `json:"finding"`
	Retry    string     `json:"retry,omitempty"`
	Evidence []evidence `json:"evidence,omitempty"`
}

// A valid proof receipt can dispose of
// the assignment without covering the
// passage. Preserve the legacy retry
// field as the marker of a partial
// landing.
func (d receipt) coversPassage() bool {
	return d.Outcome == "already_covered" || (d.Outcome == "landed" && d.Retry == "")
}

type evidence struct {
	Path         string   `json:"path"`
	Revision     string   `json:"revision,omitempty"`
	Declarations []string `json:"declarations,omitempty"`
}

func (r repository) receiptTree(ctx context.Context, tip string) (map[string]string, error) {
	if !commitID(tip) {
		return nil, fmt.Errorf("receipt tree requires a full commit ID, got %q", tip)
	}
	out, err := r.git(ctx, "ls-tree", "--full-tree", "-rz", tip, "--", noteDir)
	if err != nil {
		return nil, err
	}
	files := make(map[string]string)
	for line := range strings.SplitSeq(string(out), "\x00") {
		meta, name, _ := strings.Cut(line, "\t")
		if oid, ok := strings.CutPrefix(meta, "100644 blob "); ok && commitID(oid) {
			files[name] = oid
		}
	}
	return files, nil
}

// disposition distinguishes absent/invalid evidence (still pending) from a
// plumbing error (we could not observe the accepted tree).
func (r repository) disposition(ctx context.Context, tip string, notes map[string]string, a assignment) (receipt, string, error) {
	if a.Lane != proofLane && a.Lane != statementLane {
		return receipt{}, "unknown assignment lane", nil
	}
	oid, ok := notes[a.path()]
	if !ok {
		return receipt{}, "no accepted receipt", nil
	}
	data, err := r.git(ctx, "cat-file", "blob", oid)
	if err != nil {
		return receipt{}, "", err
	}
	var d receipt
	if err := json.Unmarshal(data, &d, json.RejectUnknownMembers(true)); err != nil {
		return receipt{}, "invalid receipt JSON: " + err.Error(), nil
	}
	if d.Key != a.Key || d.Revision != a.Revision || blank(d.Source) || blank(d.Finding) {
		return receipt{}, "wrong identity or missing source/finding", nil
	}
	statementOutcome := d.Outcome == "statement_checked" || d.Outcome == "statement_blocked"
	if (a.Lane == statementLane) != statementOutcome {
		return receipt{}, "invalid outcome for assignment lane", nil
	}
	switch d.Outcome {
	case "substantive_failure", "statement_blocked":
		if blank(d.Retry) || len(d.Evidence) != 0 {
			return receipt{}, "failure requires a retry condition and no structured Lean evidence", nil
		}
		return d, "", nil
	case "landed", "already_covered":
		if len(d.Evidence) == 0 || (d.Outcome == "already_covered" && d.Retry != "") {
			return receipt{}, "success requires Lean evidence; coverage cannot have a retry condition", nil
		}
	case "statement_checked":
		if d.Retry != "" || len(d.Evidence) != 1 || len(d.Evidence[0].Declarations) != 1 {
			return receipt{}, "checked statement requires one defining Lean path and declaration and no retry condition", nil
		}
	default:
		return receipt{}, "unknown disposition", nil
	}
	var landing string
	for _, e := range d.Evidence {
		if !strings.HasPrefix(e.Path, "Proofs/") || path.Clean(e.Path) != e.Path || !strings.HasSuffix(e.Path, ".lean") || strings.ContainsAny(e.Path, "\x00\r\n") || len(e.Declarations) == 0 {
			return receipt{}, "invalid Lean path or missing declarations", nil
		}
		for _, name := range e.Declarations {
			if blank(name) {
				return receipt{}, "empty declaration name", nil
			}
		}
		rev := e.Revision
		if d.Outcome == "landed" || (d.Outcome == "statement_checked" && rev == "") {
			if rev != "" {
				return receipt{}, "landed evidence must be in the receipt candidate", nil
			}
			if landing == "" {
				out, err := r.git(ctx, "log", "-1", "--first-parent", "--format=%H", tip, "--", a.path())
				if err != nil {
					return receipt{}, "", err
				}
				landing = strings.TrimSpace(string(out))
				if !commitID(landing) {
					return receipt{}, "cannot locate receipt candidate", nil
				}
			}
			rev = landing
			changed, err := r.git(ctx, "diff-tree", "--root", "--no-commit-id", "-r", "--name-only", rev, "--", e.Path)
			if err != nil {
				return receipt{}, "", err
			}
			if len(changed) == 0 {
				return receipt{}, "landing did not change the cited Lean path", nil
			}
		} else {
			if !commitID(rev) {
				return receipt{}, "coverage requires an exact accepted evidence revision", nil
			}
			_, err := r.git(ctx, "merge-base", "--is-ancestor", rev, tip)
			if err != nil {
				// A missing object and an unaccepted object are both insufficient evidence.
				return receipt{}, "coverage revision not proved accepted: " + err.Error(), ctx.Err()
			}
		}
		original, err := r.leanBlob(ctx, rev, e.Path)
		if err != nil {
			return receipt{}, "", err
		}
		if original == "" {
			return receipt{}, "cited Lean path missing from evidence revision", nil
		}
		if rev != tip {
			current, err := r.leanBlob(ctx, tip, e.Path)
			if err != nil {
				return receipt{}, "", err
			}
			if original != current {
				return receipt{}, "cited Lean file changed since evidence revision; reconcile coverage", nil
			}
		}
	}
	return d, "", nil
}

func (r repository) leanBlob(ctx context.Context, rev, file string) (string, error) {
	out, err := r.git(ctx, "ls-tree", "--full-tree", "-z", rev, "--", file)
	if err != nil {
		return "", err
	}
	meta, name, _ := strings.Cut(strings.TrimSuffix(string(out), "\x00"), "\t")
	if oid, ok := strings.CutPrefix(meta, "100644 blob "); ok && name == file && commitID(oid) {
		return oid, nil
	}
	return "", nil
}

func blank(s string) bool { return strings.TrimSpace(s) == "" }

func (r repository) selectBatch(ctx context.Context, tip string, work []assignment, limit int) ([]assignment, error) {
	if limit <= 0 {
		return nil, fmt.Errorf("nonpositive formalize batch limit %d", limit)
	}
	notes, err := r.receiptTree(ctx, tip)
	if err != nil {
		return nil, err
	}
	var pending []assignment
	proofs := make([]receipt, len(work))
	for i, a := range work {
		a.Lane = proofLane
		proof, err := r.pendingDisposition(ctx, tip, notes, a)
		if err != nil {
			return nil, err
		}
		proofs[i] = proof
		if proof.Outcome == "" {
			pending = append(pending, a)
			if len(pending) == limit {
				return pending, nil
			}
		}
	}
	// Scheduling policy, not statement
	// eligibility: drain pending proofs
	// first.
	if len(pending) > 0 {
		return pending, nil
	}
	for i, a := range work {
		candidate, needed, err := r.statementCandidate(ctx, tip, notes, a, proofs[i])
		if err != nil {
			return nil, err
		}
		if needed {
			pending = append(pending, candidate)
			if len(pending) == limit {
				break
			}
		}
	}
	return pending, nil
}

func (r repository) pendingDisposition(ctx context.Context, tip string, notes map[string]string, a assignment) (receipt, error) {
	d, problem, err := r.disposition(ctx, tip, notes, a)
	if err == nil && d.Outcome == "" && notes[a.path()] != "" {
		log.Printf("formalize: %s: %s", a.path(), problem)
	}
	return d, err
}

// Statement eligibility is independent of proof priority. Only full proof
// coverage or a valid statement disposition suppresses this candidate.
func (r repository) statementCandidate(ctx context.Context, tip string, notes map[string]string, a assignment, proof receipt) (assignment, bool, error) {
	if proof.coversPassage() {
		return assignment{}, false, nil
	}
	a.Lane = statementLane
	d, err := r.pendingDisposition(ctx, tip, notes, a)
	return a, err == nil && d.Outcome == "", err
}

func (r repository) acknowledge(ctx context.Context, b batch, tip string) error {
	notes, err := r.receiptTree(ctx, tip)
	if err != nil {
		return err
	}
	var missing []string
	for _, a := range b.Assignments {
		d, problem, err := r.disposition(ctx, tip, notes, a)
		if err != nil {
			return err
		}
		if d.Outcome == "" {
			missing = append(missing, a.path()+": "+problem)
			continue
		}
		log.Printf("formalize: %s at %s: %s", a.path(), tip, d.Outcome)
	}
	if len(missing) > 0 {
		return fmt.Errorf("formalize: unresolved assignments (operational stop; restart after reconciliation): %s", strings.Join(missing, "; "))
	}
	return nil
}
