package main

import (
	"context"
	"encoding/json/v2"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"testing/synctest"
	"time"

	"patel.codes/godel"
)

func recordJSON(locator, status string) string {
	if status == "established" || status == "refuted" {
		return fmt.Sprintf(`{"passage":{"kind":"lemma","locator":%q,"printed_page":17},"printed_finding":"The source claims P.","formal":{"status":%q,"scope":"P","argument_provenance":"printed"},"references":[{"kind":"lean","target":"P","revision":"fixture"}]}`, locator, status)
	}
	return fmt.Sprintf(`{"passage":{"kind":"lemma","locator":%q,"printed_page":17},"printed_finding":"The source claims P.","formal":{"status":%q,"scope":"P","argument_provenance":"printed"}}`, locator, status)
}

func chapterJSON(chapter string, records ...string) string {
	cursor := "null"
	if len(records) > 0 {
		_, rest, _ := strings.Cut(records[len(records)-1], `"passage":`)
		p, _, _ := strings.Cut(rest, "}")
		cursor = p + "}"
	}
	return fmt.Sprintf(`{"edition":%q,"chapter":%q,"cursor":%s,"complete":false,"records":[%s]}`, edition, chapter, cursor, strings.Join(records, ","))
}

func writeChapter(t *testing.T, dir, chapter string, records ...string) {
	t.Helper()
	if err := os.WriteFile(filepath.Join(dir, chapter+".json"), []byte(chapterJSON(chapter, records...)), 0600); err != nil {
		t.Fatal(err)
	}
}

func readAssignments(t *testing.T, dir string) []assignment {
	t.Helper()
	work, err := readWalk(t.Context(), dir)
	if err != nil {
		t.Fatal(err)
	}
	return work
}

func TestWalkPath(t *testing.T) {
	root, home := t.TempDir(), t.TempDir()
	actual := filepath.Join(root, "source")
	if err := os.Mkdir(actual, 0700); err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(filepath.Join(root, "cmd"), 0700); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(actual, filepath.Join(root, "cmd", "walk")); err != nil {
		t.Fatal(err)
	}
	dir, err := walkLedger(root, home)
	if err != nil || dir != filepath.Join(home, ".grh-walk-"+digest([]byte(actual))) {
		t.Fatalf("ledger = %q, %v", dir, err)
	}
	if n := len(readAssignments(t, dir)); n != 0 {
		t.Fatalf("missing ledger provided %d assignments", n)
	}
	if _, err := os.Stat(dir); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("reading must not create the ledger: %v", err)
	}
}

func TestOrderAndLimit(t *testing.T) {
	dir := t.TempDir()
	writeChapter(t, dir, "appendix-a", recordJSON("A", "established"))
	writeChapter(t, dir, "chapter-02", recordJSON("2", "refuted"))
	writeChapter(t, dir, "chapter-01", recordJSON("heading", "not_applicable"), recordJSON("z", "open"), recordJSON("a", "open"))
	work := readAssignments(t, dir)
	if len(work) != 4 || !strings.Contains(string(work[0].Record), `"locator":"z"`) || !strings.Contains(string(work[1].Record), `"locator":"a"`) || work[2].Chapter != "chapter-02" || work[3].Chapter != "appendix-a" {
		t.Fatalf("wrong reading order: %+v", work)
	}
	r := newRepo(t)
	base := snapshot(t, r, "", nil)
	pending, err := r.selectBatch(t.Context(), base, work, batchCap)
	if err != nil || len(pending) != 1 || pending[0].Key != work[0].Key {
		t.Fatalf("wrong batch: %+v, %v", pending, err)
	}
}

func TestRecordRevision(t *testing.T) {
	const id = "chapter-01"
	original := recordJSON("1.2", "open")
	parse := func(data string) assignment {
		t.Helper()
		work, err := appendChapter(nil, id, []byte(data))
		if err != nil || len(work) != 1 {
			t.Fatalf("appendChapter = %+v, %v", work, err)
		}
		return work[0]
	}
	a := parse(chapterJSON(id, original))
	reordered := `{"formal":{"scope":"P","status":"open","argument_provenance":"printed"}, "printed_finding":"The source claims P.", "passage":{"printed_page":17,"locator":"1.2","kind":"lemma"}}`
	b := parse(strings.Replace(chapterJSON(id, reordered), `"complete":false`, `"complete":true`, 1))
	if a.Key != b.Key || a.Revision != b.Revision {
		t.Fatal("JSON layout or completion changed the assignment identity")
	}
	changed := strings.TrimSuffix(original, "}") + `,"dependencies":[{"requirement":{"source":{"chapter":"chapter-01","passage":{"kind":"lemma","locator":"1.1","printed_page":17}},"conclusion":"Q"},"reviewed":null}]}`
	c := parse(chapterJSON(id, changed))
	d := parse(chapterJSON(id, strings.Replace(changed, `"reviewed":null`, `"reviewed":{"verdict":"supports","reference":{"kind":"lean","target":"Q","revision":"abc"}}`, 1)))
	if a.Key != c.Key || c.Key != d.Key || a.Revision == c.Revision || c.Revision == d.Revision {
		t.Fatal("reviewed evidence must revise the same passage")
	}
}

func TestIdleGate(t *testing.T) {
	dir := t.TempDir()
	synctest.Test(t, func(t *testing.T) {
		ctx, cancel := context.WithCancel(t.Context())
		defer cancel()
		var request string
		var reads int
		gate := startNode(ctx, repository{}, func(context.Context) (string, error) {
			reads++
			return "", errors.New("empty ledger should not need an accepted tip")
		}, dir, batchCap, &request)
		type result struct {
			node *godel.Node
			err  error
		}
		done := make(chan result, 1)
		go func() {
			node, err := gate.Next(godel.Result{Text: "stale work"})
			done <- result{node, err}
		}()
		synctest.Wait()
		<-time.After(2 * idleDelay)
		synctest.Wait()
		select {
		case got := <-done:
			t.Fatalf("idle gate returned early: %+v", got)
		default:
		}
		cancel()
		got := <-done
		if !errors.Is(got.err, context.Canceled) || got.node != nil || request != "" || reads != 0 {
			t.Fatalf("idle result = %+v; request=%q tip reads=%d", got, request, reads)
		}
	})
}

func TestDispatchAndOperationalStop(t *testing.T) {
	t.Setenv("TMPDIR", t.TempDir())
	dir := t.TempDir()
	writeChapter(t, dir, "chapter-01", recordJSON("first", "open"))
	work := readAssignments(t, dir)
	r := newRepo(t)
	base := snapshot(t, r, "", nil)
	var request string
	head := base
	start := func(old string) *godel.Node {
		t.Helper()
		gate := startNode(t.Context(), r, func(context.Context) (string, error) { return head, nil }, dir, batchCap, &request)
		n, err := gate.Next(godel.Result{Text: old})
		if err != nil || n == nil {
			t.Fatalf("dispatch = %+v, %v", n, err)
		}
		return n
	}
	n := start("untrusted stale stdin")
	if n.Directory != r.root || !strings.Contains(strings.Join(n.Args, " "), request) || strings.Contains(strings.Join(n.Args, " "), "untrusted stale stdin") {
		t.Fatalf("wrong coordinator inputs: %+v", n)
	}
	data, err := os.ReadFile(request)
	if err != nil {
		t.Fatal(err)
	}
	info, err := os.Stat(request)
	if err != nil || info.Mode().Perm() != 0600 {
		t.Fatalf("request not private: %v, %v", info, err)
	}
	var b batch
	if err := json.Unmarshal(data, &b); err != nil || b.Edition != edition || b.AcceptedTip != base || b.Target != r.target || len(b.Assignments) != 1 || b.Assignments[0].Revision != work[0].Revision {
		t.Fatalf("wrong request: %+v, %v", b, err)
	}
	firstRequest := request
	if next, err := n.Next(godel.Result{Text: "I landed everything"}); next != nil || err == nil || !strings.Contains(err.Error(), "no accepted receipt") {
		t.Fatalf("claim without accepted disposition = %+v, %v", next, err)
	}
	if _, err := os.Stat(firstRequest); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("batch input left behind: %v", err)
	}
	n = start("another old receipt")
	if request == firstRequest || request == "" {
		t.Fatalf("dispatch reused request: %q", request)
	}
	head = snapshot(t, r, base, map[string]string{
		work[0].path(): note(t, work[0], "substantive_failure", "Reconsider if premise Q is justified"),
	})
	if next, err := n.Next(godel.Result{Text: "unstructured handoff"}); next != nil || err != nil || request != "" {
		t.Fatalf("accepted outcome did not enable continuation: %+v, %v, request=%q", next, err, request)
	}
}

func newRepo(t *testing.T) repository {
	t.Helper()
	r := repository{root: t.TempDir(), target: "main"}
	r.gitDir = filepath.Join(r.root, "objects.git")
	if _, err := r.command(t.Context(), "git", "init", "--bare", "--template=", r.gitDir); err != nil {
		t.Fatal(err)
	}
	return r
}

// snapshot writes fixture objects to a temporary bare Git repo; no refs or
// workspace history are changed. files is the complete tree of the snapshot.
func snapshot(t *testing.T, r repository, parent string, files map[string]string) string {
	t.Helper()
	git := func(input string, args ...string) string {
		t.Helper()
		cmd := exec.CommandContext(t.Context(), "git", append([]string{"--git-dir", r.gitDir}, args...)...)
		cmd.Dir = r.root
		cmd.Stdin = strings.NewReader(input)
		cmd.Env = append(cmd.Environ(), "GIT_INDEX_FILE="+filepath.Join(r.root, "index"), "GIT_AUTHOR_NAME=Test", "GIT_AUTHOR_EMAIL=test@example.invalid", "GIT_COMMITTER_NAME=Test", "GIT_COMMITTER_EMAIL=test@example.invalid")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("fixture git %v: %v: %s", args, err, out)
		}
		return strings.TrimSpace(string(out))
	}
	git("", "read-tree", "--empty")
	for name, data := range files {
		oid := git(data, "hash-object", "-w", "--stdin")
		git("", "update-index", "--add", "--cacheinfo", "100644,"+oid+","+name)
	}
	args := []string{"commit-tree", git("", "write-tree")}
	if parent != "" {
		args = append(args, "-p", parent)
	}
	return git("fixture\n", args...)
}

func note(t *testing.T, a assignment, outcome, retry string, refs ...evidence) string {
	t.Helper()
	data, err := json.Marshal(receipt{Key: a.Key, Revision: a.Revision, Outcome: outcome, Source: "Pinned PDF, p. 17, display 1", Finding: "A scoped finding with a checked source mismatch.", Retry: retry, Evidence: refs})
	if err != nil {
		t.Fatal(err)
	}
	return string(data)
}

func TestAcceptedRecoveryAndIndependentOutcomes(t *testing.T) {
	dir := t.TempDir()
	writeChapter(t, dir, "chapter-01", recordJSON("landed", "open"), recordJSON("invalid", "open"), recordJSON("covered", "established"), recordJSON("blocked", "open"))
	work := readAssignments(t, dir)
	r := newRepo(t)
	const existing = "Proofs/Props/Existing.lean"
	const added = "Proofs/Props/Part.lean"
	base := snapshot(t, r, "", map[string]string{existing: "def existing := True"})
	pending, err := r.selectBatch(t.Context(), base, work, len(work))
	if err != nil || len(pending) != 4 {
		t.Fatalf("original batch = %v, %v", len(pending), err)
	}
	b := batch{edition, r.target, base, pending}
	// Model an interruption after adoption
	// of a partial proof plus its receipt,
	// but before Go acknowledged anything.
	// The accepted ancestor is the evidence.
	files := map[string]string{
		existing:       "def existing := True",
		added:          "def part := True",
		work[0].path(): note(t, work[0], "landed", "need closed embedding", evidence{Path: added, Declarations: []string{"part"}}),
	}
	landed := snapshot(t, r, base, files)
	files[work[1].path()] = note(t, work[1], "operational_failure", "try when provider returns")
	files[work[2].path()] = note(t, work[2], "already_covered", "", evidence{Path: existing, Revision: base, Declarations: []string{"existing"}})
	files[work[3].path()] = note(t, work[3], "substantive_failure", "need a premise for the displayed implication")
	accepted := snapshot(t, r, landed, files)
	pending, err = r.selectBatch(t.Context(), accepted, work, len(work))
	if err != nil || len(pending) != 1 || pending[0].Key != work[1].Key {
		t.Fatalf("restart selected %+v, %v", pending, err)
	}
	if err := r.acknowledge(t.Context(), b, accepted); err == nil || !strings.Contains(err.Error(), work[1].path()) || strings.Contains(err.Error(), work[2].path()) {
		t.Fatalf("wrong unresolved assignments: %v", err)
	}
	files["unrelated.md"] = "target movement"
	moved := snapshot(t, r, accepted, files)
	pending, err = r.selectBatch(t.Context(), moved, []assignment{work[3]}, batchCap)
	if err != nil || len(pending) != 0 {
		t.Fatalf("unrelated movement retried substantive failure: %+v, %v", pending, err)
	}
	writeChapter(t, dir, "chapter-01", strings.Replace(recordJSON("blocked", "open"), "claims P", "claims P assuming Q", 1))
	revised := readAssignments(t, dir)
	pending, err = r.selectBatch(t.Context(), moved, revised, batchCap)
	if err != nil || len(pending) != 1 || pending[0].Key != work[3].Key || pending[0].Revision == work[3].Revision {
		t.Fatalf("meaningfully revised record not selected: %+v, %v", pending, err)
	}
}

func TestCoverageRequiresAcceptedRevision(t *testing.T) {
	dir := t.TempDir()
	writeChapter(t, dir, "chapter-01", recordJSON("claim", "open"))
	work := readAssignments(t, dir)
	a := work[0]
	r := newRepo(t)
	const proof = "Proofs/Props/P.lean"
	base := snapshot(t, r, "", nil)
	other := snapshot(t, r, base, map[string]string{proof: "def p := True"})
	tip := snapshot(t, r, base, map[string]string{
		proof:    "def unrelated := True",
		a.path(): note(t, a, "already_covered", "", evidence{Path: proof, Revision: other, Declarations: []string{"p"}}),
	})
	pending, err := r.selectBatch(t.Context(), tip, work, batchCap)
	if err != nil || len(pending) != 1 {
		t.Fatalf("unaccepted evidence suppressed work: %+v, %v", pending, err)
	}
	tip = snapshot(t, r, other, map[string]string{
		proof:    "def unrelated := True",
		a.path(): note(t, a, "already_covered", "", evidence{Path: proof, Revision: other, Declarations: []string{"p"}}),
	})
	pending, err = r.selectBatch(t.Context(), tip, work, batchCap)
	if err != nil || len(pending) != 1 {
		t.Fatalf("stale evidence suppressed work: %+v, %v", pending, err)
	}
}
