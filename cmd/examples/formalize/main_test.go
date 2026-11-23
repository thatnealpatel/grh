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

func TestOrderAndLookahead(t *testing.T) {
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
	expectPlan(t, r, base, work, work[0], work[1], work[2], statementOf(work[3]))
}

func TestLookaheadReservesFreshProofs(t *testing.T) {
	ledger := t.TempDir()
	var records []string
	for i := range 2 * (offerCap + 1) {
		records = append(records, recordJSON(fmt.Sprintf("passage %d", i), "open"))
	}
	writeChapter(t, ledger, "chapter-01", records...)
	work := readAssignments(t, ledger)
	// Enough older partial proofs to fill the entire
	// window with statements if we simply took the
	// first eligible entries in Walk order.
	older, fresh := work[:offerCap+1], work[offerCap+1:]
	r := newRepo(t)
	const artifact = "Proofs/Theorems/Partial.lean"
	base := snapshot(t, r, "", nil)
	files := map[string]string{artifact: "theorem part : True := trivial\n"}
	for _, a := range older {
		files[a.path()] = note(t, a, "landed", "need the opposite implication", evidence{Path: artifact, Declarations: []string{"part"}})
	}
	tip := snapshot(t, r, base, files)
	expectPlan(t, r, tip, work, fresh[0], fresh[1], fresh[2], statementOf(older[0]))
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
		}, dir, &request)
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

// dispatch exercises the gate and its coordinator callback without running the
// coordinator process. The injected tip stands in for adoption.
func dispatch(t *testing.T, ctx context.Context, r repository, tip *string, ledger, prior string) (*godel.Node, string, batch) {
	t.Helper()
	var dir string
	gate := startNode(ctx, r, func(context.Context) (string, error) { return *tip, nil }, ledger, &dir)
	n, err := gate.Next(godel.Result{Text: prior})
	if err != nil || n == nil {
		t.Fatalf("dispatch = %+v, %v", n, err)
	}
	path := dir
	t.Cleanup(func() { os.RemoveAll(path) })
	request := filepath.Join(dir, "request.json")
	data, err := os.ReadFile(request)
	if err != nil {
		t.Fatal(err)
	}
	var b batch
	if err := json.Unmarshal(data, &b); err != nil {
		t.Fatal(err)
	}
	return n, dir, b
}

func bind(t *testing.T, dir string, selected ...assignment) {
	t.Helper()
	var paths []string
	for _, a := range selected {
		paths = append(paths, a.path())
	}
	data, err := json.Marshal(paths)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, selectionFile), data, 0600); err != nil {
		t.Fatal(err)
	}
}

func TestDispatchAndOperationalStop(t *testing.T) {
	t.Setenv("TMPDIR", t.TempDir())
	ledger := t.TempDir()
	writeChapter(t, ledger, "chapter-01", recordJSON("first", "open"))
	a := readAssignments(t, ledger)[0]
	r := newRepo(t)
	base := snapshot(t, r, "", nil)
	head := base
	const prior = "untrusted stale stdin"
	n, dir, b := dispatch(t, t.Context(), r, &head, ledger, prior)
	request := filepath.Join(dir, "request.json")
	args := strings.Join(n.Args, " ")
	if n.Directory != r.root || !strings.Contains(args, request) || !strings.Contains(args, filepath.Join(dir, selectionFile)) || strings.Contains(args, prior) {
		t.Fatalf("wrong coordinator inputs: %+v", n)
	}
	for path, mode := range map[string]os.FileMode{dir: 0700, request: 0600} {
		info, err := os.Stat(path)
		if err != nil || info.Mode().Perm() != mode {
			t.Fatalf("dispatch path not private: %v, %v", info, err)
		}
	}
	if b.Edition != edition || b.AcceptedTip != base || b.Target != r.target || b.Primary.path() != a.path() || len(b.Offers) != 0 {
		t.Fatalf("wrong request: %+v", b)
	}
	bind(t, dir, a)
	if next, err := n.Next(godel.Result{Text: "I landed everything"}); next != nil || err == nil || !strings.Contains(err.Error(), "no accepted receipt") {
		t.Fatalf("claim without accepted disposition = %+v, %v", next, err)
	}
	if _, err := os.Stat(dir); !errors.Is(err, os.ErrNotExist) {
		t.Fatalf("dispatch files left behind: %v", err)
	}
	n, dir, b = dispatch(t, t.Context(), r, &head, ledger, "another old receipt")
	bind(t, dir, b.Primary)
	head = snapshot(t, r, base, map[string]string{
		a.path(): note(t, a, "substantive_failure", "Reconsider if premise Q is justified"),
	})
	if next, err := n.Next(godel.Result{Text: "unstructured handoff"}); next != nil || err != nil {
		t.Fatalf("accepted outcome did not enable continuation: %+v, %v", next, err)
	}
	n, dir, b = dispatch(t, t.Context(), r, &head, ledger, "old proof handoff")
	statement := statementOf(a)
	if b.Primary.path() != statement.path() || len(b.Offers) != 0 {
		t.Fatalf("wrong statement request: %+v", b)
	}
	bind(t, dir, statement)
	if next, err := n.Next(godel.Result{Text: "old proof outcome"}); next != nil || err == nil || !strings.Contains(err.Error(), statement.path()+": no accepted receipt") {
		t.Fatalf("proof receipt acknowledged a statement request: %+v, %v", next, err)
	}
}

func TestBoundOptionalLane(t *testing.T) {
	t.Setenv("TMPDIR", t.TempDir())
	ledger := t.TempDir()
	writeChapter(t, ledger, "chapter-01", recordJSON("statement", "open"), recordJSON("primary", "open"), recordJSON("other proof", "open"))
	work := readAssignments(t, ledger)
	proof, statement := work[1], statementOf(work[0])
	r := newRepo(t)
	files := map[string]string{work[0].path(): note(t, work[0], "substantive_failure", "need a missing hypothesis")}
	base := snapshot(t, r, "", files)
	// The primary receipt and proof land together.
	// The other proof offer has no receipt in any
	// of these cases.
	const artifact = "Proofs/Theorems/Primary.lean"
	files[artifact] = "theorem primary : True := trivial\n"
	files[proof.path()] = note(t, proof, "landed", "", evidence{Path: artifact, Declarations: []string{"primary"}})
	landed := snapshot(t, r, base, files)
	files[statement.path()] = note(t, statement, "statement_blocked", "need the real quotient definition")
	both := snapshot(t, r, landed, files)
	for _, tc := range []struct {
		name     string
		selected []assignment
		tip      string
		wantErr  string
	}{
		{"unbound despite accepted receipts", nil, both, "read formalize selection"},
		{"declined", []assignment{proof}, landed, ""},
		{"selected missing", []assignment{proof, statement}, landed, statement.path() + ": no accepted receipt"},
		{"both accepted", []assignment{proof, statement}, both, ""},
	} {
		t.Run(tc.name, func(t *testing.T) {
			head := base
			n, dir, b := dispatch(t, t.Context(), r, &head, ledger, "")
			if b.Primary.path() != proof.path() || len(b.Offers) != 2 || b.Offers[0].path() != work[2].path() || b.Offers[1].path() != statement.path() {
				t.Fatalf("wrong proof priority or offers: %+v", b)
			}
			if tc.selected != nil {
				bind(t, dir, tc.selected...)
			}
			head = tc.tip
			// Outcome-dependent stdout cannot change the predispatch selection.
			next, err := n.Next(godel.Result{Text: "No optional lane selected."})
			if next != nil || (tc.wantErr == "" && err != nil) || (tc.wantErr != "" && (err == nil || !strings.Contains(err.Error(), tc.wantErr))) {
				t.Fatalf("acknowledgment = %+v, %v; want error %q", next, err, tc.wantErr)
			}
			if err != nil && (strings.Contains(err.Error(), proof.path()) || strings.Contains(err.Error(), work[2].path())) {
				t.Fatalf("reported an accepted or unselected proof as unresolved: %v", err)
			}
		})
	}
}

func TestInvalidSelection(t *testing.T) {
	ledger := t.TempDir()
	writeChapter(t, ledger, "chapter-01", recordJSON("primary", "open"), recordJSON("offer", "open"), recordJSON("another offer", "open"), recordJSON("foreign", "open"))
	work := readAssignments(t, ledger)
	b := batch{Primary: work[0], Offers: []assignment{work[1], work[2], statementOf(work[0])}}
	for _, tc := range []struct {
		name     string
		selected []assignment
	}{
		{"omitted primary", []assignment{work[1]}},
		{"foreign", []assignment{work[0], work[3]}},
		{"wrong lane", []assignment{work[0], statementOf(work[1])}},
		{"duplicate", []assignment{work[0], work[0]}},
		{"same passage different lane", []assignment{work[0], statementOf(work[0])}},
		{"over cap", []assignment{work[0], work[1], work[2]}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			bind(t, dir, tc.selected...)
			if got, err := b.readSelection(filepath.Join(dir, selectionFile)); err == nil || got != nil {
				t.Fatalf("invalid selection accepted: %+v, %v", got, err)
			}
		})
	}
	t.Run("truncated", func(t *testing.T) {
		file := filepath.Join(t.TempDir(), selectionFile)
		if err := os.WriteFile(file, []byte(fmt.Sprintf(`[%q,`, b.Primary.path())), 0600); err != nil {
			t.Fatal(err)
		}
		if got, err := b.readSelection(file); err == nil || got != nil {
			t.Fatalf("truncated selection accepted: %+v, %v", got, err)
		}
	})
}

func TestInterruptionRetainsAcceptedOptionalLane(t *testing.T) {
	t.Setenv("TMPDIR", t.TempDir())
	ledger := t.TempDir()
	writeChapter(t, ledger, "chapter-01", recordJSON("statement", "open"), recordJSON("primary", "open"))
	work := readAssignments(t, ledger)
	statement := statementOf(work[0])
	r := newRepo(t)
	files := map[string]string{work[0].path(): note(t, work[0], "substantive_failure", "need a missing hypothesis")}
	head := snapshot(t, r, "", files)
	ctx, cancel := context.WithCancel(t.Context())
	defer cancel()
	_, oldDir, b := dispatch(t, ctx, r, &head, ledger, "")
	if b.Primary.path() != work[1].path() || len(b.Offers) != 1 || b.Offers[0].path() != statement.path() {
		t.Fatalf("wrong initial dispatch: %+v", b)
	}
	bind(t, oldDir, b.Primary, statement)

	// Establish acceptance before interrupting,
	// not merely a writer output. As on a
	// canceled coordinator invocation, its Next
	// is never called.
	const artifact = "Proofs/Props/Statement.lean"
	files[artifact] = "def claim : Prop := True\n"
	files[statement.path()] = note(t, statement, "statement_checked", "", evidence{Path: artifact, Declarations: []string{"claim"}})
	head = snapshot(t, r, head, files)
	notes, err := r.receiptTree(ctx, head)
	if err != nil {
		t.Fatal(err)
	}
	if d, problem, err := r.disposition(ctx, head, notes, statement); err != nil || d.Outcome != "statement_checked" {
		t.Fatalf("statement not accepted before interruption: %+v, %s, %v", d, problem, err)
	}
	cancel()

	// Model a restart even if interruption left the ephemeral files behind.
	_, dir, restarted := dispatch(t, t.Context(), r, &head, ledger, `untrusted interrupted result`)
	if dir == oldDir || restarted.AcceptedTip != head || restarted.Primary.path() != b.Primary.path() || len(restarted.Offers) != 0 {
		t.Fatalf("restart did not retain just the accepted disposition: %+v", restarted)
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
	pending, err := r.planBatch(t.Context(), base, work)
	if err != nil || len(pending) != 4 {
		t.Fatalf("original batch = %v, %v", len(pending), err)
	}
	selected := pending[:2]
	// The original landing remains evidence
	// after the target moves.
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
	expectPlan(t, r, accepted, work, work[1], statementOf(work[0]), statementOf(work[3]))
	if err := r.acknowledge(t.Context(), selected, accepted); err == nil || !strings.Contains(err.Error(), work[1].path()) || strings.Contains(err.Error(), work[0].path()) {
		t.Fatalf("wrong unresolved assignments: %v", err)
	}
	blocked := statementOf(work[3])
	expectPlan(t, r, accepted, work[3:], blocked)
	files[blocked.path()] = note(t, blocked, "statement_blocked", "need the real source definition of the operator")
	files["unrelated.md"] = "target movement"
	moved := snapshot(t, r, accepted, files)
	expectPlan(t, r, moved, work[3:])
	writeChapter(t, dir, "chapter-01", strings.Replace(recordJSON("blocked", "open"), "claims P", "claims P assuming Q", 1))
	revised := readAssignments(t, dir)
	pending, err = r.planBatch(t.Context(), moved, revised)
	if err != nil || len(pending) != 1 || pending[0].Key != work[3].Key || pending[0].Revision == work[3].Revision || pending[0].Lane != proofLane {
		t.Fatalf("meaningfully revised record not selected: %+v, %v", pending, err)
	}
	files[revised[0].path()] = note(t, revised[0], "substantive_failure", "need a proof of the revised claim")
	expectPlan(t, r, snapshot(t, r, moved, files), revised, statementOf(revised[0]))
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
	pending, err := r.planBatch(t.Context(), tip, work)
	if err != nil || len(pending) != 1 {
		t.Fatalf("unaccepted evidence suppressed work: %+v, %v", pending, err)
	}
	tip = snapshot(t, r, other, map[string]string{
		proof:    "def unrelated := True",
		a.path(): note(t, a, "already_covered", "", evidence{Path: proof, Revision: other, Declarations: []string{"p"}}),
	})
	pending, err = r.planBatch(t.Context(), tip, work)
	if err != nil || len(pending) != 1 {
		t.Fatalf("stale evidence suppressed work: %+v, %v", pending, err)
	}
}
func statementOf(a assignment) assignment {
	a.Lane = statementLane
	return a
}

func expectPlan(t *testing.T, r repository, tip string, work []assignment, want ...assignment) {
	t.Helper()
	got, err := r.planBatch(t.Context(), tip, work)
	if err != nil || len(got) != len(want) {
		t.Fatalf("batch = %+v, %v; want %+v", got, err, want)
	}
	for i, a := range want {
		if got[i].Key != a.Key || got[i].Revision != a.Revision || got[i].Lane != a.Lane {
			t.Fatalf("batch = %+v; want %+v", got, want)
		}
	}
}

func TestWrongLaneOutcomes(t *testing.T) {
	dir := t.TempDir()
	writeChapter(t, dir, "chapter-01", recordJSON("claim", "open"))
	work := readAssignments(t, dir)
	proof, statement := work[0], statementOf(work[0])
	r := newRepo(t)
	failure := note(t, proof, "substantive_failure", "need a proof of the displayed implication")
	blocked := note(t, statement, "statement_blocked", "need the exact source quotient definition")
	for _, tc := range []struct {
		want  assignment
		files map[string]string
	}{
		{proof, map[string]string{proof.path(): blocked, statement.path(): blocked}},
		{statement, map[string]string{proof.path(): failure, statement.path(): failure}},
	} {
		t.Run(string(tc.want.Lane), func(t *testing.T) {
			tip := snapshot(t, r, "", tc.files)
			expectPlan(t, r, tip, work, tc.want)
			if err := r.acknowledge(t.Context(), []assignment{tc.want}, tip); err == nil || !strings.Contains(err.Error(), "invalid outcome for assignment lane") {
				t.Fatalf("wrong-lane outcome = %v", err)
			}
		})
	}
}

func TestStatementFallbackAndProofRemainder(t *testing.T) {
	dir := t.TempDir()
	writeChapter(t, dir, "chapter-01", recordJSON("landed", "open"), recordJSON("covered", "open"), recordJSON("partial", "open"), recordJSON("failed", "open"), recordJSON("pending", "open"))
	work := readAssignments(t, dir)
	landed, covered, partial, failed, pending := work[0], work[1], work[2], work[3], work[4]
	r := newRepo(t)
	const existing = "Proofs/Theorems/Existing.lean"
	const added = "Proofs/Theorems/Added.lean"
	const retry = "need a closed embedding for the opposite implication"
	files := map[string]string{existing: "theorem existing : True := trivial\n"}
	base := snapshot(t, r, "", files)
	files[added] = "theorem full : True := trivial\ntheorem part : True := trivial\n"
	files[landed.path()] = note(t, landed, "landed", "", evidence{Path: added, Declarations: []string{"full"}})
	files[covered.path()] = note(t, covered, "already_covered", "", evidence{Path: existing, Revision: base, Declarations: []string{"existing"}})
	files[partial.path()] = note(t, partial, "landed", retry, evidence{Path: added, Declarations: []string{"part"}})
	files[failed.path()] = note(t, failed, "substantive_failure", "need a missing hypothesis of the printed implication")
	tip := snapshot(t, r, base, files)
	expectPlan(t, r, tip, work, pending, statementOf(partial), statementOf(failed))
	files[pending.path()] = note(t, pending, "already_covered", "", evidence{Path: existing, Revision: base, Declarations: []string{"existing"}})
	tip = snapshot(t, r, tip, files)
	p, f := statementOf(partial), statementOf(failed)
	expectPlan(t, r, tip, work, p, f)
	// A blocker without a retry condition is not a
	// disposition.
	files[p.path()] = note(t, p, "statement_blocked", "")
	tip = snapshot(t, r, tip, files)
	expectPlan(t, r, tip, work, p, f)
	files[p.path()] = note(t, p, "statement_blocked", "need the real quotient object from display 1")
	tip = snapshot(t, r, tip, files)
	expectPlan(t, r, tip, work, f)
	files[f.path()] = note(t, f, "statement_blocked", "need the real source operator on the printed test class")
	tip = snapshot(t, r, tip, files)
	if err := r.acknowledge(t.Context(), []assignment{f}, tip); err != nil {
		t.Fatal(err)
	}
	files["unrelated.md"] = "accepted movement"
	tip = snapshot(t, r, tip, files)
	expectPlan(t, r, tip, work)
	// The distinct statement receipt has not overwritten the
	// proof remainder.
	got, err := r.git(t.Context(), "show", tip+":"+partial.path())
	if err != nil || !strings.Contains(string(got), retry) || string(got) != files[partial.path()] {
		t.Fatalf("partial proof receipt = %s, %v", got, err)
	}
	// Retire only the obsolete proof
	// disposition once its retry condition
	// is met.
	delete(files, partial.path())
	tip = snapshot(t, r, tip, files)
	expectPlan(t, r, tip, work, partial)
}

func TestCheckedStatementExactEvidence(t *testing.T) {
	dir := t.TempDir()
	writeChapter(t, dir, "chapter-01", recordJSON("claim", "open"))
	work := readAssignments(t, dir)
	proof, statement := work[0], statementOf(work[0])
	r := newRepo(t)
	selected := []assignment{statement}
	const artifact = "Proofs/Props/Statement.lean"
	const original = "namespace Fixture\ndef Claim (n : Nat) : Prop := 0 ≤ n\nend Fixture\n"
	ref := evidence{Path: artifact, Declarations: []string{"Fixture.Claim"}}
	files := map[string]string{proof.path(): note(t, proof, "substantive_failure", "need a proof of the claimed bound"), artifact: original}
	base := snapshot(t, r, "", files)

	files[statement.path()] = note(t, statement, "statement_checked", "", ref)
	tip := snapshot(t, r, base, files)
	// With no explicit revision, the
	// defining file must change in the
	// receipt candidate.
	expectPlan(t, r, tip, work, statement)
	ref.Revision = base
	files[statement.path()] = note(t, statement, "statement_checked", "", ref)
	tip = snapshot(t, r, tip, files)
	if err := r.acknowledge(t.Context(), selected, tip); err != nil {
		t.Fatal(err)
	}
	expectPlan(t, r, tip, work)

	// A new definition and receipt can instead land together.
	files[artifact] = strings.Replace(original, "0 ≤ n", "0 ≤ n + 1", 1)
	ref.Revision = ""
	files[statement.path()] = note(t, statement, "statement_checked", "", ref)
	tip = snapshot(t, r, tip, files)
	files["Proofs/Lemmas/Unrelated.lean"] = "theorem unrelated : True := trivial\n"
	tip = snapshot(t, r, tip, files)
	if err := r.acknowledge(t.Context(), selected, tip); err != nil {
		t.Fatal(err)
	}
	expectPlan(t, r, tip, work)

	// A valid statement receipt is still
	// present if the proof is retried.
	delete(files, proof.path())
	expectPlan(t, r, snapshot(t, r, tip, files), work, proof)
	files[proof.path()] = note(t, proof, "substantive_failure", "need a proof of the claimed bound")

	files[artifact] = original
	tip = snapshot(t, r, tip, files)
	if err := r.acknowledge(t.Context(), selected, tip); err == nil || !strings.Contains(err.Error(), "cited Lean file changed") {
		t.Fatalf("changed defining file acknowledged: %v", err)
	}
	expectPlan(t, r, tip, work, statement)
}
