package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"strings"
	"testing"

	"patel.codes/godel"
)

var forwardOrder = []string{
	"chapter-01", "chapter-02", "chapter-03", "chapter-04", "chapter-05", "chapter-06", "chapter-07",
	"chapter-08", "chapter-09", "chapter-10", "chapter-11", "chapter-12", "chapter-13", "chapter-14",
	"appendix-a", "appendix-b", "appendix-c", "appendix-d", "appendix-e",
}

func TestStartNodeReadsLedgerAtTransition(t *testing.T) {
	base, err := filepath.EvalSymlinks(t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	checkout := filepath.Join(base, "checkout")
	source := filepath.Join(checkout, "cmd", "walk")
	if err := os.MkdirAll(source, 0700); err != nil {
		t.Fatal(err)
	}
	alias := filepath.Join(base, "checkout-link")
	if err := os.Symlink(checkout, alias); err != nil {
		t.Fatal(err)
	}
	home := filepath.Join(base, "home")
	root, ledgerDir, err := walkPaths(filepath.Join(alias, "cmd", "walk"), home)
	if err != nil {
		t.Fatal(err)
	}
	digest := sha256.Sum256([]byte(source))
	wantLedger := filepath.Join(home, ".grh-walk-"+hex.EncodeToString(digest[:]))
	if root != checkout || ledgerDir != wantLedger {
		t.Fatalf("paths = (%q, %q); want (%q, %q)", root, ledgerDir, checkout, wantLedger)
	}

	first := openRecord("prop", "1.1", 2)
	c := chapterState{Edition: edition, Chapter: "chapter-01", Cursor: &first.Passage, Records: []record{first}}
	if err := writeChapter(wantLedger, c); err != nil {
		t.Fatal(err)
	}
	info, err := os.Stat(wantLedger)
	if err != nil {
		t.Fatal(err)
	}
	if info.Mode().Perm()&0077 != 0 {
		t.Fatalf("new ledger is not private: mode %04o", info.Mode().Perm())
	}
	start := startNode(root, ledgerDir)
	// A prior writer completes the chapter
	// before Gödel reaches Next.
	c.Complete = true
	if err := writeChapter(wantLedger, c); err != nil {
		t.Fatal(err)
	}
	node, err := start.Next(godel.Result{Text: `{"chapter":"chapter-01","cursor":null}`})
	if err != nil {
		t.Fatal(err)
	}
	w := &walkTest{t: t, dir: wantLedger, launchRoot: checkout, node: node}
	w.want("chapter-02", nil, nil)
	prompt, _ := w.reviewPrompt()
	if !strings.Contains(prompt, ".godel/walk/README.md") || !strings.Contains(prompt, "cmd/walk/store.go") ||
		strings.Contains(prompt, "../../cmd/walk/store.go") {
		t.Fatalf("reviewer did not get repository paths for schema: %q", prompt)
	}
}

func TestForwardOrderAndCoverage(t *testing.T) {
	w := startWalk(t)
	if _, err := os.Stat(w.dir); !os.IsNotExist(err) {
		t.Fatalf("opening a new walk created ledger state: %v", err)
	}
	prop := openRecord("prop", "1.1", 2)
	eq := openRecord("eq", "1.1", 2)
	eq.Printed = "fixture heading only"
	eq.Formal = formalFinding{Status: "not_applicable"}
	eq.References = []reference{{Kind: "audit", Target: "fixture-audit.md", Revision: "audit-1"}}
	w.want("chapter-01", nil, nil)
	w.accept(&prop, false)
	w.reopen()
	w.want("chapter-01", &prop.Passage, nil)
	w.accept(&eq, false)
	w.reopen()
	w.want("chapter-01", &eq.Passage, nil)
	w.accept(nil, true)
	for _, id := range forwardOrder[1:] {
		w.want(id, nil, nil)
		w.accept(nil, true)
	}
	w.done()
	w.reopen()
	w.done()
	c := w.chapter("chapter-01")
	if !c.Complete || c.Cursor == nil || *c.Cursor != eq.Passage || !reflect.DeepEqual(c.Records, []record{prop, eq}) {
		t.Fatalf("wrong reopened records or coverage: %+v", c)
	}
	entries, err := os.ReadDir(w.dir)
	if err != nil {
		t.Fatal(err)
	}
	var names, want []string
	for _, entry := range entries {
		names = append(names, entry.Name())
	}
	for _, id := range forwardOrder {
		want = append(want, id+".json")
	}
	slices.Sort(want)
	if !slices.Equal(names, want) {
		t.Fatalf("ledger files = %v, want %v", names, want)
	}
}

func TestEvidenceReplayAfterReopen(t *testing.T) {
	w := startWalk(t)
	use := openRecord("prop", "1.1", 2)
	tail := openRecord("eq", "1.1", 2)
	wrong := openRecord("eq", "2.1", 3)
	source := openRecord("prop", "2.1", 3)
	later := []record{openRecord("prop", "3.1", 4), openRecord("prop", "4.1", 5), openRecord("prop", "5.1", 6)}
	use.Dependencies = []dependency{requires("chapter-02", source, "full conclusion")}
	for i, r := range later {
		source.Dependencies = append(source.Dependencies, requires(forwardOrder[i+2], r, "premise"))
	}
	first := publish(&source, "full conclusion", "supports", "proof-1")
	publish(&wrong, "full conclusion", "supports", "wrong-kind")

	w.want("chapter-01", nil, nil)
	w.accept(&use, false)
	w.want("chapter-01", &use.Passage, nil)
	w.accept(&tail, true)
	before := w.file("chapter-01")
	w.want("chapter-02", nil, nil)
	w.accept(&wrong, false)
	w.want("chapter-02", &wrong.Passage, nil) // The equation is not the required proposition.
	w.accept(&source, false)
	w.want("chapter-01", &tail.Passage, &use.Passage)
	if !bytes.Equal(before, w.file("chapter-01")) {
		t.Fatal("issuing a revisit wrote to its chapter before review")
	}

	// Drop the continuation, as if
	// interrupted after scheduling but
	// before review.
	w.reopen()
	req := w.want("chapter-01", &tail.Passage, &use.Passage)
	if len(req.Inputs) != 1 || !reflect.DeepEqual(req.Inputs[0], offeredEvidence{
		Requirement: use.Dependencies[0].Requirement,
		Current:     first,
	}) {
		t.Fatalf("reopened request has wrong evidence: %+v", req.Inputs)
	}
	if err := w.submit(&use, false); err == nil || !strings.Contains(err.Error(), "acknowledge") {
		t.Fatalf("review without receipt: got %v, want acknowledgment error", err)
	}
	w.done()
	if !bytes.Equal(before, w.file("chapter-01")) {
		t.Fatal("unsuccessful revisit changed the chapter")
	}
	w.reopen()
	w.want("chapter-01", &tail.Passage, &use.Passage)
	w.retryMalformed()
	use.Dependencies[0].Reviewed = first
	w.accept(&use, false)
	w.reopen()
	w.want("chapter-02", &source.Passage, nil) // A completed receipt survives reopening.
	w.accept(nil, true)

	// Revisit the source three times. An
	// unrelated change does not affect the
	// use, but contradiction and withdrawal
	// each require a fresh review.
	for i, r := range later {
		id := forwardOrder[i+2]
		w.want(id, nil, nil)
		source.Dependencies[i].Reviewed = publish(&r, "premise", "supports", id+"-proof")
		w.accept(&r, true)
		w.want("chapter-02", &source.Passage, &source.Passage)
		switch i {
		case 0:
			source.Printed = "fixture rewritten reading"
			publish(&source, "unrelated specialization", "supports", "other-proof")
		case 1:
			use.Dependencies[0].Reviewed = publish(&source, "full conclusion", "contradicts", "counterexample-1")
		case 2:
			source.Evidence = source.Evidence[1:]
			use.Dependencies[0].Reviewed = nil
		}
		w.accept(&source, false)
		if i > 0 {
			req := w.want("chapter-01", &tail.Passage, &use.Passage)
			if len(req.Inputs) != 1 || !reflect.DeepEqual(req.Inputs[0].Current, use.Dependencies[0].Reviewed) {
				t.Fatalf("changed input not offered: %+v", req.Inputs)
			}
			w.accept(&use, false)
		}
		w.want(forwardOrder[i+3], nil, nil)
	}
	w.reopen()
	w.want("chapter-06", nil, nil)
	c := w.chapter("chapter-01")
	if !c.Complete || c.Cursor == nil || *c.Cursor != tail.Passage || !reflect.DeepEqual(c.Records, []record{use, tail}) {
		t.Fatalf("revisits rewound coverage or changed the still-open finding: %+v", c)
	}
}

func TestCitationCycleDefersWithoutConsumingReview(t *testing.T) {
	w := startWalk(t)
	x := openRecord("prop", "1.1", 2)
	y := openRecord("prop", "1.2", 3)
	seed := openRecord("prop", "E.1", 30)
	x.Dependencies = []dependency{requires("chapter-01", y, "Y"), requires("appendix-e", seed, "seed")}
	y.Dependencies = []dependency{requires("chapter-01", x, "X")}
	w.want("chapter-01", nil, nil)
	w.accept(&x, false)
	w.want("chapter-01", &x.Passage, nil)
	w.accept(&y, true)
	w.reopen()
	// With no independent evidence, the circular citations
	// are not a trigger.
	for _, id := range forwardOrder[1 : len(forwardOrder)-1] {
		w.want(id, nil, nil)
		w.accept(nil, true)
	}
	w.want("appendix-e", nil, nil)
	x.Dependencies[1].Reviewed = publish(&seed, "seed", "supports", "seed-proof")
	w.accept(&seed, true)
	w.want("chapter-01", &y.Passage, &x.Passage)
	y.Dependencies[0].Reviewed = publish(&x, "X", "supports", "x-proof")
	w.accept(&x, false)
	w.want("chapter-01", &y.Passage, &y.Passage)
	x.Dependencies[0].Reviewed = publish(&y, "Y", "supports", "y-proof")
	if err := w.submit(&y, false); err == nil || !strings.Contains(err.Error(), "awaits review") {
		t.Fatalf("cycle with pending evidence: got %v, want deferred review", err)
	}
	w.reopen()
	w.want("chapter-01", &y.Passage, &x.Passage)
	w.accept(&x, false)
	w.done()
	w.reopen()
	w.done()
}

func TestMalformedReviewRetry(t *testing.T) {
	w := startWalk(t)
	w.want("chapter-01", nil, nil)
	w.retryMalformed()
	r := openRecord("prop", "1.1", 2)
	w.accept(&r, false)
	w.want("chapter-01", &r.Passage, nil)
	if c := w.chapter("chapter-01"); c.Complete || !reflect.DeepEqual(c.Cursor, &r.Passage) || !reflect.DeepEqual(c.Records, []record{r}) {
		t.Fatalf("retry did not save exactly one open review: %+v", c)
	}

	// A new request in the same chapter gets
	// a retry of its own.
	w.retryMalformed()
	before := w.ledger()
	if err := w.submitText(`{"chapter":"chapter-01",`); err == nil || !strings.Contains(err.Error(), "unexpected end of JSON input") {
		t.Fatalf("second malformed response: got %v, want a syntax error", err)
	}
	w.done()
	if !reflect.DeepEqual(w.ledger(), before) {
		t.Fatal("second syntax failure changed the ledger")
	}
	w.reopen()
	w.want("chapter-01", &r.Passage, nil)
}

func TestInvalidReviewDoesNotRetry(t *testing.T) {
	for _, tc := range []struct{ name, text, diagnostic string }{
		{"chapter", `{"chapter":"chapter-02","complete":true}`, "unexpected chapter"},
		{"type", `{"chapter":"chapter-01","complete":"true"}`, "cannot unmarshal"},
		{"null", `null`, "unexpected chapter"},
		{"misspelled final record", `{"chapter":"chapter-01","complete":true,"recrod":{"printed_finding":"last passage"}}`, `unknown field "recrod"`},
		{"unknown nested field", `{"chapter":"chapter-01","record":{"formal":{"evidnce":"claim"}}}`, `unknown field "evidnce"`},
		{"missing disposition", `{"chapter":"chapter-01"}`, "must supply a passage or complete"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			w := startWalk(t)
			if !json.Valid([]byte(tc.text)) {
				t.Fatal("fixture must have valid JSON syntax")
			}
			if err := w.submitText(tc.text); err == nil || !strings.Contains(err.Error(), tc.diagnostic) {
				t.Fatalf("invalid response: got %v, want %q", err, tc.diagnostic)
			}
			w.done()
			if _, err := os.Stat(w.dir); !os.IsNotExist(err) {
				t.Fatalf("invalid response created ledger state: %v", err)
			}
		})
	}
}

func TestFailedPublicationDoesNotAdvance(t *testing.T) {
	w := startWalk(t)
	w.want("chapter-01", nil, nil)
	blocked := filepath.Join(w.dir, "chapter-01.json")
	if err := os.MkdirAll(blocked, 0755); err != nil {
		t.Fatal(err)
	}
	r := openRecord("prop", "1.1", 2)
	if err := w.submit(&r, true); err == nil {
		t.Fatal("expected rename to fail")
	}
	if err := os.Remove(blocked); err != nil {
		t.Fatal(err)
	}
	w.reopen()
	w.want("chapter-01", nil, nil)
	w.accept(&r, true)
	w.want("chapter-02", nil, nil)
}

func openRecord(kind, locator string, page int) record {
	return record{Passage: passage{kind, locator, page}, Printed: "fixture reading", Formal: formalFinding{Status: "open"}}
}

func requires(chapter string, source record, conclusion string) dependency {
	return dependency{Requirement: requirement{
		Source:     passageRef{Chapter: chapter, Passage: source.Passage},
		Conclusion: conclusion,
	}}
}

func publish(r *record, conclusion, verdict, version string) *evidence {
	e := evidence{Verdict: verdict, Reference: reference{"lean", "Fixture.example", version}}
	for i, old := range r.Evidence {
		if old.Conclusion == conclusion {
			r.Evidence[i].Evidence = e
			return &e
		}
	}
	r.Evidence = append(r.Evidence, conclusionEvidence{conclusion, e})
	return &e
}

type walkTest struct {
	t          *testing.T
	dir        string
	launchRoot string
	node       *godel.Node
}

func startWalk(t *testing.T) *walkTest {
	root := t.TempDir()
	w := &walkTest{t: t, dir: filepath.Join(root, "home", ".grh-walk-fixture"), launchRoot: filepath.Join(root, "checkout")}
	w.reopen()
	return w
}

// Rebuild all process state from the
// canonical chapter files.
func (w *walkTest) reopen() {
	w.t.Helper()
	var err error
	w.node, err = startNode(w.launchRoot, w.dir).Next(godel.Result{})
	if err != nil {
		w.t.Fatal(err)
	}
}

func (w *walkTest) reviewPrompt() (prompt, requestJSON string) {
	w.t.Helper()
	if w.node == nil || w.node.Exec != "yah" || w.node.Directory != w.launchRoot || w.node.Next == nil ||
		len(w.node.Args) != 5 || !slices.Equal(w.node.Args[:4], []string{"-yolo", "-effort", "high", "-append"}) {
		w.t.Fatalf("expected a Yah reviewer node at %s, got %+v", w.launchRoot, w.node)
	}
	prompt, requestJSON, ok := strings.Cut(w.node.Args[4], "\n\nRequest (data): ")
	if !ok || !strings.Contains(prompt, w.dir) {
		w.t.Fatalf("reviewer prompt missing request or ledger location: %q", w.node.Args[4])
	}
	return prompt, requestJSON
}

func (w *walkTest) retryMalformed() {
	w.t.Helper()
	before := w.ledger()
	_, original := w.reviewPrompt()
	if err := w.submitText(`{"chapter":"chapter-01","complete":true} trailing prose`); err != nil {
		w.t.Fatalf("first malformed response: %v", err)
	}
	prompt, retried := w.reviewPrompt()
	if retried != original || !strings.Contains(prompt, "previous response was not valid JSON") {
		w.t.Fatalf("retry changed the request or omitted the diagnostic: %s -> %s", original, retried)
	}
	if !reflect.DeepEqual(w.ledger(), before) {
		w.t.Fatal("first syntax failure changed the ledger")
	}
}

func (w *walkTest) request() request {
	w.t.Helper()
	_, requestJSON := w.reviewPrompt()
	var req request
	if err := json.Unmarshal([]byte(requestJSON), &req); err != nil {
		w.t.Fatal(err)
	}
	return req
}

func (w *walkTest) want(chapter string, cursor, revisit *passage) request {
	w.t.Helper()
	req := w.request()
	var gotRevisit *passage
	if req.Revisit != nil {
		gotRevisit = &req.Revisit.Passage
	}
	if req.Chapter != chapter || !reflect.DeepEqual(req.Cursor, cursor) || !reflect.DeepEqual(gotRevisit, revisit) {
		w.t.Fatalf("request = chapter %s cursor %+v revisit %+v; want chapter %s cursor %+v revisit %+v",
			req.Chapter, req.Cursor, gotRevisit, chapter, cursor, revisit)
	}
	return req
}

func (w *walkTest) submit(r *record, complete bool) error {
	w.t.Helper()
	// Exercise the actual stdout-to-Next transition without invoking the runner.
	data, err := json.Marshal(review{Chapter: w.request().Chapter, Record: r, Complete: complete})
	if err != nil {
		w.t.Fatal(err)
	}
	return w.submitText(string(data))
}

func (w *walkTest) submitText(text string) error {
	w.t.Helper()
	node, err := w.node.Next(godel.Result{Text: text})
	w.node = node
	return err
}

func (w *walkTest) accept(r *record, complete bool) {
	w.t.Helper()
	if err := w.submit(r, complete); err != nil {
		w.t.Fatal(err)
	}
}

func (w *walkTest) done() {
	w.t.Helper()
	if w.node != nil {
		w.t.Fatalf("expected no remaining review, got %s", w.node.Args)
	}
}

func (w *walkTest) file(id string) []byte {
	w.t.Helper()
	data, err := os.ReadFile(filepath.Join(w.dir, id+".json"))
	if err != nil {
		w.t.Fatal(err)
	}
	return data
}

func (w *walkTest) ledger() map[string]string {
	w.t.Helper()
	entries, err := os.ReadDir(w.dir)
	if os.IsNotExist(err) {
		return nil
	}
	if err != nil {
		w.t.Fatal(err)
	}
	files := make(map[string]string, len(entries))
	for _, entry := range entries {
		data, err := os.ReadFile(filepath.Join(w.dir, entry.Name()))
		if err != nil {
			w.t.Fatal(err)
		}
		files[entry.Name()] = string(data)
	}
	return files
}

func (w *walkTest) chapter(id string) chapterState {
	w.t.Helper()
	var c chapterState
	if err := json.Unmarshal(w.file(id), &c); err != nil {
		w.t.Fatal(err)
	}
	return c
}
