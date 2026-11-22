package main

import (
	"bytes"
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
	if !bytes.Equal(before, w.file("chapter-01")) {
		t.Fatal("unsuccessful revisit changed the chapter")
	}
	w.reopen()
	w.want("chapter-01", &tail.Passage, &use.Passage)
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
	t    *testing.T
	dir  string
	node *godel.Node
}

func startWalk(t *testing.T) *walkTest {
	w := &walkTest{t: t, dir: filepath.Join(t.TempDir(), "walk")}
	w.reopen()
	return w
}

// Rebuild all process state from the
// canonical chapter files.
func (w *walkTest) reopen() {
	w.t.Helper()
	t, err := openTraversal(w.dir)
	if err != nil {
		w.t.Fatal(err)
	}
	w.node, err = t.nextNode(godel.Node{Exec: "test-reviewer"})
	if err != nil {
		w.t.Fatal(err)
	}
}

func (w *walkTest) request() request {
	w.t.Helper()
	if w.node == nil || w.node.Exec != "test-reviewer" || len(w.node.Args) != 1 || w.node.Next == nil {
		w.t.Fatalf("expected a reviewer node, got %+v", w.node)
	}
	var req request
	if err := json.Unmarshal([]byte(w.node.Args[0]), &req); err != nil {
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
	w.node, err = w.node.Next(godel.Result{Text: string(data)})
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

func (w *walkTest) chapter(id string) chapterState {
	w.t.Helper()
	var c chapterState
	if err := json.Unmarshal(w.file(id), &c); err != nil {
		w.t.Fatal(err)
	}
	return c
}
