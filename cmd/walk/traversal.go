package main

import (
	"encoding/json"
	"fmt"
	"slices"

	"patel.codes/godel"
)

type traversal struct {
	dir       string
	chapters  [len(manuscriptOrder)]chapterState
	revisited map[passageRef]bool
}

type offeredEvidence struct {
	Requirement requirement `json:"requirement"`
	Current     *evidence   `json:"current"`
}

type request struct {
	Edition string            `json:"edition"`
	Chapter string            `json:"chapter"`
	Cursor  *passage          `json:"cursor"`
	Revisit *record           `json:"revisit,omitempty"`
	Inputs  []offeredEvidence `json:"inputs,omitempty"`
}

type review struct {
	Chapter  string  `json:"chapter"`
	Record   *record `json:"record,omitempty"`
	Complete bool    `json:"complete,omitempty"`
}

func openTraversal(dir string) (*traversal, error) {
	t := &traversal{dir: dir, revisited: make(map[passageRef]bool)}
	incomplete := ""
	for i, id := range manuscriptOrder {
		c, err := readChapter(dir, id)
		if err != nil {
			return nil, err
		}
		if incomplete != "" && (c.Cursor != nil || c.Complete) {
			return nil, fmt.Errorf("%s has forward progress before %s completed", id, incomplete)
		}
		if incomplete == "" && !c.Complete {
			incomplete = id
		}
		t.chapters[i] = c
	}
	return t, nil
}

func (t *traversal) currentEvidence(q requirement) *evidence {
	i := slices.Index(manuscriptOrder[:], q.Source.Chapter)
	if i < 0 {
		return nil
	}
	for _, r := range t.chapters[i].Records {
		if r.Passage != q.Source.Passage {
			continue
		}
		for _, e := range r.Evidence {
			if e.Conclusion == q.Conclusion {
				return &e.Evidence
			}
		}
		break
	}
	return nil
}

func sameEvidence(a, b *evidence) bool {
	if a == nil || b == nil {
		return a == b
	}
	return *a == *b
}

func (t *traversal) nextNode(launchRoot string) (*godel.Node, error) {
	deferred := false
	for i, c := range t.chapters {
		for j, r := range c.Records {
			for _, d := range r.Dependencies {
				if sameEvidence(d.Reviewed, t.currentEvidence(d.Requirement)) {
					continue
				}
				// A cycle may change a use already revisited at
				// this forward checkpoint. Leave its receipt stale
				// and allow forward progress.
				if t.revisited[passageRef{c.Chapter, r.Passage}] {
					deferred = true
					break
				}
				return t.node(launchRoot, i, j)
			}
		}
	}
	for i, c := range t.chapters {
		if !c.Complete {
			return t.node(launchRoot, i, -1)
		}
	}
	if deferred {
		return nil, fmt.Errorf("forward coverage complete; changed evidence awaits review on reopen")
	}
	return nil, nil
}

func (t *traversal) node(launchRoot string, chapterIndex, recordIndex int) (*godel.Node, error) {
	c := &t.chapters[chapterIndex]
	req := request{Edition: edition, Chapter: c.Chapter, Cursor: c.Cursor}
	if recordIndex >= 0 {
		req.Revisit = &c.Records[recordIndex]
		for _, d := range req.Revisit.Dependencies {
			req.Inputs = append(req.Inputs, offeredEvidence{
				Requirement: d.Requirement,
				Current:     t.currentEvidence(d.Requirement),
			})
		}
	}
	arg, err := json.Marshal(req)
	if err != nil {
		return nil, err
	}
	// Both attempts use the same serialized request,
	// including the evidence offered on a revisit.
	// Only a published review reschedules.
	var attempt func(diagnostic string) *godel.Node
	attempt = func(diagnostic string) *godel.Node {
		node := passageReviewer(launchRoot, t.dir, string(arg), diagnostic)
		node.Next = func(result godel.Result) (*godel.Node, error) {
			var out review
			if err := json.Unmarshal([]byte(result.Text), &out); err != nil {
				if syntax, ok := err.(*json.SyntaxError); ok && diagnostic == "" {
					return attempt(fmt.Sprintf("The previous response was not valid JSON (byte %d). Check the JSON and answer the same request.", syntax.Offset)), nil
				}
				return nil, fmt.Errorf("%s review: %w", req.Chapter, err)
			}
			if err := t.applyReview(chapterIndex, recordIndex, out); err != nil {
				return nil, fmt.Errorf("%s review: %w", req.Chapter, err)
			}
			return t.nextNode(launchRoot)
		}
		return &node
	}
	return attempt(""), nil
}

func (t *traversal) applyReview(chapterIndex, recordIndex int, out review) error {
	c := t.chapters[chapterIndex]
	if out.Chapter != c.Chapter {
		return fmt.Errorf("unexpected chapter %q", out.Chapter)
	}
	revisit := recordIndex >= 0
	r := out.Record
	switch {
	case revisit:
		if out.Complete || r == nil || r.Passage != c.Records[recordIndex].Passage {
			return fmt.Errorf("revisit must replace the same passage without changing forward coverage")
		}
	case r == nil && !out.Complete:
		return fmt.Errorf("forward review must supply a passage or complete the chapter")
	case r != nil:
		if c.Cursor != nil && r.Passage.PrintedPage < c.Cursor.PrintedPage {
			return fmt.Errorf("forward passage precedes the cursor")
		}
		for _, previous := range c.Records {
			if previous.Passage == r.Passage {
				return fmt.Errorf("forward passage was already reviewed")
			}
		}
	}
	if r != nil {
		if err := t.checkRecord(*r, revisit); err != nil {
			return err
		}
	}
	if revisit {
		c.Records = slices.Clone(c.Records)
		c.Records[recordIndex] = *r
	} else {
		if r != nil {
			c.Records = append(slices.Clone(c.Records), *r)
			c.Cursor = &r.Passage
		} else if c.Records == nil {
			c.Records = []record{}
		}
		c.Complete = out.Complete
	}
	if err := writeChapter(t.dir, c); err != nil {
		return err
	}
	t.chapters[chapterIndex] = c
	if revisit {
		t.revisited[passageRef{c.Chapter, r.Passage}] = true
	} else {
		clear(t.revisited)
	}
	return nil
}

func (t *traversal) checkRecord(r record, revisit bool) error {
	if !r.Passage.valid() || r.Printed == "" {
		return fmt.Errorf("review requires a passage identity and printed finding")
	}
	switch r.Formal.Status {
	case "open", "not_applicable":
	case "established", "refuted":
		if r.Formal.Scope == "" || r.Formal.Argument == "" || len(r.References) == 0 {
			return fmt.Errorf("resolved formal finding requires scope, argument provenance, and a reference")
		}
	default:
		return fmt.Errorf("unknown formal status %q", r.Formal.Status)
	}
	for _, ref := range r.References {
		if !ref.valid() {
			return fmt.Errorf("invalid reference: %+v", ref)
		}
	}
	seen := make(map[string]bool)
	for _, e := range r.Evidence {
		if e.Conclusion == "" || seen[e.Conclusion] || !e.Evidence.valid() {
			return fmt.Errorf("invalid or duplicate evidence for conclusion %q", e.Conclusion)
		}
		seen[e.Conclusion] = true
	}
	deps := make(map[requirement]bool)
	for _, d := range r.Dependencies {
		q := d.Requirement
		if q.Conclusion == "" || !q.Source.Passage.valid() || !slices.Contains(manuscriptOrder[:], q.Source.Chapter) || deps[q] {
			return fmt.Errorf("invalid or duplicate dependency: %+v", q)
		}
		deps[q] = true
		// A forward review can declare a dependency without reviewing its evidence. A
		// revisit must explicitly reconcile the current input.
		if (revisit || d.Reviewed != nil) && !sameEvidence(d.Reviewed, t.currentEvidence(q)) {
			return fmt.Errorf("review did not acknowledge current evidence for %q", q.Conclusion)
		}
	}
	return nil
}

func (e evidence) valid() bool {
	return (e.Verdict == "supports" || e.Verdict == "contradicts") && e.Reference.valid()
}

func (r reference) valid() bool {
	return (r.Kind == "lean" || r.Kind == "audit") && r.Target != "" && r.Revision != ""
}
