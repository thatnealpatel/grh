package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
)

// Edition recorded in .godel/sources/masullo/README.md.
const edition = "e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5"

var manuscriptOrder = [...]string{
	"chapter-01", "chapter-02", "chapter-03", "chapter-04", "chapter-05", "chapter-06", "chapter-07",
	"chapter-08", "chapter-09", "chapter-10", "chapter-11", "chapter-12", "chapter-13", "chapter-14",
	"appendix-a", "appendix-b", "appendix-c", "appendix-d", "appendix-e",
}

// A passage's identity is this tuple
// within its chapter and edition.
type passage struct {
	Kind        string `json:"kind"`
	Locator     string `json:"locator"`
	PrintedPage int    `json:"printed_page"`
}

func (p passage) valid() bool {
	return p.Kind != "" && p.Locator != "" && p.PrintedPage > 0
}

type passageRef struct {
	Chapter string  `json:"chapter"`
	Passage passage `json:"passage"`
}

type reference struct {
	Kind     string `json:"kind"` // lean or audit
	Target   string `json:"target"`
	Revision string `json:"revision"`
}

type formalFinding struct {
	Status   string `json:"status"` // open, established, refuted, or not_applicable
	Scope    string `json:"scope"`
	Argument string `json:"argument_provenance"`
}

type evidence struct {
	Verdict   string    `json:"verdict"` // supports or contradicts
	Reference reference `json:"reference"`
}

type conclusionEvidence struct {
	Conclusion string   `json:"conclusion"`
	Evidence   evidence `json:"evidence"`
}

type requirement struct {
	Source     passageRef `json:"source"`
	Conclusion string     `json:"conclusion"`
}

type dependency struct {
	Requirement requirement `json:"requirement"`
	Reviewed    *evidence   `json:"reviewed"`
}

type record struct {
	Passage      passage              `json:"passage"`
	Printed      string               `json:"printed_finding"`
	Formal       formalFinding        `json:"formal"`
	References   []reference          `json:"references,omitempty"`
	Evidence     []conclusionEvidence `json:"conclusion_evidence,omitempty"`
	Dependencies []dependency         `json:"dependencies,omitempty"`
}

type chapterState struct {
	Edition  string   `json:"edition"`
	Chapter  string   `json:"chapter"`
	Cursor   *passage `json:"cursor"`
	Complete bool     `json:"complete"`
	Records  []record `json:"records"`
}

func readChapter(dir, id string) (chapterState, error) {
	path := filepath.Join(dir, id+".json")
	data, err := os.ReadFile(path)
	if errors.Is(err, os.ErrNotExist) {
		return chapterState{Edition: edition, Chapter: id}, nil
	}
	if err != nil {
		return chapterState{}, err
	}
	var c chapterState
	if err := json.Unmarshal(data, &c); err != nil {
		return c, fmt.Errorf("read %s: %w", path, err)
	}
	if c.Chapter != id || c.Edition != edition {
		return c, fmt.Errorf("%s: chapter or edition mismatch", path)
	}
	if n := len(c.Records); (n == 0 && (c.Cursor != nil || !c.Complete)) ||
		(n > 0 && (c.Cursor == nil || *c.Cursor != c.Records[n-1].Passage)) {
		return c, fmt.Errorf("%s: inconsistent cursor and records", path)
	}
	return c, nil
}

func writeChapter(dir string, c chapterState) error {
	data, err := json.MarshalIndent(c, "", "  ")
	if err != nil {
		return err
	}
	if err := os.MkdirAll(dir, 0755); err != nil {
		return err
	}
	f, err := os.CreateTemp(dir, ".walk-*")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	_, err = f.Write(append(data, '\n'))
	if closeErr := f.Close(); err == nil {
		err = closeErr
	}
	if err != nil {
		return err
	}
	// Readers see the previous review or the entire new review, never
	// a cursor or dependency receipt published ahead of its record.
	return os.Rename(f.Name(), filepath.Join(dir, c.Chapter+".json"))
}
