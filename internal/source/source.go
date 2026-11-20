// Package source reads passages from the pinned Masullo manuscript.
package source

import (
	"context"
	"fmt"
	"os"
	"strings"
)

// Passage specifies one or two
// consecutive printed pages in the
// pinned edition. Heading locates the
// passage; Question sets its scope
// without proposing a reading.
type Passage struct {
	First, Last int
	Heading     string
	Question    string
}

// Packet records a source reading,
// not a proof or a validation of its
// translation. An infrastructure
// failure returns an error instead of a
// disposition.
type Packet struct {
	Disposition string    `json:"disposition"`
	Anchor      string    `json:"anchor"`
	Reading     string    `json:"reading"`
	Attribution string    `json:"attribution"`
	Boundary    string    `json:"boundary"`
	Evidence    [2]string `json:"evidence"`
	Comparison  string    `json:"comparison,omitempty"`
}

const (
	verified  = "verified"
	ambiguous = "ambiguous"
	absent    = "absent"
)

// ReadPassage renders the requested pages and compares two fresh
// visual readings through headless Yah. It uses GRH_PDF (if set) or
// the digest-verified download. If Yah cannot establish visual access
// to every rendered page, it returns an error and no disposition.
func ReadPassage(ctx context.Context, target Passage) (Packet, error) {
	return manuscript.readPassage(ctx, target)
}

func (e edition) readPassage(ctx context.Context, target Passage) (Packet, error) {
	if err := ctx.Err(); err != nil {
		return Packet{}, err
	}
	target.Heading = strings.TrimSpace(target.Heading)
	target.Question = strings.TrimSpace(target.Question)
	if target.First < 1 || target.Last < target.First || target.Last > editionPages || target.Last-target.First > 1 || target.Heading == "" || target.Question == "" {
		return Packet{}, fmt.Errorf("source: passage needs one or two consecutive printed pages (1–%d), a heading, and a question", editionPages)
	}
	dir, err := os.MkdirTemp("/tmp", "grh-source-")
	if err != nil {
		return Packet{}, fmt.Errorf("source: create render directory: %w", err)
	}
	defer os.RemoveAll(dir)
	pdf, err := e.load(ctx, os.Getenv("GRH_PDF"))
	if err != nil {
		return Packet{}, err
	}
	pages, err := render(ctx, dir, pdf, target)
	if err != nil {
		return Packet{}, err
	}
	var reads [2]reading
	for i := range reads {
		r, err := read(ctx, dir, target, pages)
		if err != nil {
			return Packet{}, fmt.Errorf("source: %s: %w", readerLabel(i), err)
		}
		reads[i] = r
	}
	var review *comparison
	if needsComparison(reads) {
		c, err := adjudicate(ctx, dir, target, pages, reads)
		if err != nil {
			return Packet{}, fmt.Errorf("source: Yah adjudicator: %w", err)
		}
		review = &c
	}
	if err := ctx.Err(); err != nil {
		return Packet{}, err
	}
	return e.assemble(target, reads, review), nil
}

type reading struct {
	Disposition  string `json:"disposition"`
	PrintedPages []int  `json:"printed_pages"`
	Reading      string `json:"reading"`
	Attribution  string `json:"attribution"`
	Evidence     string `json:"evidence"`
	Boundary     string `json:"boundary"`
}

func needsComparison(reads [2]reading) bool {
	a, b := reads[0], reads[1]
	return a.Disposition == absent && b.Disposition == absent ||
		a.Disposition == verified && b.Disposition == verified && !sameReading(a, b)
}

func sameReading(a, b reading) bool {
	return sameText(a.Reading, b.Reading) && sameText(a.Attribution, b.Attribution) && sameText(a.Boundary, b.Boundary)
}

func readerLabel(i int) string {
	return fmt.Sprintf("Yah reader %d", i+1)
}

func (e edition) assemble(target Passage, reads [2]reading, review *comparison) Packet {
	p := Packet{
		Anchor: fmt.Sprintf("Alessandro Maria Masullo, The Music of the Primes, %s (SHA-256 %s), printed pp. %d–%d = PDF ordinals %d–%d: %s",
			e.url, e.sha256, target.First, target.Last, target.First, target.Last, target.Heading),
	}
	for i, r := range reads {
		p.Evidence[i] = fmt.Sprintf("%s (%s): %s", readerLabel(i), r.Disposition, r.Evidence)
	}
	a, b := reads[0], reads[1]
	approved := review != nil && review.agree()
	if review != nil {
		p.Comparison = "Yah adjudicator: " + review.Evidence
	}
	switch {
	case a.Disposition == verified && b.Disposition == verified && (sameReading(a, b) || approved):
		p.Disposition, p.Reading, p.Attribution, p.Boundary = verified, a.Reading, a.Attribution, a.Boundary
	case a.Disposition == absent && b.Disposition == absent && approved:
		p.Disposition = absent
		p.Reading = "Both readers reported the requested statement absent within the rendered passage. " + a.Reading
		p.Attribution = "No attributable statement for this question was established."
	default:
		p.Disposition = ambiguous
		p.Reading = fmt.Sprintf("No verified agreement. %s (%s): %s\n%s (%s): %s", readerLabel(0), a.Disposition, a.Reading, readerLabel(1), b.Disposition, b.Reading)
		p.Attribution = "No attribution established for a verified reading."
		p.Boundary = fmt.Sprintf("Reported boundaries (not verified): %s: %s; %s: %s", readerLabel(0), a.Boundary, readerLabel(1), b.Boundary)
	}
	if approved {
		p.Boundary = review.Boundary
	}
	p.Boundary = target.Heading + ": " + p.Boundary + " Limited to this passage; the packet is not a proof and supplies no external realization assumptions."
	return p
}

func sameText(a, b string) bool {
	// No mathematical equivalence or paraphrase inference at this boundary.
	return strings.Join(strings.Fields(a), " ") == strings.Join(strings.Fields(b), " ")
}
