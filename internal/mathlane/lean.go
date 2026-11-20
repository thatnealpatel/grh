package mathlane

import (
	"context"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"slices"
	"strconv"
	"strings"
)

const (
	propsPath        = "Proofs/Props/TraceAssembly.lean"
	theoremPath      = "Proofs/Theorems/TraceAssembly.lean"
	geometricDecl    = "TraceAssembly.GeometricDiagonal"
	spectralDecl     = "TraceAssembly.SpectralDiagonal"
	assemblyDecl     = "TraceAssembly.assemble"
	interfaceSummary = "Conditional scalar interface for the final two-diagonal-identity step. Neither analytic identity is proved."
	assemblySummary  = "Conditional two-identity algebra proof candidate. Both analytic inputs remain; no Lean verification or full trace theorem is claimed."
)

const propsIntro = `import Mathlib.Basic.Complex.Basic

/-!
# Conditional assembly of two diagonal identities

This is our scalar abstraction, not a Lean formalization of the analytic
trace theorem. All five quantities must come from the same admissible
manuscript data and normalizations. Admissibility (including the domain of
test functions and support, invariance, and auxiliary parameter restrictions)
is an interpretation condition recorded in the source packet, not encoded
as an arbitrary Lean hypothesis. Neither diagonal evaluation is proved here.

* diagonal: the global diagonal integral, common to the two identities.
* orbital: the weighted local orbital side.
* mellinPlus and mellinMinus: the two Mellin values, at the positive and
  negative half powers of the norm character respectively.
* zeros: the spectral sum with its strip, multiplicities, and Mellin argument
  as specified in the passage.
-/

`

const geometricPrefix = `
namespace TraceAssembly

/-- The geometric evaluation of the common global diagonal. -/
def GeometricDiagonal (diagonal orbital mellinPlus mellinMinus : ℂ) : Prop :=
  `

const spectralPrefix = `

/-- The spectral evaluation of the same diagonal. -/
def SpectralDiagonal (diagonal zeros : ℂ) : Prop :=
  `

const moduleEnd = `

end TraceAssembly
`

const leafPrefix = `theorem assemble (diagonal orbital mellinPlus mellinMinus zeros : ℂ)
    (hGeom : GeometricDiagonal diagonal orbital mellinPlus mellinMinus)
    (hSpec : SpectralDiagonal diagonal zeros) :
    `

const theoremPrefix = `import Props.TraceAssembly
import Mathlib.Tactic.LinearCombination

namespace TraceAssembly

/-- Assemble the two diagonal evaluations. The analytic identities are inputs,
not conclusions of this theorem. -/
`

const proofPrefix = ` := by
  unfold GeometricDiagonal at hGeom
  unfold SpectralDiagonal at hSpec
  linear_combination `

type sourceReading struct{ Disposition, Anchor, Reading, Attribution, Boundary string }

func propsPreamble(s sourceReading) string {
	var b strings.Builder
	b.WriteString(propsIntro)
	// Packet prose is data, not a Lean command or block comment. Quote it as
	// printable text on single-line comments, escaping controls and newlines.
	b.WriteString("-- Independently sourced interpretation (not formal Lean hypotheses):\n")
	for _, field := range []struct{ label, text string }{
		{"Anchor", s.Anchor}, {"Attribution", s.Attribution}, {"Reading", s.Reading}, {"Boundary", s.Boundary},
	} {
		fmt.Fprintf(&b, "-- %s: %s\n", field.label, strconv.Quote(field.text))
	}
	b.WriteString(geometricPrefix)
	return b.String()
}

func interfaceDraft(s sourceReading, g, z, goal string) (Draft, error) {
	geometric, spectral, conclusion, err := equations(g, z, goal)
	if err != nil {
		return Draft{}, err
	}
	return Draft{
		Files: map[string]string{propsPath: propsPreamble(s) + geometric + spectralPrefix + spectral + moduleEnd},
		Decls: []string{geometricDecl, spectralDecl},
		Premises: []string{
			"hGeom : TraceAssembly.GeometricDiagonal diagonal orbital mellinPlus mellinMinus",
			"hSpec : TraceAssembly.SpectralDiagonal diagonal zeros",
		},
		Leaf: leafPrefix + conclusion, Summary: interfaceSummary,
	}, nil
}

func equations(g, z, goal string) (string, string, string, error) {
	g, err := equation(g, "diagonal", "orbital", "mellinPlus", "mellinMinus")
	if err != nil {
		return "", "", "", err
	}
	z, err = equation(z, "diagonal", "zeros")
	if err != nil {
		return "", "", "", err
	}
	goal, err = equation(goal, "orbital", "mellinPlus", "mellinMinus", "zeros")
	return g, z, goal, err
}

func theoremFile(header, combination string) string {
	return theoremPrefix + header + proofPrefix + combination + moduleEnd
}

func validateDraft(s sourceReading, d Draft) error {
	data, prefix := strings.CutPrefix(d.Files[propsPath], propsPreamble(s))
	g, data, middle := strings.Cut(data, spectralPrefix)
	z, suffix := strings.CutSuffix(data, moduleEnd)
	if !prefix || !middle || !suffix {
		return fmt.Errorf("%w: invalid proposition module or source provenance", ErrRejected)
	}
	var combination string
	header := d.Leaf
	if header == "" {
		data, prefix := strings.CutPrefix(d.Files[theoremPath], theoremPrefix)
		h, data, middle := strings.Cut(data, proofPrefix)
		c, suffix := strings.CutSuffix(data, moduleEnd)
		if !prefix || !middle || !suffix || !validCombination(c) {
			return fmt.Errorf("%w: unsupported assembly proof surface", ErrRejected)
		}
		header, combination = h, c
	}
	goal, ok := strings.CutPrefix(header, leafPrefix)
	if !ok {
		return fmt.Errorf("%w: not a supported theorem header", ErrRejected)
	}
	template, err := interfaceDraft(s, g, z, goal)
	if err != nil {
		return err
	}
	if header != template.Leaf || !slices.Equal(d.Premises, template.Premises) || d.Files[propsPath] != template.Files[propsPath] {
		return fmt.Errorf("%w: header, analytic premises, or proposition module are out of scope", ErrRejected)
	}
	if d.Leaf != "" {
		if len(d.Files) != 1 || !slices.Equal(d.Decls, template.Decls) || d.Summary != interfaceSummary {
			return fmt.Errorf("%w: invalid interface file or declaration scope", ErrRejected)
		}
	} else if len(d.Files) != 2 || !slices.Equal(d.Decls, append(template.Decls, assemblyDecl)) ||
		d.Summary != assemblySummary || d.Files[theoremPath] != theoremFile(header, combination) {
		return fmt.Errorf("%w: invalid assembled file or declaration scope", ErrRejected)
	}
	return nil
}

func matchLanded(ctx context.Context, root string, d Draft) (Verdict, error) {
	r, err := os.OpenRoot(root)
	if err != nil {
		return Verdict{}, fmt.Errorf("open landed snapshot: %w", err)
	}
	defer r.Close()
	// Do not follow symlink components in
	// the candidate paths. The caller must
	// keep the snapshot immutable throughout
	// this comparison and review.
	paths := []string{propsPath}
	if _, ok := d.Files[theoremPath]; ok {
		paths = append(paths, theoremPath)
	}
	for _, path := range paths {
		if err := context.Cause(ctx); err != nil {
			return Verdict{}, err
		}
		var prefix string
		for component := range strings.SplitSeq(path, "/") {
			if prefix != "" {
				prefix += "/"
			}
			prefix += component
			info, err := r.Lstat(prefix)
			if errors.Is(err, fs.ErrNotExist) {
				return Verdict{Reason: "landed candidate path is missing: " + path}, nil
			}
			if err != nil {
				return Verdict{}, fmt.Errorf("inspect landed %s: %w", path, err)
			}
			if prefix != path && !info.IsDir() || prefix == path && !info.Mode().IsRegular() {
				return Verdict{Reason: "landed candidate path is not a regular file: " + path}, nil
			}
		}
		f, err := r.Open(path)
		if err != nil {
			return Verdict{}, fmt.Errorf("open landed %s: %w", path, err)
		}
		want := d.Files[path]
		data, err := io.ReadAll(io.LimitReader(f, int64(len(want))+1))
		f.Close()
		if err != nil {
			return Verdict{}, fmt.Errorf("read landed %s: %w", path, err)
		}
		if string(data) != want {
			return Verdict{Reason: "landed content differs from the candidate: " + path}, nil
		}
	}
	return Verdict{Accept: true}, nil
}
