package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"

	"patel.codes/grh/internal/mathlane"
)

// The campaign's accepted commit need not be the revision checked out in the
// scheduler's directory. Read only the review inputs from the immutable tree.
func reviewLanded(ctx context.Context, root, revision, mission, question, packet string, d mathlane.Draft) (mathlane.Verdict, error) {
	return landedReview(ctx, root, revision, mission, question, packet, d, mathlane.Challenge)
}

func landedReview(ctx context.Context, root, revision, mission, question, packet string, d mathlane.Draft, review func(context.Context, string, string, string, string, mathlane.Draft) (mathlane.Verdict, error)) (mathlane.Verdict, error) {
	if !regexp.MustCompile(`^[a-f0-9]{40}$`).MatchString(revision) {
		return mathlane.Verdict{}, errors.New("invalid landed revision")
	}
	dir, err := os.MkdirTemp("", "grh-landed-*")
	if err != nil {
		return mathlane.Verdict{}, err
	}
	defer os.RemoveAll(dir)
	paths := []string{"lean-toolchain", "lake-manifest.json", "lakefile.toml"}
	for name := range d.Files {
		if !filepath.IsLocal(name) || !strings.HasPrefix(name, "Proofs/") || filepath.Clean(name) != name {
			return mathlane.Verdict{}, errors.New("invalid review path")
		}
		paths = append(paths, name)
	}
	for _, name := range paths {
		cmd := exec.CommandContext(ctx, "jj", "--ignore-working-copy", "file", "show", "-r", `commit_id("`+revision+`")`, "--", name)
		cmd.Dir = root
		data, err := cmd.Output()
		if err != nil {
			return mathlane.Verdict{}, fmt.Errorf("read %s in %s: %w", name, revision, err)
		}
		if expected, ok := d.Files[name]; ok && string(data) != expected {
			return mathlane.Verdict{}, fmt.Errorf("draft differs from immutable %s at %s", revision, name)
		}
		path := filepath.Join(dir, name)
		if err = os.MkdirAll(filepath.Dir(path), 0700); err != nil {
			return mathlane.Verdict{}, err
		}
		if err = os.WriteFile(path, data, 0400); err != nil {
			return mathlane.Verdict{}, err
		}
	}
	if os.Getenv("GRH_MATHLIB") == "" {
		deps := filepath.Join(dir, ".lake", "packages")
		if err = os.MkdirAll(deps, 0700); err != nil {
			return mathlane.Verdict{}, err
		}
		if err = os.Symlink(filepath.Join(root, ".lake", "packages", "mathlib"), filepath.Join(deps, "mathlib")); err != nil {
			return mathlane.Verdict{}, err
		}
	}
	return review(ctx, dir, mission, question, packet, d)
}
