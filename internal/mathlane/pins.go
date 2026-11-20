package mathlane

import (
	"context"
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
)

const (
	leanToolchain = "leanprover/lean4:v4.36.0"
	mathlibRev    = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
	mathlibURL    = "https://github.com/leanprover-community/mathlib4"
)

// Match only the two files used by this lane against
// their contents at the supported manifest revision.
// This is not a transitive dependency audit.
var mathlibModules = [...]struct{ name, digest string }{
	{"Mathlib.Basic.Complex.Basic", "2b8d7a4b65fd6118967bc1c62a1d628aceadb8926549cc1de2d3f38a0e90d15b"},
	{"Mathlib.Tactic.LinearCombination", "dcdbcbbdd75efb60a8a494acd280d11f1e512394686946c747a99f61c2ca837c"},
}

type moduleSource struct{ Module, Source string }

func pinnedSources(ctx context.Context, project, mathlib string) ([]moduleSource, error) {
	if err := context.Cause(ctx); err != nil {
		return nil, err
	}
	toolchain, err := readBounded(filepath.Join(project, "lean-toolchain"))
	if err != nil {
		return nil, err
	}
	if strings.TrimSpace(string(toolchain)) != leanToolchain {
		return nil, fmt.Errorf("unsupported Lean toolchain, want %s", leanToolchain)
	}
	data, err := readBounded(filepath.Join(project, "lake-manifest.json"))
	if err != nil {
		return nil, err
	}
	var manifest struct {
		Packages []struct{ Name, URL, Rev string }
	}
	if err := json.Unmarshal(data, &manifest); err != nil {
		return nil, fmt.Errorf("read Lake manifest: %w", err)
	}
	count := 0
	for _, pkg := range manifest.Packages {
		if pkg.Name == "mathlib" {
			count++
			if pkg.URL != mathlibURL || pkg.Rev != mathlibRev {
				return nil, fmt.Errorf("unsupported Mathlib pin, want %s at %s", mathlibURL, mathlibRev)
			}
		}
	}
	if count != 1 {
		return nil, fmt.Errorf("want one Mathlib pin in the Lake manifest, got %d", count)
	}
	if mathlib == "" {
		mathlib = filepath.Join(project, ".lake", "packages", "mathlib")
	} else if !filepath.IsAbs(mathlib) {
		return nil, fmt.Errorf("GRH_MATHLIB must be an absolute path")
	}
	var modules []moduleSource
	for _, mod := range mathlibModules {
		if err := context.Cause(ctx); err != nil {
			return nil, err
		}
		path := filepath.Join(mathlib, filepath.FromSlash(strings.ReplaceAll(mod.name, ".", "/")+".lean"))
		data, err := readBounded(path)
		if err != nil {
			return nil, err
		}
		if fmt.Sprintf("%x", sha256.Sum256(data)) != mod.digest {
			return nil, fmt.Errorf("source %s does not match Mathlib %s", path, mathlibRev)
		}
		modules = append(modules, moduleSource{mod.name, string(data)})
	}
	return modules, nil
}

func readBounded(path string) ([]byte, error) {
	info, err := os.Stat(path)
	if err != nil {
		return nil, err
	}
	if !info.Mode().IsRegular() || info.Size() > maxPromptBytes {
		return nil, fmt.Errorf("not a bounded regular file: %s", path)
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, maxPromptBytes+1))
	if err != nil {
		return nil, fmt.Errorf("read %s: %w", path, err)
	}
	if len(data) > maxPromptBytes {
		return nil, fmt.Errorf("file exceeds source limit: %s", path)
	}
	return data, nil
}
