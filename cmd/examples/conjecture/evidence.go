package main

import (
	"bytes"
	"context"
	"fmt"
	"io/fs"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"strconv"
	"strings"

	"patel.codes/grh/internal/accepted"
)

const (
	cardRoot = ".godel/conjectures"
	mission  = "cmd/godel/mission.md"
	frontier = ".godel/frontier.md"
)

var evidencePaths = []string{
	mission, frontier, ".godel/obligations", cardRoot, ".godel/sources",
	"Proofs", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
}

// Read exact blobs, not archive-filtered or working-copy contents. The index
// gives the reader entry points without putting the entire Lean tree in a
// prompt.
func exportEvidence(ctx context.Context, pin accepted.Snapshot, dir string) (map[string]string, error) {
	git := func(args ...string) *exec.Cmd {
		return exec.CommandContext(ctx, "git", append([]string{"--no-replace-objects", "--literal-pathspecs", "--git-dir", pin.GitDir}, args...)...)
	}
	if !commitID(pin.Revision) {
		return nil, fmt.Errorf("expected full evidence commit, got %q", pin.Revision)
	}
	list, err := git(append([]string{"ls-tree", "-rz", "--full-tree", pin.Revision, "--"}, evidencePaths...)...).Output()
	if err != nil {
		return nil, fmt.Errorf("list accepted evidence: %w", err)
	}
	type entry struct{ name, oid string }
	var files []entry
	var ids, index strings.Builder
	fmt.Fprintln(&index, "Accepted evidence commit:", pin.Revision)
	var haveMission, haveFrontier bool
	for row := range bytes.SplitSeq(list, []byte{0}) {
		if len(row) == 0 {
			continue
		}
		meta, name, _ := strings.Cut(string(row), "\t")
		fields := strings.Fields(meta)
		if len(fields) != 3 || (fields[0] != "100644" && fields[0] != "100755") || fields[1] != "blob" || !commitID(fields[2]) ||
			!fs.ValidPath(name) || name == "." || strings.ContainsAny(name, "\r\n\t") {
			return nil, fmt.Errorf("unexpected evidence entry %q", row)
		}
		files = append(files, entry{name, fields[2]})
		fmt.Fprintln(&ids, fields[2])
		fmt.Fprintln(&index, name)
		haveMission = haveMission || name == mission
		haveFrontier = haveFrontier || name == frontier
	}
	if !haveMission || !haveFrontier {
		return nil, fmt.Errorf("accepted evidence %s is missing the mission or frontier", pin.Revision)
	}
	batch := git("cat-file", "--batch")
	batch.Stdin = strings.NewReader(ids.String())
	blobs, err := batch.Output()
	if err != nil {
		return nil, fmt.Errorf("read accepted evidence: %w", err)
	}
	cards := make(map[string]string)
	for _, f := range files {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		header, rest, ok := bytes.Cut(blobs, []byte{'\n'})
		size, err := strconv.Atoi(strings.TrimPrefix(string(header), f.oid+" blob "))
		if !ok || err != nil || size < 0 || size >= len(rest) || rest[size] != '\n' {
			return nil, fmt.Errorf("missing or malformed accepted blob for %q", f.name)
		}
		data := rest[:size:size]
		blobs = rest[size+1:]
		if rel, ok := strings.CutPrefix(f.name, cardRoot+"/"); ok {
			where, name, _ := strings.Cut(rel, "/")
			slug, md := strings.CutSuffix(name, ".md")
			if md && (where == "open" || where == "closed") {
				if !validSlug(slug) || cards[slug] != "" {
					return nil, fmt.Errorf("invalid or duplicate accepted card %q", f.name)
				}
				cards[slug] = where
			}
		}
		name := filepath.Join(dir, filepath.FromSlash(f.name))
		if err := os.MkdirAll(filepath.Dir(name), 0700); err != nil {
			return nil, err
		}
		if err := os.WriteFile(name, data, 0400); err != nil {
			return nil, err
		}
	}
	if len(blobs) != 0 {
		return nil, fmt.Errorf("unexpected trailing Git blob data")
	}
	return cards, os.WriteFile(filepath.Join(dir, "index.txt"), []byte(index.String()), 0400)
}

func cardPath(where, slug string) string { return path.Join(cardRoot, where, slug+".md") }

func commitID(s string) bool {
	return (len(s) == 40 || len(s) == 64) && strings.Trim(s, "0123456789abcdef") == ""
}
