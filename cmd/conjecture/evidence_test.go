package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"patel.codes/grh/internal/accepted"
)

func TestExportPinnedEvidence(t *testing.T) {
	t.Parallel()
	base := t.TempDir()
	root := filepath.Join(base, "repo")
	if err := os.Mkdir(root, 0700); err != nil {
		t.Fatal(err)
	}
	write := func(path, value string) {
		t.Helper()
		if err := os.WriteFile(path, []byte(value), 0600); err != nil {
			t.Fatal(err)
		}
	}
	read := func(path string) []byte {
		t.Helper()
		b, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		return b
	}
	git := func(args ...string) string {
		t.Helper()
		cmd := exec.CommandContext(t.Context(), "git", args...)
		cmd.Dir = root
		cmd.Env = append(cmd.Environ(), "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_NOSYSTEM=1",
			"GIT_AUTHOR_NAME=fixture", "GIT_AUTHOR_EMAIL=fixture@example.invalid",
			"GIT_COMMITTER_NAME=fixture", "GIT_COMMITTER_EMAIL=fixture@example.invalid")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("git %v: %s: %v", args, out, err)
		}
		return strings.TrimSpace(string(out))
	}
	git("init", "--template=", "-b", "main")
	old := cardPath("open", "older-claim")
	files := map[string]string{
		mission:                            "Mission at the pin\n",
		frontier:                           "Frontier at the pin\n",
		".godel/obligations/missing.md":    "An unresolved premise.\n",
		".godel/sources/edition/README.md": "Pinned edition.\n",
		"Proofs/Test.lean":                 "theorem test : True := trivial\n",
		old:                                "An accepted card.\n",
		"unrelated.md":                     "Do not export.\n",
		// git archive would omit Proofs; exact blob
		// export must include it.
		".gitattributes": "Proofs export-ignore\n",
	}
	for name, contents := range files {
		p := filepath.Join(root, name)
		if err := os.MkdirAll(filepath.Dir(p), 0700); err != nil {
			t.Fatal(err)
		}
		write(p, contents)
	}
	git("add", ".")
	first := git("commit-tree", git("write-tree"), "-m", "accepted evidence")
	git("update-ref", "refs/heads/main", first)
	pin := accepted.Snapshot{Root: root, GitDir: filepath.Join(root, ".git"), Target: "main", Revision: first}
	write(filepath.Join(root, mission), "Changed mission.\n")
	git("add", mission)
	next := git("commit-tree", git("write-tree"), "-p", first, "-m", "new evidence")
	git("update-ref", "refs/heads/main", next, first)
	write(filepath.Join(root, old), "Dirty card.\n")
	dir := filepath.Join(base, "snapshot")
	cards, err := exportEvidence(t.Context(), pin, dir)
	if err != nil {
		t.Fatal(err)
	}
	if len(cards) != 1 || cards["older-claim"] != "open" {
		t.Fatalf("wrong accepted card inventory: %+v", cards)
	}
	index := string(read(filepath.Join(dir, "index.txt")))
	if !strings.HasPrefix(index, "Accepted evidence commit: "+first+"\n") {
		t.Fatalf("wrong evidence index: %s", index)
	}
	for name, want := range files {
		if name == "unrelated.md" || name == ".gitattributes" {
			if _, err := os.Lstat(filepath.Join(dir, name)); !os.IsNotExist(err) {
				t.Errorf("unexpected export for %s: %v", name, err)
			}
			continue
		}
		if got := string(read(filepath.Join(dir, name))); got != want || !strings.Contains(index, "\n"+name+"\n") {
			t.Errorf("wrong export for %s: %q (wanted %q)", name, got, want)
		}
	}
}
