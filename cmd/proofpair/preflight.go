package main

import (
	"bytes"
	"context"
	"crypto/sha1"
	"crypto/sha256"
	"debug/buildinfo"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"strings"

	"golang.org/x/sys/unix"
)

const (
	pdfHash    = "e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5"
	yahVersion = "v0.0.59-0.20261119201545-8f0869c38bc6"
)

func checkEnvironment(env []string) error {
	for _, entry := range env {
		name, _, _ := strings.Cut(entry, "=")
		if strings.HasPrefix(name, "GIT_") || strings.HasPrefix(name, "JJ_") || strings.HasPrefix(name, "YAH_") {
			return fmt.Errorf("unset routing/configuration variable %s", name)
		}
	}
	return nil
}

func trialEnv(root string) []string {
	// Use the same Git routing during
	// verification and in Yah (including
	// when Yah initializes the colocated
	// repo). Do not inherit operator config.
	return []string{
		"HOME=" + trialHome, "PATH=" + binDir + ":/usr/bin:/bin", "LC_ALL=C", "TZ=UTC",
		"GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL=/dev/null", "GIT_ATTR_NOSYSTEM=1",
		"GIT_NO_REPLACE_OBJECTS=1", "GIT_TERMINAL_PROMPT=0",
		"JJ_CONFIG=/dev/null", "JJ_USER=Proofpair", "JJ_EMAIL=proofpair@invalid",
		"YAH_DEFAULT_MODEL=" + model, "YAH_INBOX=off", "YAH_CAMPAIGN_TARGET=main",
		"YAH_DEFAULT_TOOLS=read:write:edit:bash:subagent:task:campaign",
		"GRH_PDF=" + filepath.Join(root, "..", "masullo.pdf"),
		"GOPROXY=off", "GOTOOLCHAIN=local", "GOSUMDB=off",
	}
}

type checkout struct {
	root string
	env  []string
	seed string
}

func (c checkout) git(ctx context.Context, args ...string) (string, error) {
	cmd := exec.CommandContext(ctx, "/usr/bin/git", args...)
	cmd.Dir, cmd.Env = c.root, c.env
	b, err := cmd.Output()
	if err != nil {
		if exit, ok := err.(*exec.ExitError); ok {
			return "", fmt.Errorf("git %s: %w: %s", args[0], err, bytes.TrimSpace(exit.Stderr))
		}
		return "", fmt.Errorf("git %s: %w", args[0], err)
	}
	return string(b), nil
}

func (c *checkout) checkSnapshot(ctx context.Context, tree string) error {
	// No .jj: Yah must initialize from the exact Git checkout we
	// check, not attach to an existing operation log, alternate
	// backend or workspace.
	if err := absent(filepath.Join(c.root, ".jj")); err != nil {
		return err
	}
	gd := filepath.Join(c.root, ".git")
	if err := realDir(gd); err != nil {
		return err
	}
	if err := checkGitLayout(gd); err != nil {
		return err
	}
	if err := c.checkGitIdentity(ctx, tree); err != nil {
		return err
	}
	return c.checkFiles(ctx)
}

var looseObject = regexp.MustCompile(`^objects/[0-9a-f]{2}/[0-9a-f]{38}$`)
var objectDir = regexp.MustCompile(`^objects/[0-9a-f]{2}$`)

func checkGitLayout(dir string) error {
	return filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
		if err != nil || path == dir {
			return err
		}
		rel, err := filepath.Rel(dir, path)
		if err != nil {
			return err
		}
		if d.IsDir() {
			switch rel {
			case "objects", "objects/info", "objects/pack", "refs", "refs/heads", "refs/tags":
				return nil
			}
			if objectDir.MatchString(rel) {
				return nil
			}
		} else if d.Type().IsRegular() {
			switch rel {
			case "HEAD", "config", "index", "refs/heads/main":
				return nil
			}
			if looseObject.MatchString(rel) {
				return nil
			}
		}
		return fmt.Errorf("unexpected Git metadata: %s", rel)
	})
}

func (c *checkout) checkGitIdentity(ctx context.Context, tree string) error {
	cfg, err := c.git(ctx, "config", "--local", "--no-includes", "--null", "--list")
	if err != nil {
		return err
	}
	// An empty-template, ordinary Git init has just these keys. Reject includes,
	// remotes, extensions, core.worktree, and any other local customization.
	for entry := range strings.SplitSeq(strings.TrimSuffix(cfg, "\x00"), "\x00") {
		switch entry {
		case "core.repositoryformatversion\n0", "core.filemode\ntrue", "core.bare\nfalse", "core.logallrefupdates\ntrue":
		default:
			key, _, _ := strings.Cut(entry, "\n")
			return fmt.Errorf("unexpected Git config key or value: %s", key)
		}
	}
	for _, check := range []struct {
		args []string
		want string
	}{
		{[]string{"rev-parse", "--show-toplevel"}, c.root},
		{[]string{"rev-parse", "--absolute-git-dir"}, filepath.Join(c.root, ".git")},
		{[]string{"symbolic-ref", "HEAD"}, "refs/heads/main"},
		{[]string{"for-each-ref", "--format=%(refname)"}, "refs/heads/main"},
		{[]string{"rev-parse", "HEAD^{tree}"}, tree},
		{[]string{"rev-parse", "HEAD"}, seedFor(tree)},
	} {
		got, err := c.git(ctx, check.args...)
		if err != nil {
			return err
		}
		if strings.TrimSuffix(got, "\n") != check.want {
			return fmt.Errorf("unexpected Git %s; want %s", strings.Join(check.args, " "), check.want)
		}
	}
	if _, err := c.git(ctx, "fsck", "--full", "--strict", "--no-progress"); err != nil {
		return err
	}
	// Unreachable objects could contain later proofs even with only one ref.
	reachable, err := c.git(ctx, "rev-list", "--objects", "--no-object-names", "HEAD")
	if err != nil {
		return err
	}
	objects, err := c.git(ctx, "cat-file", "--batch-all-objects", "--batch-check=%(objectname)")
	if err != nil {
		return err
	}
	want := strings.Fields(reachable)
	slices.Sort(want)
	if !slices.Equal(want, strings.Fields(objects)) {
		return fmt.Errorf("Git object database contains material outside the synthetic root")
	}
	c.seed = seedFor(tree)
	return nil
}

// seedFor pins the parentless commit's
// exact bytes as well as its tree.
func seedFor(tree string) string {
	const identity = "Proofpair <proofpair@invalid> 946684800 +0000"
	body := fmt.Sprintf("tree %s\nauthor %s\ncommitter %s\n\nFreeze proofpair input\n", tree, identity, identity)
	h := sha1.New()
	fmt.Fprintf(h, "commit %d\x00%s", len(body), body)
	return fmt.Sprintf("%x", h.Sum(nil))
}

func (c checkout) checkFiles(ctx context.Context) error {
	index, err := c.git(ctx, "ls-files", "-z", "-v")
	if err != nil {
		return err
	}
	for entry := range strings.SplitSeq(strings.TrimSuffix(index, "\x00"), "\x00") {
		if !strings.HasPrefix(entry, "H ") {
			return fmt.Errorf("unexpected Git index state")
		}
	}
	status, err := c.git(ctx, "--no-optional-locks", "status", "--porcelain=v1", "-z", "--untracked-files=no")
	if err != nil {
		return err
	}
	if status != "" {
		return fmt.Errorf("staged or unstaged changes in the baseline")
	}
	entries, err := c.git(ctx, "ls-tree", "-rz", "HEAD")
	if err != nil {
		return err
	}
	// Check disk bytes directly, including changes hidden by
	// index stat data.
	files, dirs := map[string][]string{}, map[string]bool{".": true}
	for entry := range strings.SplitSeq(strings.TrimSuffix(entries, "\x00"), "\x00") {
		meta, name, _ := strings.Cut(entry, "\t")
		bits := strings.Fields(meta)
		if len(bits) != 3 || bits[1] != "blob" || !fs.ValidPath(name) || (bits[0] != "100644" && bits[0] != "100755") {
			return fmt.Errorf("unexpected tree entry: %q", name)
		}
		files[name] = bits
		for dir := filepath.Dir(name); !dirs[dir]; dir = filepath.Dir(dir) {
			dirs[dir] = true
		}
	}
	err = fs.WalkDir(os.DirFS(c.root), ".", func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if path == ".git" || (path == ".lake" && d.IsDir()) {
			return fs.SkipDir
		}
		if d.IsDir() && dirs[path] {
			return nil
		}
		bits, tracked := files[path]
		if !tracked || !d.Type().IsRegular() {
			return fmt.Errorf("unexpected file, directory or symlink: %s", path)
		}
		data, err := os.ReadFile(filepath.Join(c.root, path))
		if err != nil {
			return err
		}
		info, err := d.Info()
		if err != nil {
			return err
		}
		h := sha1.New() // Git blob object format, not an authentication primitive.
		fmt.Fprintf(h, "blob %d\x00", len(data))
		h.Write(data)
		if fmt.Sprintf("%x", h.Sum(nil)) != bits[2] || (info.Mode()&0o100 != 0) != (bits[0] == "100755") {
			return fmt.Errorf("different worktree bytes or mode: %s", path)
		}
		delete(files, path)
		return nil
	})
	if err != nil {
		return err
	}
	if len(files) != 0 {
		return fmt.Errorf("missing tracked files")
	}
	return nil
}

// Check the entire PATH prefix, not just
// the tools we install: a stray git here
// would shadow the /usr/bin/git used by
// checkout verification.
func checkBinDir(dir string) error {
	canonical, err := filepath.EvalSymlinks(dir)
	if err != nil || canonical != dir {
		return fmt.Errorf("expected a canonical operator binary directory: %s", dir)
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		return err
	}
	want := []string{"godel-base", "jj", "lake", "pdftotext", "proofpair", "yah"}
	if len(entries) != len(want) {
		return fmt.Errorf("unexpected contents of operator binary directory: %s", dir)
	}
	for i, entry := range entries {
		info, err := entry.Info()
		if err != nil {
			return err
		}
		if entry.Name() != want[i] || info.Mode() != 0555 {
			return fmt.Errorf("unexpected operator binary name, type or mode: %s", entry.Name())
		}
	}
	return nil
}

func (c checkout) checkInputs() error {
	if err := checkBinDir(binDir); err != nil {
		return err
	}
	info, err := buildinfo.ReadFile(yahBin)
	if err != nil || info.Main.Path != "patel.codes/yah" || info.Main.Version != yahVersion {
		return fmt.Errorf("expected %s as module patel.codes/yah@%s (Go build metadata)", yahBin, yahVersion)
	}
	home, err := filepath.EvalSymlinks(trialHome)
	if err != nil || home != trialHome {
		return fmt.Errorf("HOME must name a canonical absolute directory")
	}
	if err := realDir(home); err != nil {
		return err
	}
	if homeEntries, err := os.ReadDir(home); err != nil || len(homeEntries) != 0 {
		return fmt.Errorf("require an empty trial HOME")
	}
	lake := filepath.Join(c.root, ".lake")
	if err := realDir(lake); err != nil {
		return err
	}
	if entries, err := os.ReadDir(lake); err != nil || len(entries) != 2 || entries[0].Name() != "build" || entries[1].Name() != "packages" {
		return fmt.Errorf("expected only build and packages in canonical .lake")
	}
	for _, path := range []string{"build", "packages"} {
		path = filepath.Join(lake, path)
		if err := realDir(path); err != nil {
			return err
		}
		var stat unix.Statfs_t
		if err := unix.Statfs(path, &stat); err != nil || stat.Flags&unix.ST_RDONLY == 0 {
			return fmt.Errorf("expected a read-only canonical cache mount: %s", path)
		}
	}
	pdf := filepath.Join(c.root, "..", "masullo.pdf")
	pdfInfo, err := os.Lstat(pdf)
	if err != nil || !pdfInfo.Mode().IsRegular() || pdfInfo.Size() != 6756996 {
		return fmt.Errorf("expected the pinned masullo.pdf alongside the baseline directory")
	}
	f, err := os.Open(pdf)
	if err != nil {
		return err
	}
	defer f.Close()
	h := sha256.New()
	if _, err := io.Copy(h, f); err != nil {
		return err
	}
	if fmt.Sprintf("%x", h.Sum(nil)) != pdfHash {
		return fmt.Errorf("masullo.pdf digest mismatch")
	}
	return nil
}

func realDir(path string) error {
	info, err := os.Lstat(path)
	if err != nil {
		return err
	}
	if !info.IsDir() {
		return fmt.Errorf("expected a real directory: %s", path)
	}
	return nil
}

func absent(path string) error {
	if _, err := os.Lstat(path); os.IsNotExist(err) {
		return nil
	} else if err != nil {
		return err
	}
	return fmt.Errorf("must not exist: %s", path)
}
