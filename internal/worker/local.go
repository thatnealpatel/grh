package worker

import (
	"archive/tar"
	"bytes"
	"context"
	"crypto/sha256"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// CheckLocal builds the pinned project in a campaign integration workspace and
// audits the supplied modules and endpoints. It checks the disk build inputs
// against the exact revision without snapshotting or changing the jj graph.
// Use a trusted local toolchain and Lake cache. Independent statement review
// and selecting all affected modules and endpoints remain the caller's job.
func CheckLocal(ctx context.Context, root, revision string, modules, decls []string, out, diagnostics io.Writer) error {
	if !commitID.MatchString(revision) || len(modules) == 0 || len(decls) == 0 {
		return errors.New("expected full jj commit ID, project modules, and declarations")
	}
	for _, names := range [][]string{modules, decls} {
		seen := map[string]bool{}
		for _, name := range names {
			if !leanName.MatchString(name) || seen[name] {
				return fmt.Errorf("invalid or repeated Lean name %q", name)
			}
			seen[name] = true
		}
	}
	cmd := func(name string, args ...string) *exec.Cmd {
		c := exec.CommandContext(ctx, name, args...)
		c.Dir, c.Stderr = root, diagnostics
		return c
	}
	gitDir, err := cmd("jj", "--ignore-working-copy", "--at-op=@", "git", "root").Output()
	if err != nil {
		return fmt.Errorf("find backing Git repository: %w", err)
	}
	archive, err := cmd("git", "--no-replace-objects", "--git-dir", strings.TrimSuffix(string(gitDir), "\n"),
		"archive", "--format=tar", revision, "--", "Proofs", "lakefile.toml", "lake-manifest.json", "lean-toolchain").Output()
	if err != nil {
		return fmt.Errorf("read candidate %s: %w", revision, err)
	}
	verify := func() error { return compareLocalInputs(root, archive, modules) }
	if err := verify(); err != nil {
		return fmt.Errorf("workspace does not match %s: %w", revision, err)
	}
	c := cmd("lake", "--wfail", "build", "Proofs")
	c.Stdout = diagnostics
	if err := c.Run(); err != nil {
		return fmt.Errorf("lake --wfail build Proofs: %w", errors.Join(ctx.Err(), err))
	}
	// Lean 4.36 replays multiple targets
	// concurrently within one process.
	// Replay separately: The rational
	// explicit-formula batch crashed
	// with status 139, while all three
	// individual replays succeeded.
	for _, m := range modules {
		c := cmd("lake", "env", "leanchecker", "-v", m)
		c.Stdout = diagnostics
		if err := c.Run(); err != nil {
			return fmt.Errorf("lake env leanchecker %s: %w", m, errors.Join(ctx.Err(), err))
		}
	}
	c = cmd("lake", "env", "lean", "--json", "--stdin")
	c.Stdin = strings.NewReader(auditSource(modules, decls))
	msgs, err := c.Output()
	if err != nil {
		return fmt.Errorf("run Lean axiom audit: %w (%s)", errors.Join(ctx.Err(), err), tail(msgs))
	}
	if err := audit(msgs, decls); err != nil {
		return fmt.Errorf("Lean axiom audit: %w (%s)", err, tail(msgs))
	}
	if err := verify(); err != nil {
		return fmt.Errorf("build inputs changed during audit of %s: %w", revision, err)
	}
	if err := ctx.Err(); err != nil {
		return err
	}
	if _, err := out.Write(msgs); err != nil {
		return err
	}
	_, err = fmt.Fprintf(out, "Local build and kernel/axiom audit passed for %s (%s).\n", revision, strings.Join(modules, ", "))
	return err
}

func compareLocalInputs(root string, archive []byte, modules []string) error {
	if _, err := os.Lstat(filepath.Join(root, "lakefile.lean")); !errors.Is(err, fs.ErrNotExist) {
		return errors.New("cannot exclude alternate configuration lakefile.lean")
	}
	seen := map[string]bool{}
	tr := tar.NewReader(bytes.NewReader(archive))
	for {
		h, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}
		if h.Typeflag == tar.TypeDir || h.Typeflag == tar.TypeXGlobalHeader {
			continue
		}
		_, config := configHashes[h.Name]
		if !fs.ValidPath(h.Name) || h.Typeflag != tar.TypeReg || (!config && !strings.HasPrefix(h.Name, "Proofs/")) {
			return fmt.Errorf("unexpected archive entry %q", h.Name)
		}
		name := filepath.Join(root, h.Name)
		info, err := os.Lstat(name)
		if err != nil {
			return err
		}
		if !info.Mode().IsRegular() || info.Size() != h.Size {
			return fmt.Errorf("different file type or size: %s", h.Name)
		}
		data, err := io.ReadAll(tr)
		if err != nil {
			return err
		}
		local, err := os.ReadFile(name)
		if err != nil {
			return err
		}
		if !bytes.Equal(data, local) {
			return fmt.Errorf("different contents: %s", h.Name)
		}
		if config && fmt.Sprintf("%x", sha256.Sum256(data)) != configHashes[h.Name] {
			return fmt.Errorf("project pin changed: %s", h.Name)
		}
		seen[h.Name] = true
	}
	for config := range configHashes {
		if !seen[config] {
			return fmt.Errorf("missing pinned configuration: %s", config)
		}
	}
	for _, m := range modules {
		if !seen["Proofs/"+strings.ReplaceAll(m, ".", "/")+".lean"] {
			return fmt.Errorf("not a candidate module: %s", m)
		}
	}
	return fs.WalkDir(os.DirFS(root), "Proofs", func(name string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !d.IsDir() && !seen[name] {
			return fmt.Errorf("extra file in proof tree: %s", name)
		}
		return nil
	})
}
