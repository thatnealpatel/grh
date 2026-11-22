package main

import (
	"bytes"
	"context"
	"fmt"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
)

// history is read-only. Campaign
// adoption uses a linear chain of exact
// candidates; a rewrite or merge is an
// operator-visible error, not an empty
// batch. In particular, each commit gets
// its own diff even after a revert.
type history interface {
	tip(context.Context) (string, error)
	between(ctx context.Context, base, tip string) ([]string, error)
	changes(ctx context.Context, parent, rev string) ([]change, error)
	matchesNote(ctx context.Context, rev, path string, data []byte) (bool, error)
}

type repository struct {
	root, gitDir, target string
}

func openRepository(ctx context.Context, root, target string) (*repository, error) {
	if target == "" {
		target = "main"
	}
	r := &repository{root: root, target: target}
	out, err := r.jj(ctx, "git", "root")
	if err != nil {
		return nil, err
	}
	r.gitDir, err = filepath.EvalSymlinks(strings.TrimSuffix(string(out), "\n"))
	if err != nil {
		return nil, err
	}
	if !filepath.IsAbs(r.gitDir) {
		return nil, fmt.Errorf("audit: expected an absolute backing Git path, got %q", r.gitDir)
	}
	return r, nil
}

func (r *repository) command(ctx context.Context, name string, args ...string) ([]byte, error) {
	cmd := exec.CommandContext(ctx, name, args...)
	cmd.Dir = r.root
	out, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("%s %v: %w", name, args, err)
	}
	return out, nil
}

func (r *repository) jj(ctx context.Context, args ...string) ([]byte, error) {
	return r.command(ctx, "jj", append([]string{"--ignore-working-copy", "--at-op=@"}, args...)...)
}

func (r *repository) git(ctx context.Context, args ...string) ([]byte, error) {
	return r.command(ctx, "git", append([]string{"--no-replace-objects", "--git-dir", r.gitDir}, args...)...)
}

func (r *repository) tip(ctx context.Context) (string, error) {
	// Use the same accepted identity as accepted.Enter, not the launch checkout,
	// an output revision, or a pending integration candidate.
	out, err := r.jj(ctx, "bookmark", "list", "-T", `if(!remote && normal_target && !normal_target.conflict(), normal_target.commit_id() ++ "\n")`, "--", "exact:"+strconv.Quote(r.target))
	if err != nil {
		return "", err
	}
	tip := strings.TrimSuffix(string(out), "\n")
	if !commitID(tip) {
		return "", fmt.Errorf("audit: no unambiguous local bookmark %q", r.target)
	}
	out, err = r.git(ctx, "rev-parse", "--verify", "refs/heads/"+r.target+"^{commit}")
	if err != nil {
		return "", err
	}
	if branch := strings.TrimSuffix(string(out), "\n"); branch != tip {
		return "", fmt.Errorf("audit: accepted target %q disagrees: jj %s, Git %s", r.target, tip, branch)
	}
	return tip, nil
}

func commitID(s string) bool {
	return (len(s) == 40 || len(s) == 64) && strings.Trim(s, "0123456789abcdef") == ""
}

func (r *repository) between(ctx context.Context, base, tip string) ([]string, error) {
	if !commitID(base) || !commitID(tip) {
		return nil, fmt.Errorf("audit: history endpoints must be full commit IDs")
	}
	if base == tip {
		return nil, ctx.Err()
	}
	out, err := r.git(ctx, "rev-list", "--first-parent", "--reverse", "--parents", base+".."+tip)
	if err != nil {
		return nil, err
	}
	var revs []string
	parent := base
	for line := range strings.SplitSeq(strings.TrimSuffix(string(out), "\n"), "\n") {
		fields := strings.Fields(line)
		if len(fields) != 2 || fields[1] != parent || !commitID(fields[0]) {
			return nil, fmt.Errorf("audit: not a linear accepted range %s..%s (at %q)", base, tip, line)
		}
		parent = fields[0]
		revs = append(revs, parent)
	}
	if parent != tip {
		return nil, fmt.Errorf("audit: accepted range %s..%s does not reach target", base, tip)
	}
	return revs, nil
}

type change struct{ status, path string }

func (r *repository) changes(ctx context.Context, parent, rev string) ([]change, error) {
	out, err := r.git(ctx, "diff-tree", "--no-commit-id", "--no-renames", "--ignore-submodules=none", "-r", "--name-status", "-z", parent, rev, "--")
	if err != nil || len(out) == 0 {
		return nil, err
	}
	parts := bytes.Split(out, []byte{0})
	if len(parts)%2 != 1 || len(parts[len(parts)-1]) != 0 {
		return nil, fmt.Errorf("audit: malformed changed paths at %s", rev)
	}
	var changes []change
	for i := 0; i+1 < len(parts); i += 2 {
		if len(parts[i]) != 1 || len(parts[i+1]) == 0 {
			return nil, fmt.Errorf("audit: malformed path/status at %s", rev)
		}
		changes = append(changes, change{string(parts[i]), string(parts[i+1])})
	}
	return changes, nil
}

func (r *repository) matchesNote(ctx context.Context, rev, path string, data []byte) (bool, error) {
	out, err := r.git(ctx, "ls-tree", "--full-tree", rev, "--", path)
	if err != nil || !bytes.HasPrefix(out, []byte("100644 blob ")) {
		return false, err
	}
	out, err = r.git(ctx, "cat-file", "blob", rev+":"+path)
	return bytes.Equal(out, data), err
}

func leanPath(path string) bool {
	return path == "Proofs" || strings.HasPrefix(path, "Proofs/") || strings.HasSuffix(path, ".lean") ||
		path == "lakefile.toml" || path == "lake-manifest.json" || path == "lean-toolchain"
}
