// Package landing checks exact campaign revisions before allowing adoption.
package landing

import (
	"context"
	"errors"
	"fmt"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"unicode"
)

// Land adds the authorized proof files to the accepted target after checking
// both the finalized output and the integrated candidate. check must check the
// given immutable revision in an isolated worker, not the root working copy.
func Land(ctx context.Context, root string, files map[string]string, decls []string, description string, check func(context.Context, string, string, []string) error) (string, error) {
	return LandWithIntent(ctx, root, files, decls, description, check, nil)
}

// LandWithIntent calls beforeAdopt with the exact checked candidate immediately
// before requesting adoption. A caller can durably record the revision there
// for reconciliation with ReadLanded if the outcome is not confirmed.
func LandWithIntent(ctx context.Context, root string, files map[string]string, decls []string, description string, check func(context.Context, string, string, []string) error, beforeAdopt func(context.Context, string) error) (string, error) {
	return LandReplacing(ctx, root, files, decls, description, check, beforeAdopt, nil)
}

// LandReplacing is like LandWithIntent but permits replacing proof files whose
// exact accepted contents match their entries in previous. Any path not in
// previous must be absent from the accepted base.
func LandReplacing(ctx context.Context, root string, files map[string]string, decls []string, description string, check func(context.Context, string, string, []string) error, beforeAdopt func(context.Context, string) error, previous map[string]string) (string, error) {
	if check == nil {
		return "", errors.New("landing: missing exact-revision worker check")
	}
	if strings.TrimSpace(description) == "" {
		return "", errors.New("landing: empty integration description")
	}
	for _, line := range strings.Split(description, "\n") {
		if strings.HasPrefix(strings.TrimSpace(line), "Change-Id:") {
			return "", errors.New("landing: Change-Id trailers can replace unrelated pending attempts")
		}
	}
	files, decls, previous = maps.Clone(files), slices.Clone(decls), maps.Clone(previous)
	paths, err := proofPaths(files)
	if err != nil {
		return "", err
	}
	for name := range previous {
		if _, ok := files[name]; !ok {
			return "", fmt.Errorf("landing: preimage for unauthorized path %q", name)
		}
	}
	var changed []string
	for _, name := range paths {
		if old, ok := previous[name]; !ok || old != files[name] {
			changed = append(changed, name)
		}
	}
	if len(changed) == 0 {
		return "", errors.New("landing: no changes to integrate")
	}
	c, err := openCampaign(root)
	if err != nil {
		return "", err
	}
	base, err := c.accepted(ctx)
	if err != nil {
		return "", err
	}
	if err := c.tree(ctx, base).checkBase(paths, previous); err != nil {
		return "", fmt.Errorf("verify accepted base: %w", err)
	}
	var w workspace
	if err := c.call(ctx, request{Op: "prepare", On: base}, &w); err != nil {
		return "", err
	}
	if w.Base != base || !validRevision(w.Checkpoint) {
		return "", errors.New("landing: prepare returned an invalid checkpoint or a different base")
	}
	if err := c.verifyWorkspace(ctx, w); err != nil {
		return "", fmt.Errorf("verify prepared workspace: %w", err)
	}
	if err := ctx.Err(); err != nil {
		return "", err
	}
	if err := stage(w.Path, changed, files, previous); err != nil {
		return "", fmt.Errorf("stage campaign output: %w", err)
	}
	var out output
	if err := c.call(ctx, request{Op: "finalize", Workspace: &w}, &out); err != nil {
		return "", err
	}
	if out.Base != base || out.Workspace != w.Path || !validRevision(out.Commit) || out.Conflicted == nil || *out.Conflicted {
		return "", errors.New("landing: invalid or conflicted finalized campaign output")
	}
	if err := c.tree(ctx, out.Commit).checkChange(base, changed, paths, files, previous); err != nil {
		return "", fmt.Errorf("verify finalized output: %w", err)
	}
	if err := check(ctx, c.root, out.Commit, slices.Clone(decls)); err != nil {
		return "", fmt.Errorf("check finalized output %s: %w", out.Commit, err)
	}

	var attempt integration
	if err := c.call(ctx, request{Op: "integrate", On: base, Outputs: []string{out.Commit}, Description: description}, &attempt); err != nil {
		return "", err
	}
	candidate := attempt.Candidate
	if attempt.Status != "pending" || attempt.Replaces != "" || attempt.NothingToAdopt || attempt.Adopted || attempt.Conflicted == nil || *attempt.Conflicted ||
		attempt.Base != base || !validRevision(candidate) || !slices.Equal(attempt.Inputs, []string{out.Commit}) || len(attempt.Behind) != 0 {
		return "", errors.New("landing: integration did not return a clean pending candidate for the exact output and base")
	}
	if err := c.tree(ctx, candidate).checkChange(base, changed, paths, files, previous); err != nil {
		return "", fmt.Errorf("verify integrated candidate: %w", err)
	}
	if err := check(ctx, c.root, candidate, slices.Clone(decls)); err != nil {
		return "", fmt.Errorf("check integrated candidate %s: %w", candidate, err)
	}
	current, err := c.accepted(ctx)
	if err != nil {
		return "", err
	}
	if current != base {
		return "", fmt.Errorf("landing: stale integration base %s (accepted %s)", base, current)
	}
	if beforeAdopt != nil {
		if err := beforeAdopt(ctx, candidate); err != nil {
			return "", fmt.Errorf("record adoption intent for %s: %w", candidate, err)
		}
	}
	if err := c.adopt(ctx, candidate, paths, files); err != nil {
		return "", err
	}
	return candidate, nil
}

// ReadLanded verifies that revision is accepted or is an ancestor of the
// accepted target, and that the exact anchored files are retained there.
func ReadLanded(ctx context.Context, root, revision string, files map[string]string) error {
	if !validRevision(revision) {
		return fmt.Errorf("landing: invalid anchored revision %q", revision)
	}
	paths, err := proofPaths(files)
	if err != nil {
		return err
	}
	c, err := openCampaign(root)
	if err != nil {
		return err
	}
	return c.readLanded(ctx, revision, paths, files)
}

func (c campaign) readLanded(ctx context.Context, revision string, paths []string, files map[string]string) error {
	accepted, err := c.accepted(ctx)
	if err != nil {
		return err
	}
	if err := c.checkAncestor(ctx, revision, accepted); err != nil {
		return err
	}
	if err := c.tree(ctx, revision).checkFiles(paths, files); err != nil {
		return fmt.Errorf("verify anchored revision %s: %w", revision, err)
	}
	if accepted != revision {
		if err := c.tree(ctx, accepted).checkFiles(paths, files); err != nil {
			return fmt.Errorf("verify retained files at accepted revision %s: %w", accepted, err)
		}
	}
	return nil
}

func (c campaign) adopt(ctx context.Context, candidate string, paths []string, files map[string]string) error {
	var result adoption
	if err := c.call(ctx, request{Op: "adopt", Candidate: candidate}, &result); err != nil {
		return fmt.Errorf("adoption of %s unconfirmed: %w", candidate, err)
	}
	if result.Stale == nil || !validRevision(result.Accepted) {
		return fmt.Errorf("adoption of %s unconfirmed: invalid campaign acknowledgment", candidate)
	}
	if *result.Stale {
		return fmt.Errorf("adoption of %s is stale (accepted %s)", candidate, result.Accepted)
	}
	if err := c.checkAncestor(ctx, candidate, result.Accepted); err != nil {
		return fmt.Errorf("adoption of %s unconfirmed: %w", candidate, err)
	}
	if err := c.readLanded(ctx, candidate, paths, files); err != nil {
		return fmt.Errorf("adoption of %s unconfirmed: %w", candidate, err)
	}
	return nil
}

func proofPaths(files map[string]string) ([]string, error) {
	if len(files) == 0 {
		return nil, errors.New("landing: no authorized proof files")
	}
	paths := slices.Sorted(maps.Keys(files))
	for _, name := range paths {
		if !fs.ValidPath(name) || !strings.HasPrefix(name, "Proofs/") || !strings.HasSuffix(name, ".lean") ||
			strings.ContainsRune(name, '\\') || strings.ContainsFunc(name, unicode.IsControl) {
			return nil, fmt.Errorf("landing: invalid proof path %q", name)
		}
		for _, part := range strings.Split(name, "/") {
			if strings.EqualFold(part, ".jj") || strings.EqualFold(part, ".git") {
				return nil, fmt.Errorf("landing: invalid proof path %q", name)
			}
		}
	}
	return paths, nil
}

func stage(workspace string, paths []string, files, previous map[string]string) error {
	root, err := os.OpenRoot(workspace)
	if err != nil {
		return err
	}
	defer root.Close()
	for _, name := range paths {
		dir := ""
		for _, part := range strings.Split(filepath.Dir(name), string(filepath.Separator)) {
			dir = filepath.Join(dir, part)
			info, err := root.Lstat(dir)
			if errors.Is(err, fs.ErrNotExist) {
				if err := root.Mkdir(dir, 0o755); err != nil {
					return err
				}
			} else if err != nil {
				return err
			} else if !info.IsDir() {
				return fmt.Errorf("workspace path %q is not a real directory", dir)
			}
		}
		if old, replacing := previous[name]; replacing {
			info, err := root.Lstat(name)
			if err != nil {
				return err
			}
			if !info.Mode().IsRegular() || info.Mode().Perm()&0o111 != 0 {
				return fmt.Errorf("workspace preimage %q is not a non-executable regular file", name)
			}
			content, err := root.ReadFile(name)
			if err != nil {
				return err
			}
			if string(content) != old {
				return fmt.Errorf("workspace preimage changed for %q", name)
			}
			if err := root.Remove(name); err != nil {
				return err
			}
		}
		file, err := root.OpenFile(name, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o644)
		if err != nil {
			return err
		}
		_, err = file.WriteString(files[name])
		if err := errors.Join(err, file.Close()); err != nil {
			return err
		}
	}
	return nil
}
