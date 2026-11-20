package landing

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os/exec"
	"path/filepath"
	"strings"
)

// These tracked inputs define the Lean/Lake setup used by the worker. Their
// pins come from the accepted tree, not from the control working copy.
var setupPaths = []string{"lean-toolchain", "lakefile.toml", "lake-manifest.json"}

type tree struct {
	ctx       context.Context
	root, rev string
}

func (c campaign) tree(ctx context.Context, revision string) tree {
	return tree{ctx: ctx, root: c.root, rev: revision}
}

func (c campaign) verifyWorkspace(ctx context.Context, w workspace) error {
	path, err := filepath.EvalSymlinks(w.Path)
	if err != nil {
		return err
	}
	if !filepath.IsAbs(path) || path != w.Path || within(c.root, path) || within(path, c.root) {
		return fmt.Errorf("invalid isolated campaign workspace %q", w.Path)
	}
	root, err := jj(ctx, path, "workspace", "root")
	if err != nil {
		return err
	}
	if root != path+"\n" {
		return fmt.Errorf("expected a jj workspace rooted at %q", path)
	}
	rev, err := jj(ctx, path, "log", "--no-graph", "-r", "@", "-T", `commit_id ++ "\n"`)
	if err != nil {
		return err
	}
	if rev != w.Checkpoint+"\n" {
		return fmt.Errorf("workspace is not at prepared checkpoint %s", w.Checkpoint)
	}
	t := c.tree(ctx, w.Checkpoint)
	if err := t.checkCommit(w.Base); err != nil {
		return err
	}
	diff, err := t.diff(w.Base)
	if err != nil {
		return err
	}
	if diff != "" {
		return errors.New("prepared checkpoint differs from accepted base")
	}
	return nil
}

func within(parent, path string) bool {
	rel, err := filepath.Rel(parent, path)
	return err == nil && rel != ".." && !strings.HasPrefix(rel, ".."+string(filepath.Separator))
}

func validRevision(rev string) bool {
	return (len(rev) == 40 || len(rev) == 64) && strings.Trim(rev, "0123456789abcdef") == ""
}

func jj(ctx context.Context, root string, args ...string) (string, error) {
	cmd := exec.CommandContext(ctx, "jj", append([]string{"--ignore-working-copy", "--color=never", "--no-pager"}, args...)...)
	cmd.Dir = root
	data, err := commandOutput(ctx, cmd)
	if err != nil {
		return "", fmt.Errorf("inspect revision (jj %s): %w", args[0], err)
	}
	return string(data), nil
}

func (c campaign) checkAncestor(ctx context.Context, ancestor, descendant string) error {
	// The accepted head comes from campaign
	// status or adoption, not any local
	// bookmark or mutable checkout. Only
	// inspect immutable objects here.
	if len(ancestor) != len(descendant) {
		return fmt.Errorf("revisions %s and %s have different ID lengths", ancestor, descendant)
	}
	revset := commitID(ancestor) + " & ancestors(" + commitID(descendant) + ")"
	found, err := jj(ctx, c.root, "log", "--no-graph", "-r", revset, "-T", `commit_id ++ "\n"`)
	if err != nil {
		return err
	}
	if found != ancestor+"\n" {
		return fmt.Errorf("revision %s is not in accepted ancestry of %s", ancestor, descendant)
	}
	return nil
}

func commitID(id string) string { return `commit_id("` + id + `")` }

func (t tree) checkCommit(parent string) error {
	info, err := jj(t.ctx, t.root, "log", "--no-graph", "-r", commitID(t.rev), "-T", `commit_id ++ "\n" ++ conflict ++ "\n" ++ parents.map(|p| p.commit_id()).join("\n") ++ "\n"`)
	if err != nil {
		return err
	}
	id, rest, _ := strings.Cut(info, "\n")
	conflict, parents, _ := strings.Cut(rest, "\n")
	if id != t.rev || conflict != "false" {
		return fmt.Errorf("revision %s could not be resolved exactly and without conflicts", t.rev)
	}
	if parent != "" && parents != parent+"\n" {
		return fmt.Errorf("revision %s does not have %s as sole parent", t.rev, parent)
	}
	return nil
}

func (t tree) diff(base string) (string, error) {
	return jj(t.ctx, t.root, "diff", "--from", commitID(base), "--to", commitID(t.rev), "-T", `json(path) ++ "\t" ++ status ++ "\n"`)
}

func (t tree) checkBase(paths []string, previous map[string]string) error {
	if err := t.checkCommit(""); err != nil {
		return err
	}
	entries, err := t.entries(setupPaths)
	if err != nil {
		return err
	}
	for _, name := range setupPaths {
		if entries[name] != "file\tfalse" {
			return fmt.Errorf("missing or invalid pinned setup file %q", name)
		}
		content, err := t.content(name)
		if err != nil {
			return err
		}
		if strings.TrimSpace(content) == "" {
			return fmt.Errorf("empty pinned setup file %q", name)
		}
	}
	entries, err = t.entries(paths)
	if err != nil {
		return err
	}
	for _, name := range paths {
		old, replacing := previous[name]
		if replacing {
			if err := t.checkFile(entries, name, old); err != nil {
				return fmt.Errorf("verify accepted preimage: %w", err)
			}
		} else if _, exists := entries[name]; exists {
			return fmt.Errorf("proof path %q already exists at accepted base without authorized preimage", name)
		}
	}
	return nil
}

func (t tree) checkChange(base string, changed, paths []string, files, previous map[string]string) error {
	if err := t.checkCommit(base); err != nil {
		return err
	}
	diff, err := t.diff(base)
	if err != nil {
		return err
	}
	entries, err := parseRows(diff)
	if err != nil {
		return err
	}
	for _, name := range changed {
		want := "added"
		if _, ok := previous[name]; ok {
			want = "modified"
		}
		if status := entries[name]; status != want {
			return fmt.Errorf("diff for %q reports %q, want %q", name, status, want)
		}
		delete(entries, name)
	}
	for name := range entries {
		return fmt.Errorf("diff includes unauthorized path %q", name)
	}
	return t.checkFiles(paths, files)
}

func (t tree) entries(paths []string) (map[string]string, error) {
	args := []string{"file", "list", "-r", commitID(t.rev), "-T", `json(path) ++ "\t" ++ file_type ++ "\t" ++ executable ++ "\n"`, "--"}
	for _, name := range paths {
		args = append(args, filePath(name))
	}
	data, err := jj(t.ctx, t.root, args...)
	if err != nil {
		return nil, err
	}
	return parseRows(data)
}

func filePath(name string) string {
	// Literal fileset: no glob, revset, prefix match, or
	// option injection.
	return `file:"` + strings.ReplaceAll(name, `"`, `\"`) + `"`
}

func (t tree) content(name string) (string, error) {
	return jj(t.ctx, t.root, "file", "show", "-T", `""`, "-r", commitID(t.rev), "--", filePath(name))
}

func (t tree) checkFiles(paths []string, files map[string]string) error {
	entries, err := t.entries(paths)
	if err != nil {
		return err
	}
	for _, name := range paths {
		if err := t.checkFile(entries, name, files[name]); err != nil {
			return err
		}
	}
	return nil
}

func (t tree) checkFile(entries map[string]string, name, want string) error {
	if entries[name] != "file\tfalse" {
		return fmt.Errorf("%q is not a non-executable regular file", name)
	}
	content, err := t.content(name)
	if err != nil {
		return err
	}
	if content != want {
		return fmt.Errorf("unexpected contents of %q", name)
	}
	return nil
}

func parseRows(data string) (map[string]string, error) {
	result := make(map[string]string)
	for data != "" {
		line, rest, ended := strings.Cut(data, "\n")
		path, value, ok := strings.Cut(line, "\t")
		var name string
		if !ended || !ok || json.Unmarshal([]byte(path), &name) != nil || name == "" || value == "" {
			return nil, errors.New("invalid jj tree inspection output")
		}
		if _, exists := result[name]; exists {
			return nil, fmt.Errorf("duplicate path %q in jj tree inspection", name)
		}
		result[name] = value
		data = rest
	}
	return result, nil
}
