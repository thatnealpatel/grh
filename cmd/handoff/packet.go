package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"unicode/utf8"
)

const maxPacketBytes = 80 << 10

type plan struct {
	Train   selection `json:"train"`
	HeldOut selection `json:"held_out"`
}

type selection struct {
	Commit   string   `json:"commit"`
	Area     string   `json:"area"`
	Handoff  string   `json:"handoff"`
	Evidence []string `json:"evidence"`
}

var (
	commitID = regexp.MustCompile(`^([0-9a-f]{40}|[0-9a-f]{64})$`)
	areaID   = regexp.MustCompile(`^[a-z][a-z0-9_-]{0,47}$`)
	filePath = regexp.MustCompile(`^[a-zA-Z0-9_./-]{1,255}$`)
)

func (p plan) validate() error {
	if p.Train.Area == p.HeldOut.Area || p.Train.Commit == p.HeldOut.Commit {
		return errors.New("preselect different commit IDs and manuscript areas")
	}
	for _, s := range []selection{p.Train, p.HeldOut} {
		if !commitID.MatchString(s.Commit) || !areaID.MatchString(s.Area) {
			return errors.New("need full lowercase commit IDs and short manuscript area slugs")
		}
		if len(s.Evidence) == 0 || len(s.Evidence) > 8 {
			return fmt.Errorf("%s: select one to eight supporting artifacts", s.Area)
		}
		seen := make(map[string]bool)
		for _, name := range s.paths() {
			if !filePath.MatchString(name) || !filepath.IsLocal(name) || path.Clean(name) != name || name == "." || seen[name] {
				return fmt.Errorf("%s: invalid or repeated tracked path %q", s.Area, name)
			}
			seen[name] = true
		}
	}
	return nil
}

func (s selection) paths() []string { return append([]string{s.Handoff}, s.Evidence...) }

type packet struct {
	selection
	Files map[string]string `json:"files"`
}

func launchRoot(ctx context.Context) (string, error) {
	cwd, err := os.Getwd()
	if err != nil {
		return "", err
	}
	out, err := jj(ctx, cwd, "workspace", "root").Output()
	if err != nil {
		return "", fmt.Errorf("resolve launch workspace: %w", err)
	}
	root := strings.TrimSuffix(string(out), "\n")
	if filepath.Join(root, "cmd/handoff") != cwd {
		return "", errors.New("launch from the workspace's cmd/handoff directory for separate Gödel registration")
	}
	return root, nil
}

func jj(ctx context.Context, dir string, args ...string) *exec.Cmd {
	cmd := exec.CommandContext(ctx, "jj", append([]string{"--ignore-working-copy", "--at-op=@", "--no-pager", "--color=never"}, args...)...)
	cmd.Dir, cmd.Stderr = dir, os.Stderr
	return cmd
}

func loadPacket(ctx context.Context, root string, s selection) (packet, error) {
	rev := fmt.Sprintf(`commit_id(%q)`, s.Commit)
	fileset := func(name string) string { return fmt.Sprintf(`root-file:%q`, name) }
	paths := s.paths()
	args := []string{"file", "list", "-r", rev, "-T", `if(file_type == "file" && !conflict, path ++ "\n")`, "--"}
	for _, name := range paths {
		args = append(args, fileset(name))
	}
	listed, err := jj(ctx, root, args...).Output()
	if err != nil {
		return packet{}, err
	}
	p := packet{selection: s, Files: make(map[string]string)}
	remaining := maxPacketBytes
	for _, name := range paths {
		if !slices.Contains(strings.Split(string(listed), "\n"), name) {
			return packet{}, fmt.Errorf("%q is not an unconflicted tracked regular file at %s", name, s.Commit)
		}
		cmd := jj(ctx, root, "file", "show", "-r", rev, "--", fileset(name))
		pipe, err := cmd.StdoutPipe()
		if err != nil {
			return packet{}, err
		}
		if err = cmd.Start(); err != nil {
			return packet{}, err
		}
		data, err := io.ReadAll(io.LimitReader(pipe, int64(remaining)+1))
		// Close before Wait even on overflow so
		// jj cannot block writing the excess.
		pipe.Close()
		waitErr := cmd.Wait()
		if len(data) > remaining {
			return packet{}, fmt.Errorf("packet exceeds %d bytes at %q", maxPacketBytes, name)
		}
		if err := errors.Join(err, waitErr); err != nil {
			return packet{}, fmt.Errorf("read %q: %w", name, err)
		}
		if !utf8.Valid(data) || strings.ContainsRune(string(data), 0) || strings.TrimSpace(string(data)) == "" {
			return packet{}, fmt.Errorf("%q must be nonempty UTF-8 text without NULs", name)
		}
		p.Files[name] = string(data)
		remaining -= len(data)
	}
	encoded, err := json.Marshal(p)
	if err != nil {
		return packet{}, err
	}
	if len(encoded) > maxPacketBytes {
		return packet{}, fmt.Errorf("encoded packet exceeds %d bytes", maxPacketBytes)
	}
	return p, nil
}
