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
	"os/exec"
	"path"
	"strconv"
	"strings"
)

// The check is for this project's pinned
// toolchain, import roots and dependency
// graph. Changes to these build inputs
// require reviewing the worker gate too.
var configHashes = map[string]string{
	"lakefile.toml":      "19748e2651151fe3add8f56650403f7bc857955ffc6d0ec99a8abca0772a6e33",
	"lake-manifest.json": "7e840678c78bf915849e6a8e65b33fb5ab2efa3e12e387e4d1b21b376911181f",
	"lean-toolchain":     "582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a",
}

func archive(ctx context.Context, root, revision string, dst io.Writer) ([]string, error) {
	rev := `commit_id("` + revision + `")`
	jj := func(args ...string) ([]byte, error) {
		cmd := exec.CommandContext(ctx, "jj", append([]string{"--ignore-working-copy", "--color", "never"}, args...)...)
		cmd.Dir = root
		out, err := cmd.Output()
		if err != nil {
			var exit *exec.ExitError
			if errors.As(err, &exit) {
				return nil, fmt.Errorf("jj: %w (stderr %q)", errors.Join(ctx.Err(), err), tail(exit.Stderr))
			}
			return nil, errors.Join(ctx.Err(), err)
		}
		return out, nil
	}
	entries, err := jj("file", "list", "-r", rev, "-T", `file_type ++ "\0" ++ if(executable, "x", "-") ++ "\0" ++ path ++ "\0"`)
	if err != nil {
		return nil, err
	}
	tw := tar.NewWriter(dst)
	var modules []string
	var configs int
	fields := bytes.Split(entries, []byte{0})
	if len(fields)%3 != 1 || len(fields[len(fields)-1]) != 0 {
		return nil, errors.New("incomplete jj tree listing")
	}
	for i := 0; i+2 < len(fields); i += 3 {
		name := string(fields[i+2])
		if !fs.ValidPath(name) || name == "." || string(fields[i]) != "file" {
			return nil, fmt.Errorf("unsafe or non-regular candidate entry %q", name)
		}
		// Do not let an alternate Lake config
		// or prebuilt module replace a source
		// file from this revision. Project
		// modules must be built in clean
		// scratch.
		switch strings.Split(name, "/")[0] {
		case ".lake", ".jj", ".git", "lakefile.lean":
			return nil, fmt.Errorf("unexpected build input %q", name)
		}
		if ext := path.Ext(name); ext == ".olean" || ext == ".ilean" || ext == ".ir" || ext == ".so" || strings.Contains(name, ".olean.") {
			return nil, fmt.Errorf("precompiled input %q", name)
		}
		if strings.HasSuffix(name, ".lean") {
			rel, ok := strings.CutPrefix(name, "Proofs/")
			if !ok || !(strings.HasPrefix(rel, "Props/") || strings.HasPrefix(rel, "Lemmas/") || strings.HasPrefix(rel, "Theorems/")) {
				return nil, fmt.Errorf("module outside project import roots: %q", name)
			}
			rel = strings.TrimSuffix(rel, ".lean")
			mod := strings.ReplaceAll(rel, "/", ".")
			if strings.Contains(rel, ".") || !leanName.MatchString(mod) {
				return nil, fmt.Errorf("unsupported module path %q", name)
			}
			modules = append(modules, mod)
		}
		data, err := jj("file", "show", "-T", `path ++ "\0"`, "-r", rev, "root-file:"+strconv.Quote(name))
		if err != nil {
			return nil, fmt.Errorf("read %q: %w", name, err)
		}
		// An unmatched fileset can yield no bytes
		// without an error. Distinguish that case
		// from a selected file whose contents happen
		// to be empty.
		header, data, ok := bytes.Cut(data, []byte{0})
		if !ok || string(header) != name {
			return nil, fmt.Errorf("missing contents for %q", name)
		}
		if want, ok := configHashes[name]; ok {
			if fmt.Sprintf("%x", sha256.Sum256(data)) != want {
				return nil, fmt.Errorf("project pin changed: %s", name)
			}
			configs++
		}
		mode := int64(0644)
		if string(fields[i+1]) == "x" {
			mode = 0755
		}
		if err := tw.WriteHeader(&tar.Header{Name: name, Mode: mode, Size: int64(len(data))}); err != nil {
			return nil, err
		}
		if _, err := tw.Write(data); err != nil {
			return nil, err
		}
	}
	if configs != len(configHashes) {
		return nil, errors.New("missing pinned project configuration")
	}
	if len(modules) == 0 {
		return nil, errors.New("candidate has no project modules")
	}
	return modules, tw.Close()
}
