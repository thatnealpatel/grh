package main

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json/jsontext"
	"encoding/json/v2"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// Walk owns the chapter format (cmd/walk/store.go) and its forward order.
const edition = "e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5"

const noteDir = ".godel/formalize"

type passage struct {
	Kind        string `json:"kind"`
	Locator     string `json:"locator"`
	PrintedPage int    `json:"printed_page"`
}

type assignment struct {
	Chapter  string         `json:"chapter"`
	Key      string         `json:"key"`
	Revision string         `json:"revision"`
	Record   jsontext.Value `json:"record"`
}

func (a assignment) path() string { return noteDir + "/" + a.Key + "-" + a.Revision + ".json" }

func digest(data []byte) string {
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:])
}

func walkLedger(root, home string) (string, error) {
	if !filepath.IsAbs(home) {
		return "", errors.New("formalize requires an absolute home directory")
	}
	source, err := filepath.EvalSymlinks(filepath.Join(root, "cmd", "walk"))
	if err != nil {
		return "", err
	}
	return filepath.Join(home, ".grh-walk-"+digest([]byte(source))), nil
}

func readWalk(ctx context.Context, dir string) ([]assignment, error) {
	var sections []string
	for i := 1; i <= 14; i++ {
		sections = append(sections, fmt.Sprintf("chapter-%02d", i))
	}
	for id := 'a'; id <= 'e'; id++ {
		sections = append(sections, fmt.Sprintf("appendix-%c", id))
	}
	var work []assignment
	for _, id := range sections {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		path := filepath.Join(dir, id+".json")
		data, err := os.ReadFile(path)
		if errors.Is(err, os.ErrNotExist) {
			continue
		}
		if err != nil {
			return nil, err
		}
		work, err = appendChapter(work, id, data)
		if err != nil {
			return nil, fmt.Errorf("read %s: %w", path, err)
		}
	}
	return work, nil
}

func appendChapter(work []assignment, id string, data []byte) ([]assignment, error) {
	var c struct {
		Edition string           `json:"edition"`
		Chapter string           `json:"chapter"`
		Records []jsontext.Value `json:"records"`
	}
	if err := json.Unmarshal(data, &c); err != nil {
		return nil, err
	}
	if c.Edition != edition || c.Chapter != id {
		return nil, errors.New("chapter or edition mismatch")
	}
	seen := make(map[passage]bool)
	for _, raw := range c.Records {
		// Decode scheduling fields only.
		// Preserve Walk's full handoff rather
		// than projecting a second schema for
		// references and dependencies.
		var r struct {
			Passage passage `json:"passage"`
			Printed string  `json:"printed_finding"`
			Formal  struct {
				Status string `json:"status"`
			} `json:"formal"`
		}
		if err := json.Unmarshal(raw, &r); err != nil {
			return nil, err
		}
		p := r.Passage
		if p.Kind == "" || p.Locator == "" || p.PrintedPage <= 0 || seen[p] {
			return nil, fmt.Errorf("invalid or repeated passage: %+v", p)
		}
		seen[p] = true
		switch r.Formal.Status {
		case "not_applicable":
			continue
		case "open", "established", "refuted":
			if strings.TrimSpace(r.Printed) == "" {
				return nil, fmt.Errorf("empty finding for %+v", p)
			}
		default:
			return nil, fmt.Errorf("unknown Walk status %q for %+v", r.Formal.Status, p)
		}
		identity, err := json.Marshal([]any{edition, id, p.Kind, p.Locator, p.PrintedPage})
		if err != nil {
			return nil, err
		}
		if err := raw.Canonicalize(jsontext.CanonicalizeRawInts(false)); err != nil {
			return nil, err
		}
		work = append(work, assignment{id, digest(identity), digest(raw), raw})
	}
	return work, nil
}
