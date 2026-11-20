package landing

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

const adapterEnv = "GRH_CAMPAIGN_ADAPTER"

type campaign struct {
	root, executable string
}

type request struct {
	Op          string     `json:"op"`
	Root        string     `json:"root"`
	On          string     `json:"on,omitempty"`
	Workspace   *workspace `json:"workspace,omitempty"`
	Outputs     []string   `json:"outputs,omitempty"`
	Description string     `json:"description,omitempty"`
	Candidate   string     `json:"candidate,omitempty"`
}

type workspace struct {
	Path       string `json:"path"`
	Base       string `json:"base"`
	Checkpoint string `json:"checkpoint"`
}

type output struct {
	Commit     string `json:"commit"`
	Workspace  string `json:"workspace"`
	Base       string `json:"base"`
	Conflicted *bool  `json:"conflicted"`
}

type integration struct {
	Status         string   `json:"status"`
	Base           string   `json:"base"`
	Inputs         []string `json:"inputs"`
	Behind         []string `json:"behind"`
	Candidate      string   `json:"candidate"`
	Replaces       string   `json:"replaces"`
	NothingToAdopt bool     `json:"nothing_to_adopt"`
	Adopted        bool     `json:"adopted"`
	Conflicted     *bool    `json:"conflicted"`
}

type adoption struct {
	Accepted string `json:"accepted"`
	Stale    *bool  `json:"stale"`
}

func openCampaign(root string) (campaign, error) {
	executable := os.Getenv(adapterEnv)
	if !filepath.IsAbs(executable) {
		return campaign{}, fmt.Errorf("landing: %s must name an absolute trusted campaign adapter executable (no public Yah campaign process API)", adapterEnv)
	}
	if _, err := exec.LookPath(executable); err != nil {
		return campaign{}, fmt.Errorf("landing: %s: %w", adapterEnv, err)
	}
	if root == "" {
		return campaign{}, errors.New("landing: empty repository root")
	}
	root, err := filepath.Abs(root)
	if err == nil {
		root, err = filepath.EvalSymlinks(root)
	}
	if err != nil {
		return campaign{}, fmt.Errorf("resolve repository root: %w", err)
	}
	return campaign{root: root, executable: executable}, nil
}

func (c campaign) call(ctx context.Context, in request, result any) error {
	in.Root = c.root
	data, err := json.Marshal(in)
	if err != nil {
		return fmt.Errorf("encode campaign %s: %w", in.Op, err)
	}
	cmd := exec.CommandContext(ctx, c.executable)
	cmd.Dir = c.root
	cmd.Stdin = bytes.NewReader(data)
	data, err = commandOutput(ctx, cmd)
	if err != nil {
		return fmt.Errorf("campaign %s: %w", in.Op, err)
	}
	if err := json.Unmarshal(data, result); err != nil {
		return fmt.Errorf("decode campaign %s: %w", in.Op, err)
	}
	return nil
}

func (c campaign) accepted(ctx context.Context) (string, error) {
	var status struct {
		Available   bool   `json:"available"`
		Unavailable string `json:"unavailable"`
		Accepted    string `json:"accepted"`
	}
	if err := c.call(ctx, request{Op: "status"}, &status); err != nil {
		return "", err
	}
	if !status.Available {
		return "", fmt.Errorf("campaign status unavailable: %s", status.Unavailable)
	}
	if !validRevision(status.Accepted) {
		return "", fmt.Errorf("campaign status did not return an exact accepted revision: %q", status.Accepted)
	}
	return status.Accepted, nil
}

func commandOutput(ctx context.Context, cmd *exec.Cmd) ([]byte, error) {
	cmd.WaitDelay = 2 * time.Second
	data, err := cmd.Output()
	if cause := ctx.Err(); cause != nil {
		err = errors.Join(err, cause)
	}
	if err != nil {
		if exit, ok := errors.AsType[*exec.ExitError](err); ok && len(exit.Stderr) != 0 {
			err = fmt.Errorf("%w: %s", err, strings.TrimSpace(string(exit.Stderr)))
		}
		return nil, err
	}
	return data, nil
}
