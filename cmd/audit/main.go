// Command audit independently reviews accepted GRH campaign progress.
package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"log"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"patel.codes/godel"
	"patel.codes/grh/internal/accepted"
)

func main() {
	baseline := flag.String("baseline", "", "full accepted ancestor commit to start after (required for a new journal)")
	flag.Parse()
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx, *baseline); err != nil {
		log.Print(err)
		os.Exit(1)
	}
}

func run(ctx context.Context, baseline string) error {
	if flag.NArg() != 0 || (baseline != "" && !commitID(baseline)) {
		return errors.New("audit accepts only -baseline with a full commit ID")
	}
	if err := accepted.Enter(ctx, "audit"); err != nil {
		return err
	}
	source, err := os.Getwd()
	if err != nil {
		return err
	}
	source, err = filepath.EvalSymlinks(source)
	if err != nil {
		return err
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return err
	}
	if !filepath.IsAbs(home) {
		return errors.New("audit requires an absolute home directory")
	}
	root := filepath.Join(source, "../..")
	repo, err := openRepository(ctx, root, os.Getenv("YAH_CAMPAIGN_TARGET"))
	if err != nil {
		return err
	}
	file := filepath.Join(home, ".grh-audit-"+digest([]byte(source))+".json")
	log.Printf("audit target %s; journal %s", repo.target, file)
	a := auditor{repo: repo, file: file, wait: waitForProgress}
	var scratch string
	defer func() { os.RemoveAll(scratch) }()
	artifact := func(name string, data []byte) (string, error) {
		if scratch == "" {
			var err error
			scratch, err = os.MkdirTemp("", "grh-audit-")
			if err != nil {
				return "", err
			}
		}
		path := filepath.Join(scratch, name)
		return path, os.WriteFile(path, data, 0600)
	}
	publish := func() (*godel.Node, error) {
		p := *a.state.Pending
		path, err := artifact("finding.md", p.note())
		if err != nil {
			return nil, err
		}
		instruction := fmt.Sprintf(publishPrompt, repo.target, p.Scope.Target, path, notePath(p.Scope.Target))
		return yah(root, instruction, func(r godel.Result) (*godel.Node, error) {
			if err := a.acceptPublication(ctx, r.Text); err != nil {
				return nil, err
			}
			return nil, os.RemoveAll(scratch)
		}), nil
	}
	// Next runs under Gödel's program lock. Ignore stdin (including recycled
	// responses) as authority; the cat only gives us a cheap Go entry point.
	node := &godel.Node{Exec: "cat", Next: func(godel.Result) (*godel.Node, error) {
		if err := a.load(identity{Source: source, Git: repo.gitDir, Target: repo.target}, baseline); err != nil {
			return nil, err
		}
		s, err := a.prepare(ctx)
		if err != nil {
			return nil, err
		}
		if s == nil {
			return publish()
		}
		request := struct {
			Scope scope     `json:"scope"`
			Open  []finding `json:"open_handoffs"`
		}{*s, a.state.Findings}
		path, err := artifact("request.json", encode(request))
		if err != nil {
			return nil, err
		}
		return yah(root, fmt.Sprintf(reviewPrompt, path), func(r godel.Result) (*godel.Node, error) {
			if err := a.acceptReview(ctx, *s, r.Text); err != nil {
				return nil, err
			}
			if a.state.Pending != nil {
				return publish()
			}
			return nil, os.RemoveAll(scratch)
		}), nil
	}}
	g := godel.New("Independently audit exact accepted GRH progress. Preserve evidence and unresolved findings without repairing proofs or controlling producers.")
	_, err = g.Run(ctx, &godel.Params{Node: node, Loop: true})
	return err
}

func waitForProgress(ctx context.Context) error {
	timer := time.NewTimer(10 * time.Minute)
	defer timer.Stop()
	select {
	case <-ctx.Done():
		return ctx.Err()
	case <-timer.C:
		return ctx.Err()
	}
}

func yah(root, instruction string, next func(godel.Result) (*godel.Node, error)) *godel.Node {
	return &godel.Node{
		Directory: root, Exec: "timeout", Next: next,
		Args: []string{"--kill-after=30s", "2h", "yah", "-yolo", "-effort", "high", "-append", instruction},
	}
}
