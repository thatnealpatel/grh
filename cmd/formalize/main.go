// Command formalize turns substantive Masullo Walk records into checked Lean work.
package main

import (
	"context"
	_ "embed"
	"encoding/json/v2"
	"errors"
	"fmt"
	"log"
	"os"
	"os/signal"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"patel.codes/godel"
	"patel.codes/grh/internal/accepted"
	grhgodel "patel.codes/grh/internal/godel"
)

const (
	batchCap  = 1
	idleDelay = 10 * time.Minute
)

//go:embed coordinator.md
var protocol string

func main() {
	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	if err := run(ctx); err != nil {
		log.Print(err)
		os.Exit(1)
	}
}

func run(ctx context.Context) error {
	if len(os.Args) != 1 {
		return errors.New("formalize takes no arguments; supply a nonblank seed on stdin for the first launch")
	}
	if err := accepted.Enter(ctx, "formalize"); err != nil {
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
	root := filepath.Join(source, "../..")
	home, err := os.UserHomeDir()
	if err != nil {
		return err
	}
	ledger, err := walkLedger(root, home)
	if err != nil {
		return err
	}
	repo, err := openRepository(ctx, root, os.Getenv("YAH_CAMPAIGN_TARGET"))
	if err != nil {
		return err
	}
	log.Printf("formalize target %q; reading Walk ledger %s", repo.target, ledger)
	var request string
	defer func() {
		if request != "" {
			os.Remove(request)
		}
	}()
	g := godel.New("Formalize individual Masullo passages from Walk with checked, independently reviewed campaign landings.")
	_, err = g.Run(ctx, &godel.Params{Node: startNode(ctx, repo, repo.tip, ledger, batchCap, &request), Loop: false, SelfImprove: nil})
	return err
}

type batch struct {
	Edition     string       `json:"edition"`
	Target      string       `json:"target"`
	AcceptedTip string       `json:"accepted_tip"`
	Assignments []assignment `json:"assignments"`
}

func startNode(ctx context.Context, repo repository, tip func(context.Context) (string, error), ledger string, limit int, request *string) *godel.Node {
	// Next holds Gödel's per-source lock, including idle waits. Walk uses a
	// different lock and publishes complete chapter files by atomic rename.
	return &godel.Node{Exec: "cat", Args: []string{"/dev/null"}, Next: func(godel.Result) (*godel.Node, error) {
		for ctx.Err() == nil {
			work, err := readWalk(ctx, ledger)
			if err != nil {
				return nil, err
			}
			if len(work) > 0 {
				base, err := tip(ctx)
				if err != nil {
					return nil, err
				}
				pending, err := repo.selectBatch(ctx, base, work, limit)
				if err != nil {
					return nil, err
				}
				if len(pending) > 0 {
					b := batch{edition, repo.target, base, pending}
					return coordinator(repo.root, b, request, func(godel.Result) (*godel.Node, error) {
						if err := os.Remove(*request); err != nil {
							return nil, err
						}
						*request = ""
						head, err := tip(ctx)
						if err != nil {
							return nil, err
						}
						return nil, repo.acknowledge(ctx, b, head)
					})
				}
			}
			if err := waitForWork(ctx); err != nil {
				return nil, err
			}
		}
		return nil, ctx.Err()
	}}
}

func waitForWork(ctx context.Context) error {
	t := time.NewTimer(idleDelay)
	defer t.Stop()
	select {
	case <-ctx.Done():
	case <-t.C:
	}
	return ctx.Err()
}

func coordinator(root string, b batch, request *string, next func(godel.Result) (*godel.Node, error)) (*godel.Node, error) {
	data, err := json.Marshal(b)
	if err != nil {
		return nil, fmt.Errorf("encode formalize batch: %w", err)
	}
	dir, err := filepath.Abs(os.TempDir())
	if err != nil {
		return nil, err
	}
	dir, err = filepath.EvalSymlinks(dir)
	if err != nil {
		return nil, err
	}
	rel, err := filepath.Rel(root, dir)
	if err != nil {
		return nil, err
	}
	if rel != ".." && !strings.HasPrefix(rel, ".."+string(filepath.Separator)) {
		return nil, errors.New("formalize batch temp directory must be outside the launch checkout")
	}
	f, err := os.CreateTemp(dir, "grh-formalize-*.json")
	if err != nil {
		return nil, err
	}
	*request = f.Name()
	_, err = f.Write(data)
	if err := errors.Join(err, f.Close()); err != nil {
		return nil, err
	}
	// Gödel normally passes its original stdin, possibly a recycled old
	// response. Replace it with a fixed seed. Only the fresh file is input.
	return &godel.Node{Directory: root, Exec: "sh", Next: next, Args: []string{
		"-c", `exec timeout --kill-after=30s 2h yah -yolo -effort high -append "$1" <<'SEED'
Process the supplied Formalize batch.
SEED`, "formalize-yah", protocol + "\n" + grhgodel.ScratchPolicy + "\n\nRead the fresh batch JSON at " + fmt.Sprintf("%q", *request) + ".",
	}}, nil
}
