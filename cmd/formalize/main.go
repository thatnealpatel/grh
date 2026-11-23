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
	idleDelay = 10 * time.Minute

	selectionFile = "selection.json"
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
	var dispatchDir string
	defer func() {
		if dispatchDir != "" {
			os.RemoveAll(dispatchDir)
		}
	}()
	g := godel.New("Formalize individual Masullo passages from Walk with checked, independently reviewed campaign landings.")
	_, err = g.Run(ctx, &godel.Params{Node: startNode(ctx, repo, repo.tip, ledger, &dispatchDir), Loop: true, SelfImprove: nil})
	return err
}

type batch struct {
	Edition     string       `json:"edition"`
	Target      string       `json:"target"`
	AcceptedTip string       `json:"accepted_tip"`
	Primary     assignment   `json:"primary"`
	Offers      []assignment `json:"offers"`
}

func startNode(ctx context.Context, repo repository, tip func(context.Context) (string, error), ledger string, dispatchDir *string) *godel.Node {
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
				plan, err := repo.planBatch(ctx, base, work)
				if err != nil {
					return nil, err
				}
				if len(plan) > 0 {
					b := batch{edition, repo.target, base, plan[0], plan[1:]}
					return coordinator(repo.root, b, dispatchDir, func(selected []assignment) error {
						if err := ctx.Err(); err != nil {
							return err
						}
						head, err := tip(ctx)
						if err != nil {
							return err
						}
						return repo.acknowledge(ctx, selected, head)
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

// readSelection reads the coordinator's predispatch choice, not
// its final report. The selection is disposable; only accepted
// receipts survive restart.
func (b batch) readSelection(file string) ([]assignment, error) {
	info, err := os.Lstat(file)
	if err != nil {
		return nil, fmt.Errorf("read formalize selection: %w", err)
	}
	if !info.Mode().IsRegular() || info.Size() > 1024 {
		return nil, errors.New("formalize selection must be a regular JSON file of at most 1024 bytes")
	}
	data, err := os.ReadFile(file)
	if err != nil {
		return nil, fmt.Errorf("read formalize selection: %w", err)
	}
	var paths []string
	if err := json.Unmarshal(data, &paths); err != nil {
		return nil, fmt.Errorf("invalid formalize selection: %w", err)
	}
	if len(paths) < 1 || len(paths) > 2 || paths[0] != b.Primary.path() {
		return nil, errors.New("formalize selection must name the primary first and at most one optional offer")
	}
	if len(paths) == 1 {
		return []assignment{b.Primary}, nil
	}
	for _, offer := range b.Offers {
		if offer.Key != b.Primary.Key && offer.path() == paths[1] {
			return []assignment{b.Primary, offer}, nil
		}
	}
	return nil, fmt.Errorf("formalize selection is not a distinct offered passage/lane: %q", paths[1])
}

func coordinator(root string, b batch, dispatchDir *string, acknowledge func([]assignment) error) (*godel.Node, error) {
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
	dispatch, err := os.MkdirTemp(dir, "grh-formalize-*")
	if err != nil {
		return nil, err
	}
	*dispatchDir = dispatch
	request := filepath.Join(dispatch, "request.json")
	if err := os.WriteFile(request, data, 0600); err != nil {
		return nil, err
	}
	selection := filepath.Join(dispatch, selectionFile)
	// Gödel normally passes its original stdin, possibly a recycled
	// old response. Replace it with a fixed seed. Only the fresh
	// request is input.
	return &godel.Node{Directory: root, Exec: "sh", Args: []string{
		"-c", `exec timeout --kill-after=30s 2h yah -yolo -effort high -append "$1" <<'SEED'
Process the supplied Formalize batch.
SEED`, "formalize-yah", protocol + "\n" + grhgodel.ScratchPolicy + fmt.Sprintf("\n\nRead the fresh batch JSON at %q. Bind selection at %q.", request, selection),
	}, Next: func(godel.Result) (*godel.Node, error) {
		selected, err := b.readSelection(selection)
		if cleanupErr := os.RemoveAll(dispatch); cleanupErr != nil {
			return nil, errors.Join(err, cleanupErr)
		}
		*dispatchDir = ""
		if err != nil {
			return nil, err
		}
		return nil, acknowledge(selected)
	}}, nil
}
