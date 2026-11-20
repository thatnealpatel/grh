package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"strings"

	"patel.codes/grh/internal/landing"
	"patel.codes/grh/internal/mathlane"
	"patel.codes/grh/internal/source"
	"patel.codes/grh/internal/worker"
)

type lanes struct {
	source     func(context.Context, source.Passage) (source.Packet, error)
	translate  func(context.Context, string, string, string, string, string) (mathlane.Draft, error)
	challenge  func(context.Context, string, string, string, string, string, mathlane.Draft) (mathlane.Verdict, error)
	fidelity   func(context.Context, string, string, string, string, mathlane.Draft) (mathlane.Verdict, error)
	prove      func(context.Context, string, string, string, string, mathlane.Draft) (mathlane.Draft, error)
	land       func(context.Context, string, map[string]string, []string, string, func(context.Context, string, string, []string) error, func(context.Context, string) error, map[string]string) (string, error)
	check      func(context.Context, string, string, []string) error
	readLanded func(context.Context, string, string, map[string]string) error
}

var live = lanes{source: source.ReadPassage, translate: mathlane.Translate, fidelity: mathlane.Fidelity, challenge: reviewLanded, prove: mathlane.Prove, land: landing.LandReplacing, check: worker.Check, readLanded: landing.ReadLanded}

func compact(v any) string {
	b, err := json.Marshal(v)
	if err != nil {
		panic(err)
	}
	return string(b)
}
func (r *record) repair(reason string) {
	if r.ProofAttempt && r.Interface != nil {
		// A rejected proof is not permission to restate its accepted target.
		r.Block = "proof candidate rejected for fixed target " + r.Interface.Leaf + ": " + reason
		return
	}
	r.Critique = reason
	r.Repairs++
	r.Draft = nil
	r.Fidelity = nil
	r.Challenge = nil
	r.ProofAttempt = false
	r.Interface = nil
	r.InterfaceRevision = ""
	r.Stage = "translate"
	if r.Repairs >= 2 {
		r.Block = "interface repair limit: " + reason
	}
}
func (r *record) adopted(rev string) {
	r.Landed = r.Draft
	r.PendingAdoption = ""
	r.Revision = rev
	r.Stage = "challenge"
}
func (w *work) advance(ctx context.Context, r *record, l lanes) error {
	r.Block = ""
	r.Capability = ""
	q := w.plan.Goal + "\nObligation: " + r.Task.Question
	p := compact(r.Source)
	if r.Stage != "source" && (r.Source == nil || r.Source.Disposition != "verified") {
		return errors.New("missing verified source packet; no mathematical transition permitted")
	}
	switch r.Stage {
	case "source":
		packet, err := l.source(ctx, r.Task.Passage)
		if err != nil {
			return err
		}
		if strings.TrimSpace(packet.Anchor) == "" || strings.TrimSpace(packet.Boundary) == "" || strings.TrimSpace(packet.Attribution) == "" || strings.TrimSpace(packet.Reading) == "" || strings.TrimSpace(packet.Evidence[0]) == "" || strings.TrimSpace(packet.Evidence[1]) == "" {
			return errors.New("incomplete source packet")
		}
		switch packet.Disposition {
		case "verified":
			r.Stage = "translate"
		case "absent", "ambiguous":
			r.Block = packet.Disposition + ": " + packet.Boundary
		default:
			return fmt.Errorf("unknown disposition %q", packet.Disposition)
		}
		r.Source = &packet
	case "translate":
		d, err := l.translate(ctx, w.root, mission, q, p, r.Critique)
		if err != nil {
			return err
		}
		r.Draft = &d
		r.Stage = "fidelity"
	case "fidelity":
		if r.Draft == nil {
			return errors.New("missing draft")
		}
		v, err := l.fidelity(ctx, w.root, mission, q, p, *r.Draft)
		if err != nil {
			return err
		}
		if !v.Accept {
			r.repair(v.Reason)
			break
		}
		r.Fidelity = &v
		r.Stage = "land"
	case "land":
		if r.Draft == nil || r.Fidelity == nil || !r.Fidelity.Accept {
			return errors.New("cannot land without independently reviewed draft")
		}
		if r.PendingAdoption != "" {
			if err := l.readLanded(ctx, w.root, r.PendingAdoption, r.Draft.Files); err != nil {
				r.Block = "unreconciled adoption intent: " + err.Error()
				return nil
			}
			r.adopted(r.PendingAdoption)
			break
		}
		if r.ProofAttempt {
			if err := w.checkInterface(ctx, r, l); err != nil {
				return err
			}
		}
		desc := "Props: record the trace comparison premises"
		if r.ProofAttempt {
			desc = "Theorems: derive the trace comparison from both diagonal identities"
		}
		var previous map[string]string
		if r.Landed != nil {
			previous = r.Landed.Files
		}
		rev, err := l.land(ctx, w.root, r.Draft.Files, r.Draft.Decls, desc, l.check, func(_ context.Context, id string) error { r.PendingAdoption = id; return save(w.path(r.Task.ID), r) }, previous)
		if err != nil {
			return err
		}
		r.adopted(rev)
	case "challenge":
		if r.Revision == "" || r.Draft == nil {
			return errors.New("no landed draft")
		}
		if err := l.readLanded(ctx, w.root, r.Revision, r.Draft.Files); err != nil {
			return err
		}
		v, err := l.challenge(ctx, w.root, r.Revision, mission, q, p, *r.Draft)
		if err != nil {
			return err
		}
		if !v.Accept {
			r.repair(v.Reason)
			break
		}
		r.Challenge = &v
		if r.ProofAttempt || r.Draft.Leaf == "" {
			r.Stage = "checkpoint"
			if len(r.Draft.Premises) > 0 {
				r.Block = "checked conditional interface; remaining premises: " + strings.Join(r.Draft.Premises, "; ")
			}
			break
		}
		r.Interface = r.Draft
		r.InterfaceRevision = r.Revision
		r.Stage = "prove"
	case "prove":
		if err := w.checkInterface(ctx, r, l); err != nil {
			return err
		}
		d, err := l.prove(ctx, w.root, mission, q, p, *r.Interface)
		if errors.Is(err, mathlane.ErrProofNotReady) || errors.Is(err, mathlane.ErrRejected) {
			r.Block = "fixed target " + r.Interface.Leaf + ": " + err.Error()
			return nil
		}
		if err != nil {
			return fmt.Errorf("fixed target %s: %w", r.Interface.Leaf, err)
		}
		r.Draft = &d
		r.ProofAttempt = true
		r.Fidelity = nil
		r.Stage = "fidelity"
	default:
		return fmt.Errorf("unrecognized work stage %q", r.Stage)
	}
	return nil
}
func (w *work) checkInterface(ctx context.Context, r *record, l lanes) error {
	if r.Interface == nil || r.Interface.Leaf == "" || r.Challenge == nil || !r.Challenge.Accept {
		return errors.New("no accepted, challenged leaf type")
	}
	return l.readLanded(ctx, w.root, r.InterfaceRevision, r.Interface.Files)
}
func (w *work) step(ctx context.Context, l lanes) error {
	if err := ctx.Err(); err != nil {
		return err
	}
	// Charge before dispatch. An interrupted
	// landing may have side effects, unlike
	// a read-only review. Never replay it
	// blindly.
	if w.budget.Active != "" {
		for i := range w.records {
			r := &w.records[i]
			if r.Task.ID+"/"+r.Stage == w.budget.Active && r.Stage == "land" && r.PendingAdoption == "" {
				r.Block = "interrupted campaign operation before recorded adoption intent; inspect campaign before retry"
				if err := save(w.path(r.Task.ID), r); err != nil {
					return err
				}
			}
		}
		w.budget.Active = ""
		if err := save(w.budgetPath, w.budget); err != nil {
			return err
		}
	}
	if w.terminal() != "" {
		return nil
	}
	i := choose(w.records, selection)
	r := &w.records[i]
	w.budget.Active = r.Task.ID + "/" + r.Stage
	w.budget.Used++
	if err := save(w.budgetPath, w.budget); err != nil {
		return err
	}
	fmt.Fprintf(os.Stderr, "[%d/%d] %s: %s\n", w.budget.Used, w.budget.Limit, r.Task.ID, r.Stage)
	actionCtx, cancel := context.WithDeadline(ctx, w.budget.Deadline)
	defer cancel()
	err := w.advance(actionCtx, r, l)
	if ctx.Err() != nil {
		return ctx.Err()
	}
	if err != nil {
		if actionCtx.Err() != nil && r.PendingAdoption == "" {
			return nil
		}
		r.Block = err.Error()
		if !errors.Is(err, mathlane.ErrRejected) {
			r.Capability = capability(r.Stage)
		}
	}
	if err := save(w.path(r.Task.ID), r); err != nil {
		return err
	}
	w.budget.Active = ""
	return save(w.budgetPath, w.budget)
}
