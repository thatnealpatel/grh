package main

import (
	"bufio"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// A bracket bounds when a complete
// journal record became observable, on
// the same monotonic clock as coordinator
// elapsed. Neither endpoint is a wall
// timestamp.
type bracket struct {
	Lo time.Duration `json:"lo_ns"`
	Hi time.Duration `json:"hi_ns"`
}

type dispatchObservation struct {
	Slug           string   `json:"slug"`
	Baseline       *bracket `json:"baseline,omitempty"`
	FirstAssistant *bracket `json:"first_assistant,omitempty"`
	LastAssistant  *bracket `json:"last_assistant,omitempty"`
	Terminal       *bracket `json:"terminal,omitempty"`
	Outcome        string   `json:"outcome,omitempty"`

	offset     int64
	absent     time.Duration
	incomplete bool
}

type observer struct {
	root     string
	start    time.Time
	session  string
	previous time.Duration
	byFile   map[string]*dispatchObservation
}

// Poll the pinned Yah child journals
// (not launch acknowledgments). Advance
// only over complete JSONL records; a
// short concurrent append is retried.
func (o *observer) poll() error {
	before := time.Since(o.start)
	sessions, err := os.ReadDir(o.root)
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	for _, s := range sessions {
		if s.Name() == "campaign.lock" && s.Type().IsRegular() {
			continue
		}
		if !s.IsDir() || (o.session != "" && s.Name() != o.session) {
			return errors.New("unexpected or additional session directory")
		}
		o.session = s.Name()
	}
	if o.session == "" {
		o.previous = before
		return nil
	}
	dir := filepath.Join(o.root, o.session, "agents")
	entries, err := os.ReadDir(dir)
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	seen := 0
	for _, f := range entries {
		if f.Type().IsRegular() && strings.HasSuffix(f.Name(), ".lock") {
			continue
		}
		seen++
		if seen > 3 || !f.Type().IsRegular() || !strings.HasSuffix(f.Name(), ".jsonl") {
			return errors.New("unexpected child journal entry")
		}
		d := o.byFile[f.Name()]
		if d == nil {
			d = &dispatchObservation{absent: o.previous}
			o.byFile[f.Name()] = d
		}
		if err := d.read(filepath.Join(dir, f.Name()), o.start); err != nil {
			return err
		}
	}
	if seen != len(o.byFile) {
		return errors.New("child journal disappeared")
	}
	o.previous = before
	return nil
}

func (d *dispatchObservation) read(path string, start time.Time) error {
	before := time.Since(start)
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	info, err := f.Stat()
	if err != nil {
		return err
	}
	if info.Size() < d.offset || info.Size() > 64<<20 {
		return errors.New("child journal truncated or exceeds 64 MiB observation limit")
	}
	if _, err := f.Seek(d.offset, io.SeekStart); err != nil {
		return err
	}
	r := bufio.NewReaderSize(io.LimitReader(f, info.Size()-d.offset), 1<<20)
	dispatch := strings.TrimSuffix(filepath.Base(path), ".jsonl")
	for {
		line, err := r.ReadSlice('\n')
		if err == io.EOF {
			d.incomplete = len(line) != 0
			d.absent = before
			return nil
		}
		if err != nil {
			return err
		}
		var rec struct {
			Type     string `json:"type"`
			Role     string `json:"role"`
			Slug     string `json:"slug"`
			Outcome  string `json:"outcome"`
			Build    string `json:"build"`
			Hostname string `json:"hostname"`
			Dispatch string `json:"dispatch"`
		}
		if err := json.Unmarshal(line, &rec); err != nil {
			return err
		}
		if d.offset == 0 {
			if rec.Type != "" || rec.Build == "" || rec.Hostname == "" || rec.Dispatch != dispatch {
				return errors.New("unexpected child journal header")
			}
		} else {
			b := &bracket{Lo: d.absent, Hi: time.Since(start)}
			if err := d.record(rec.Type, rec.Role, rec.Slug, rec.Outcome, b); err != nil {
				return err
			}
		}
		d.offset += int64(len(line))
	}
}

func (d *dispatchObservation) record(kind, role, slug, outcome string, b *bracket) error {
	if d.Terminal != nil || (d.Baseline == nil && kind != "dispatch_baseline") {
		return errors.New("record outside the fresh dispatch epoch")
	}
	switch kind {
	case "dispatch_baseline":
		if d.Baseline != nil || (slug != "writer-a" && slug != "writer-b" && slug != "statement-review") {
			return errors.New("unexpected dispatch baseline")
		}
		d.Slug, d.Baseline = slug, b
	case "message":
		if role == "assistant" {
			if d.FirstAssistant == nil {
				d.FirstAssistant = b
			}
			d.LastAssistant = b
		}
	case "dispatch_terminal":
		switch outcome {
		case "ok", "error", "timeout", "cancelled", "interrupted":
		default:
			return fmt.Errorf("unrecognized terminal outcome %q", outcome)
		}
		d.Outcome, d.Terminal = outcome, b
	case "dispatch_resume":
		return errors.New("unexpected dispatch resume")
	}
	return nil
}

func (o *observer) watch(done <-chan struct{}) error {
	ticker := time.NewTicker(time.Second)
	defer ticker.Stop()
	for {
		select {
		case <-done:
			return o.poll()
		case <-ticker.C:
			if err := o.poll(); err != nil {
				return err
			}
		}
	}
}

// Writer timing uses journal visibility, not inference or CPU time. The
// observed active window starts at the first evidence of execution, not at
// the baseline persisted before execution. Both windows end at terminal.
func writerTiming(a, b *dispatchObservation) (sessionSum, observedActiveSum, assistantOverlap *bracket) {
	if a == nil || b == nil {
		return nil, nil, nil
	}
	sessionSum = summedWindows(a.Baseline, a.Terminal, b.Baseline, b.Terminal)
	observedActiveSum = summedWindows(a.FirstAssistant, a.Terminal, b.FirstAssistant, b.Terminal)
	if a.FirstAssistant != nil && b.FirstAssistant != nil {
		assistantOverlap = &bracket{
			max(0, min(a.LastAssistant.Lo, b.LastAssistant.Lo)-max(a.FirstAssistant.Hi, b.FirstAssistant.Hi)),
			max(0, min(a.LastAssistant.Hi, b.LastAssistant.Hi)-max(a.FirstAssistant.Lo, b.FirstAssistant.Lo)),
		}
	}
	return sessionSum, observedActiveSum, assistantOverlap
}

func summedWindows(aStart, aEnd, bStart, bEnd *bracket) *bracket {
	if aStart == nil || bStart == nil || aEnd == nil || bEnd == nil {
		return nil
	}
	return &bracket{
		max(0, aEnd.Lo-aStart.Hi) + max(0, bEnd.Lo-bStart.Hi),
		aEnd.Hi - aStart.Lo + bEnd.Hi - bStart.Lo,
	}
}

func (o *observer) report(out io.Writer, elapsed time.Duration, watchErr error) error {
	dispatches := make(map[string]*dispatchObservation)
	for _, d := range o.byFile {
		if d.incomplete || d.Terminal == nil {
			watchErr = errors.Join(watchErr, fmt.Errorf("incomplete dispatch journal for %q", d.Slug))
		}
		if d.Slug == "" || dispatches[d.Slug] != nil {
			watchErr = errors.Join(watchErr, errors.New("missing or duplicate dispatch slug"))
			continue
		}
		dispatches[d.Slug] = d
	}
	receipt := struct {
		Elapsed          time.Duration                   `json:"elapsed_ns"`
		Session          string                          `json:"session"`
		Dispatches       map[string]*dispatchObservation `json:"dispatches"`
		Error            string                          `json:"observation_error,omitempty"`
		WriterSum        *bracket                        `json:"writer_session_sum,omitempty"`
		ActiveSum        *bracket                        `json:"writer_observed_active_sum,omitempty"`
		AssistantOverlap *bracket                        `json:"writer_assistant_span_overlap,omitempty"`
	}{Elapsed: elapsed, Session: o.session, Dispatches: dispatches}
	if watchErr != nil {
		receipt.Error = watchErr.Error()
	} else {
		receipt.WriterSum, receipt.ActiveSum, receipt.AssistantOverlap = writerTiming(dispatches["writer-a"], dispatches["writer-b"])
	}
	_, err := io.WriteString(out, "proofpair monotonic receipt: ")
	return errors.Join(watchErr, err, json.NewEncoder(out).Encode(receipt))
}
