package main

import (
	"bytes"
	"context"
	"errors"
	"flag"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestParseArm(t *testing.T) {
	for _, tt := range []struct {
		args []string
		want arm
		help bool
	}{
		{args: []string{"-arm", "sequential"}, want: sequential},
		{args: []string{"-arm=concurrent"}, want: concurrent},
		{args: []string{"-h"}, help: true},
		{args: nil},
		{args: []string{"-arm", "parallel"}},
		{args: []string{"-arm", "sequential", "/other/checkout"}},
		{args: []string{"-revision", "other"}},
	} {
		got, err := parseArm(tt.args, io.Discard)
		if got != tt.want || (err == nil) != (tt.want != "") || errors.Is(err, flag.ErrHelp) != tt.help {
			t.Errorf("parseArm(%q) = %q, %v; want %q, help=%v", tt.args, got, err, tt.want, tt.help)
		}
	}
}

func TestRoutingRejectedBeforeLaunch(t *testing.T) {
	for _, v := range []string{"GIT_WORK_TREE", "GIT_CONFIG_PARAMETERS", "JJ_CONFIG", "YAH_CAMPAIGN_TARGET"} {
		t.Run(v, func(t *testing.T) {
			t.Setenv(v, "") // Even an empty override is not an admitted invocation.
			err := runArm(sequential, io.Discard, io.Discard, func(checkout, string, io.Writer, io.Writer) error {
				t.Fatal("started after routing rejection")
				return nil
			})
			if err == nil || !strings.Contains(err.Error(), "routing/configuration variable") {
				t.Fatalf("want routing rejection, got %v", err)
			}
		})
	}
}

func TestSnapshotRejectsAlternateMetadata(t *testing.T) {
	for _, tt := range []struct{ path, want string }{
		{".jj/repo", "must not exist"},
		{".git", "real directory"},
		{".git/objects/info/alternates", "unexpected Git metadata"},
		{".git/logs/HEAD", "unexpected Git metadata"},
	} {
		t.Run(tt.path, func(t *testing.T) {
			root := t.TempDir()
			put(t, filepath.Join(root, tt.path), "alternate")
			c := checkout{root: root}
			if err := c.checkSnapshot(context.Background(), baseTree); err == nil || !strings.Contains(err.Error(), tt.want) {
				t.Fatalf("want %q, got %v", tt.want, err)
			}
		})
	}
}

func TestOperatorPathRejectsShadowGit(t *testing.T) {
	dir := t.TempDir()
	for _, name := range []string{"godel-base", "jj", "lake", "pdftotext", "proofpair", "yah"} {
		if err := os.WriteFile(filepath.Join(dir, name), nil, 0555); err != nil {
			t.Fatal(err)
		}
	}
	if err := checkBinDir(dir); err != nil {
		t.Fatal(err)
	}
	put(t, filepath.Join(dir, "git"), "shadowed PATH")
	if err := checkBinDir(dir); err == nil {
		t.Fatal("accepted alternate git routing")
	}
}

func TestServiceProperties(t *testing.T) {
	want := map[string]string{"MainPID": "123", "KillMode": "control-group"}
	for _, tt := range []struct {
		data string
		ok   bool
	}{
		{"MainPID=123\nKillMode=control-group\n", true},
		{"MainPID=123\nKillMode=process\n", false},
		{"MainPID=456\nKillMode=control-group\n", false},
		{"MainPID=123\n", false},
		{"MainPID=123\nMainPID=123\nKillMode=control-group\n", false},
	} {
		if err := checkProperties(want, tt.data); (err == nil) != tt.ok {
			t.Errorf("checkProperties(%q) = %v, want success=%v", tt.data, err, tt.ok)
		}
	}
}

func TestSeedAndPrompt(t *testing.T) {
	seed := seedFor(baseTree)
	if seed != "4c0ccd361d70957dc93ec9be3cc109fb3362458a" {
		t.Fatalf("unexpected synthetic seed %s", seed)
	}
	a, b := prompt(sequential, seed), prompt(concurrent, seed)
	for _, brief := range []string{writerA, writerB, reviewBrief} {
		if strings.Count(a, brief) != 1 || strings.Count(b, brief) != 1 {
			t.Fatal("same brief must occur once per arm")
		}
	}
	if a == b || !strings.Contains(a, "before attempting writer-b") || !strings.Contains(b, "immediately writer-b") {
		t.Fatal("expected distinct scheduling instructions")
	}
}

func TestObserverPartialTerminal(t *testing.T) {
	root := t.TempDir()
	put(t, filepath.Join(root, "campaign.lock"), "")
	file := filepath.Join(root, "session", "agents", "id.jsonl")
	put(t, filepath.Join(filepath.Dir(file), "id.lock"), "")
	const prefix = `{"build":"test","hostname":"test","dispatch":"id"}` + "\n" +
		`{"seq":1,"type":"dispatch_baseline","slug":"writer-a"}` + "\n" +
		`{"seq":2,"type":"message","role":"user","msg":{"role":"user","text":"task"}}` + "\n" +
		`{"seq":3,"type":"message","role":"assistant","msg":{"role":"assistant","text":"reply"}}` + "\n"
	const partial = `{"type":"dispatch_terminal","outcome":"timeout"}`
	put(t, file, prefix+partial)
	o := observer{root: root, start: time.Now(), byFile: make(map[string]*dispatchObservation)}
	if err := o.poll(); err != nil {
		t.Fatal(err)
	}
	d := o.byFile["id.jsonl"]
	if d == nil || d.Baseline == nil || d.FirstAssistant == nil || d.Terminal != nil {
		t.Fatalf("expected partial record to remain unread: %+v", d)
	}
	var buf bytes.Buffer
	if err := o.report(&buf, time.Since(o.start), nil); err == nil || !strings.Contains(buf.String(), "incomplete dispatch journal") {
		t.Fatalf("missing evidence not reported: %v, %s", err, &buf)
	}
	buf.Reset()
	put(t, file, prefix+partial+"\n")
	if err := o.poll(); err != nil {
		t.Fatal(err)
	}
	if err := o.report(&buf, time.Since(o.start), nil); err != nil {
		t.Fatal(err)
	}
	if d.Outcome != "timeout" || d.Terminal == nil || !strings.Contains(buf.String(), `"outcome":"timeout"`) || strings.Contains(buf.String(), "writer_session_sum") {
		t.Fatalf("unexpected incomplete receipt: %s", &buf)
	}
}

func TestWriterTiming(t *testing.T) {
	a := &dispatchObservation{Baseline: &bracket{1, 2}, FirstAssistant: &bracket{3, 4}, LastAssistant: &bracket{12, 13}, Terminal: &bracket{14, 16}}
	b := &dispatchObservation{Baseline: &bracket{4, 5}, FirstAssistant: &bracket{6, 7}, LastAssistant: &bracket{10, 12}, Terminal: &bracket{12, 13}}
	sum, active, overlap := writerTiming(a, b)
	if sum == nil || active == nil || overlap == nil || *sum != (bracket{19, 24}) || *active != (bracket{15, 20}) || *overlap != (bracket{3, 6}) {
		t.Fatalf("session sum = %+v, observed active sum = %+v, overlap = %+v", sum, active, overlap)
	}
	b.Terminal = nil
	sum, active, _ = writerTiming(a, b)
	if sum != nil || active != nil {
		t.Fatalf("missing terminal produced a duration: session %+v, active %+v", sum, active)
	}
}

func put(t *testing.T, path, data string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0700); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(data), 0600); err != nil {
		t.Fatal(err)
	}
}
