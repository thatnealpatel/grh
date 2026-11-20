package source

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"image"
	"image/png"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

func TestRenderedPassageThroughYah(t *testing.T) {
	poppler, err := exec.LookPath("pdftoppm")
	if err != nil {
		t.Skip("requires pdftoppm on PATH")
	}
	fixtures := t.TempDir()
	pdf := fixturePDF()
	path := filepath.Join(fixtures, "paper.pdf")
	writeFixture(t, path, pdf)
	if output, err := exec.CommandContext(t.Context(), poppler, "-r", "175", "-png", path, filepath.Join(fixtures, "reference")).CombinedOutput(); err != nil {
		t.Fatalf("reference render: %v: %s", err, output)
	}
	t.Setenv("GRH_PDF", path)
	t.Setenv("SRC_REFERENCE", fixtures)
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	bin := t.TempDir()
	if err := os.Symlink(exe, filepath.Join(bin, "yah")); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", bin+string(os.PathListSeparator)+os.Getenv("PATH"))

	a := reading{verified, []int{1, 2}, "For every x in A, f(x) = -g(x).", "Author, eq. (1)", "Only on A.", "Assumes x belongs to A."}
	b := reading{verified, []int{1, 2}, "If x belongs to A, f(x) equals the negative of g(x).", "Author, equation (1)", "On A only.", "The equation does not cover other x."}
	near := b
	near.Reading = "If x belongs to A, f(x) equals g(x)."
	missing := reading{absent, []int{1, 2}, "The theorem heading is followed by the next chapter without a statement.", "None", "Insert statement.", "Section 2 ends at Chapter 3."}
	unclear := b
	unclear.Disposition = ambiguous
	wrong := a
	wrong.PrintedPages = []int{2, 1}
	yes := comparison{[]int{1, 2}, "yes", "yes", "yes", "Eq. (1) has a minus sign.", "The visible hypothesis is x in A."}
	no := comparison{[]int{1, 2}, "no", "no", "yes", "Reading B drops the minus sign in eq. (1).", "The equation still assumes x in A."}
	gap := comparison{[]int{1, 2}, "yes", "yes", "yes", "Visible note: Insert statement.", "Section 2 ends with the Chapter 3 heading."}
	for _, tc := range []struct {
		name    string
		answers []any
		fault   string // Applied only to the final configured invocation.
		want    string
		wantErr string
	}{
		{"exact agreement", []any{a, a}, "", verified, ""},
		{"paraphrase", []any{a, b, yes}, "", verified, ""},
		{"not a paraphrase", []any{a, near, no}, "", ambiguous, ""},
		{"visibly absent", []any{missing, missing, gap}, "", absent, ""},
		{"independent uncertainty", []any{a, unclear}, "", ambiguous, ""},
		{"wrong printed pages", []any{wrong}, "", "", "different printed page mapping"},
		{"guesses after an image is missing", []any{a}, "guess missing", "", "visual access"},
		{"second reader supplies only one code", []any{a, a}, "omit code", "", "visual access"},
		{"adjudicator swaps page codes", []any{a, b, yes}, "swap codes", "", "visual access"},
		{"reviewer abstains", []any{a}, "unavailable", "", "visual access"},
		{"code outside response field", []any{a}, "echo code", "", "outside its response field"},
		{"valid partial output from failed process", []any{a}, "failed process", "", "exit status 9"},
		{"malformed final answer", []any{a}, "bad JSON", "", "malformed JSON"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			dir := t.TempDir()
			t.Setenv("TMPDIR", filepath.Join(fixtures, "must-not-use-for-source"))
			t.Setenv("SRC_FAKE", dir)
			script, err := json.Marshal(struct {
				Answers []any
				Fault   string
			}{tc.answers, tc.fault})
			if err != nil {
				t.Fatal(err)
			}
			writeFixture(t, filepath.Join(dir, "script.json"), script)
			e := fixtureEdition("https://invalid.example/test.pdf", pdf)
			p, err := e.readPassage(t.Context(), Passage{1, 2, "Fixture (1)", "Is there a formula?"})
			if detail, readErr := os.ReadFile(filepath.Join(dir, "error")); readErr == nil {
				t.Fatalf("fake rejected the invocation: %s (call error %v)", detail, err)
			}
			data, readErr := os.ReadFile(filepath.Join(dir, "turns"))
			if readErr != nil {
				t.Fatalf("fake was not invoked: %v (%v)", readErr, err)
			}
			turns := strings.Fields(string(data))
			if len(turns) != len(tc.answers) {
				t.Fatalf("got %d invocations, want %d (packet %+v, error %v)", len(turns), len(tc.answers), p, err)
			}
			for i, turn := range turns {
				if slices.Contains(turns[:i], turn) {
					t.Fatalf("invocations shared scratch: %s", turn)
				}
				if _, err := os.Stat(filepath.Dir(turn)); !errors.Is(err, os.ErrNotExist) {
					t.Fatalf("request scratch was not removed: %v", err)
				}
			}
			if tc.wantErr != "" {
				if err == nil || !strings.Contains(err.Error(), tc.wantErr) || p != (Packet{}) {
					t.Fatalf("wanted no disposition and error %q, got %+v, %v", tc.wantErr, p, err)
				}
				return
			}
			if err != nil || p.Disposition != tc.want {
				t.Fatalf("wanted %s, got %+v, %v", tc.want, p, err)
			}
			if !strings.Contains(p.Anchor, e.sha256) || !strings.Contains(p.Anchor, "printed pp. 1–2 = PDF ordinals 1–2") {
				t.Errorf("anchor lost edition or page mapping: %s", p.Anchor)
			}
			for i, evidence := range p.Evidence {
				if !strings.HasPrefix(evidence, fmt.Sprintf("Yah reader %d (", i+1)) {
					t.Errorf("evidence lost role attribution: %s", evidence)
				}
			}
			if tc.want == absent && !strings.Contains(p.Boundary, "Chapter 3 heading") {
				t.Errorf("absence dropped its visible boundary: %s", p.Boundary)
			}
			if tc.name == "not a paraphrase" && p.Comparison != "Yah adjudicator: Reading B drops the minus sign in eq. (1)." {
				t.Errorf("disagreement dropped its evidence: %s", p.Comparison)
			}
		})
	}
}

// The test executable installed as "yah"
// consumes only the public command
// contract and the PNGs. It never invokes
// Yah or a model.
func TestMain(m *testing.M) {
	if filepath.Base(os.Args[0]) == "yah" && os.Getenv("SRC_FAKE") != "" {
		if err := fakeYah(os.Getenv("SRC_FAKE")); err != nil {
			if err := os.WriteFile(filepath.Join(os.Getenv("SRC_FAKE"), "error"), []byte(err.Error()), 0o600); err != nil {
				panic(err)
			}
			os.Exit(1)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

func fakeYah(dir string) error {
	cwd, err := os.Getwd()
	if err != nil {
		return err
	}
	log := filepath.Join(dir, "turns")
	previous, err := os.ReadFile(log)
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		return err
	}
	turn := len(strings.Fields(string(previous)))
	if err := os.WriteFile(log, append(previous, cwd+"\n"...), 0o600); err != nil {
		return err
	}
	data, err := os.ReadFile(filepath.Join(dir, "script.json"))
	if err != nil {
		return err
	}
	var script struct {
		Answers []json.RawMessage
		Fault   string
	}
	if err := json.Unmarshal(data, &script); err != nil {
		return err
	}
	if turn >= len(script.Answers) {
		return fmt.Errorf("unexpected invocation %d", turn+1)
	}
	if filepath.Dir(filepath.Dir(cwd)) != "/tmp" || os.Getenv("TMPDIR") != cwd || os.Getenv("YAH_DEFAULT_TOOLS") != "subagent" || os.Getenv("YAH_CAMPAIGN_TARGET") != "main" {
		return errors.New("wrong scratch or capability setup")
	}
	if len(os.Args) != 5 || !slices.Equal(os.Args[1:4], []string{"-jj", "-yolo", "-replace"}) || !strings.Contains(os.Args[4], "native image-capable reviewer") {
		return errors.New("wrong fresh headless flags or missing native visual instruction")
	}
	input, err := io.ReadAll(os.Stdin)
	if err != nil {
		return err
	}
	prompt := string(input)
	if !strings.Contains(prompt, "native image-capable Read tool") || !strings.Contains(prompt, "Use no OCR") || !strings.Contains(prompt, "Locator: Fixture (1)\nQuestion: Is there a formula?") {
		return errors.New("missing visual inspection contract or passage scope")
	}
	if candidates := strings.Contains(prompt, "Untrusted candidate readings (JSON):"); candidates != (turn == 2) {
		return errors.New("independent read received another reading, or adjudication lacks both candidates")
	}
	_, rest, ok := strings.Cut(prompt, "Rendered PNG paths (in order):\n")
	line, _, _ := strings.Cut(rest, "\n")
	var paths []string
	if !ok || json.Unmarshal([]byte(line), &paths) != nil || len(paths) != 2 {
		return errors.New("missing ordered PNG paths in text stdin")
	}
	fault := ""
	if turn == len(script.Answers)-1 {
		fault = script.Fault
	}
	entries, err := os.ReadDir(cwd)
	if err != nil || len(entries) != 2 {
		return errors.New("scratch contains something other than the supplied images")
	}
	codes := make([]string, 0, 2)
	answer := script.Answers[turn]
	for i, path := range paths {
		if path != fmt.Sprintf("page-%d.png", i+1) {
			return errors.New("path escapes the invocation or is not a plain page filename")
		}
		if fault == "guess missing" && i == 1 {
			if err := os.Remove(path); err != nil {
				return err
			}
			// Guess with a well-formed code, but
			// without inspecting the missing page.
			codes = append(codes, codes[0])
			continue
		}
		original, err := decodePNG(filepath.Join(os.Getenv("SRC_REFERENCE"), fmt.Sprintf("reference-%d.png", i+1)))
		if err != nil {
			return err
		}
		img, err := decodePNG(path)
		if err != nil {
			return err
		}
		if img.Bounds() != image.Rect(0, 0, 1488, 2069) || !bytes.Equal(img.Pix[:len(original.Pix)], original.Pix) {
			return errors.New("full original rendered page did not survive pixel-for-pixel")
		}
		code, err := sampleStrip(img)
		if err != nil {
			return err
		}
		if strings.Contains(prompt+strings.Join(os.Args, " "), code) {
			return errors.New("a challenge solution leaked outside the image")
		}
		codes = append(codes, code)
	}
	switch fault {
	case "swap codes":
		slices.Reverse(codes)
	case "omit code":
		codes = codes[:1]
	case "unavailable":
		codes, answer = []string{}, json.RawMessage("null")
	case "echo code":
		var r reading
		if err := json.Unmarshal(answer, &r); err != nil {
			return err
		}
		r.Evidence = codes[0]
		answer, err = json.Marshal(r)
		if err != nil {
			return err
		}
	case "bad JSON":
		_, err := fmt.Fprint(os.Stdout, `{"page_codes":[]}`+" trailing data")
		return err
	}
	if err := json.NewEncoder(os.Stdout).Encode(map[string]any{"page_codes": codes, "answer": answer}); err != nil {
		return err
	}
	if fault == "failed process" {
		os.Exit(9)
	}
	return nil
}

func decodePNG(path string) (*image.RGBA, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	img, err := png.Decode(f)
	if err != nil {
		return nil, err
	}
	rgba, ok := img.(*image.RGBA)
	if !ok {
		return nil, fmt.Errorf("expected opaque RGB fixture: %s", path)
	}
	return rgba, nil
}

// Sample the segment centers in the known
// fixture canvas. The fake derives its answer
// from pixels, not production challenge state or
// a text side channel.
func sampleStrip(img *image.RGBA) (string, error) {
	digits := map[string]byte{
		"1111110": '0', "0110000": '1', "1101101": '2', "1111001": '3', "0110011": '4',
		"1011011": '5', "1011111": '6', "1110000": '7', "1111111": '8', "1111011": '9',
	}
	var code strings.Builder
	for i := range 12 {
		var pattern strings.Builder
		for _, p := range []image.Point{{348, 1955}, {366, 1976}, {366, 2018}, {348, 2039}, {330, 2018}, {330, 1976}, {348, 1997}} {
			switch c := img.RGBAAt(p.X+72*i, p.Y); {
			case c.R == 0 && c.G == 0 && c.B == 0 && c.A == 255:
				pattern.WriteByte('1')
			case c.R == 255 && c.G == 255 && c.B == 255 && c.A == 255:
				pattern.WriteByte('0')
			default:
				return "", errors.New("challenge was not drawn on a white strip")
			}
		}
		digit, ok := digits[pattern.String()]
		if !ok {
			return "", errors.New("could not find legible digit in the white strip")
		}
		code.WriteByte(digit)
	}
	return code.String(), nil
}
