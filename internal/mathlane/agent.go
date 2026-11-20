package mathlane

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"syscall"
	"time"
)

const agentTimeout = 3 * time.Minute

var piModelID = regexp.MustCompile(`^[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9][A-Za-z0-9_.@/-]*$`)

func mathModel(instructions, configured string) (string, error) {
	if configured != "" {
		if !piModelID.MatchString(configured) {
			return "", errors.New("GRH_MATH_MODEL must be a Pi provider/model ID")
		}
		return configured, nil
	}
	// Use the same provider integrations as SOURCE, with a separate model
	// from the default candidate generator for both fresh semantic reviews.
	if instructions == fidelityPrompt || instructions == challengePrompt {
		return "exe-dev-anthropic/claude-opus-4-8@llm", nil
	}
	return "exe-dev-openai/gpt-6.2-sol@llm", nil
}

func piArgs(provider, id, instructions string) ([]string, error) {
	// Disable model-accessible tools and all resource discovery; only the
	// explicitly selected provider registration may be loaded.
	args := []string{"--offline", "--no-approve", "--no-session", "--no-extensions", "--no-tools", "--no-skills", "--no-context-files", "--no-prompt-templates", "--no-themes"}
	if strings.HasPrefix(provider, "exe-dev-") {
		dir := os.Getenv("PI_CODING_AGENT_DIR")
		if dir == "" {
			home, err := os.UserHomeDir()
			if err != nil {
				return nil, fmt.Errorf("locate Pi exe-dev integration: %w", err)
			}
			dir = filepath.Join(home, ".pi", "agent")
		}
		extension, err := filepath.Abs(filepath.Join(dir, "extensions", "exe-dev", "index.ts"))
		if err != nil {
			return nil, fmt.Errorf("locate Pi exe-dev integration: %w", err)
		}
		if info, err := os.Stat(extension); err != nil || !info.Mode().IsRegular() {
			return nil, errors.New("Pi exe-dev integration not found under the Pi agent directory")
		}
		args = append(args, "--extension", extension)
	}
	return append(args, "--mode", "json", "--print", "--provider", provider, "--model", id, "--thinking", "high", "--system-prompt", instructions), nil
}

func runPi(ctx context.Context, root, instructions string, input []byte) ([]byte, error) {
	ctx, cancel := context.WithTimeout(ctx, agentTimeout)
	defer cancel()
	modules, err := pinnedSources(ctx, root, os.Getenv("GRH_MATHLIB"))
	if err != nil {
		return nil, fmt.Errorf("retrieve mathlane Mathlib sources: %w", err)
	}
	data, err := json.Marshal(struct {
		MathlibRev     string
		MathlibSources []moduleSource
		Request        json.RawMessage
	}{mathlibRev, modules, input})
	if err != nil {
		return nil, fmt.Errorf("encode agent input: %w", err)
	}
	return askPi(ctx, instructions, data)
}

func askPi(ctx context.Context, instructions string, data []byte) (output []byte, err error) {
	model, err := mathModel(instructions, os.Getenv("GRH_MATH_MODEL"))
	if err != nil {
		return nil, err
	}
	provider, id, _ := strings.Cut(model, "/")
	args, err := piArgs(provider, id, instructions)
	if err != nil {
		return nil, err
	}
	// The disposable working directory isolates
	// project discovery even from a malicious
	// draft. This is a no-tools invocation, not an
	// OS sandbox for Pi.
	scratch, err := os.MkdirTemp("", "grh-mathlane-")
	if err != nil {
		return nil, fmt.Errorf("create mathlane scratch: %w", err)
	}
	defer func() {
		if cleanErr := os.RemoveAll(scratch); cleanErr != nil {
			err = errors.Join(err, fmt.Errorf("remove mathlane scratch: %w", cleanErr))
		}
	}()
	cmd := exec.CommandContext(ctx, "pi", args...)
	cmd.Dir = scratch
	cmd.Stdin = bytes.NewReader(data) // Print mode reads piped stdin as the prompt.
	// The caller's Gödel scope owns descendants. Cancel
	// this immediate process group on a per-request
	// deadline, including ordinary launcher children.
	cmd.SysProcAttr = &syscall.SysProcAttr{Setpgid: true}
	cmd.Cancel = func() error {
		err := syscall.Kill(-cmd.Process.Pid, syscall.SIGKILL)
		if errors.Is(err, syscall.ESRCH) {
			return os.ErrProcessDone
		}
		return err
	}
	cmd.WaitDelay = 2 * time.Second
	var stdout piOutput
	cmd.Stdout = &stdout
	runErr := cmd.Run()
	if cause := context.Cause(ctx); cause != nil {
		return nil, cause
	}
	if runErr != nil {
		// Provider diagnostics may contain credentials or supplied
		// source data.
		return nil, fmt.Errorf("run tool-free Pi (%s): %w", model, runErr)
	}
	if stdout.truncated {
		return nil, errors.New("mathlane Pi event stream exceeds size limit")
	}
	return readPi(stdout.buf.Bytes(), data, provider, id)
}

const maxPiOutput = 16 << 20

type piOutput struct {
	buf       bytes.Buffer
	truncated bool
}

func (b *piOutput) Write(p []byte) (int, error) {
	n := len(p)
	if remain := maxPiOutput - b.buf.Len(); remain < n {
		p = p[:remain]
		b.truncated = true
	}
	b.buf.Write(p)
	return n, nil
}

type piMessage struct {
	Role, Provider, Model, StopReason, RawStopReason, ErrorMessage string
	Content                                                        []struct{ Type, Text string }
}

// A zero exit status is not enough: Pi may emit partial text for a
// failed stream. Require one settled turn with the actual expected
// input and model.
func readPi(output, input []byte, provider, id string) ([]byte, error) {
	scan := bufio.NewScanner(bytes.NewReader(output))
	scan.Buffer(nil, 1<<20)
	var messages []piMessage
	settled := false
	for scan.Scan() {
		var event struct {
			Type      string
			Messages  []piMessage
			WillRetry bool
		}
		if err := json.Unmarshal(scan.Bytes(), &event); err != nil || event.Type == "" {
			return nil, errors.New("malformed Pi event stream")
		}
		switch event.Type {
		case "tool_execution_start", "auto_retry_start", "auto_compaction_start", "compaction_start":
			return nil, errors.New("Pi did not complete a single tool-free turn")
		case "agent_end":
			if messages != nil || settled || event.WillRetry || len(event.Messages) != 2 {
				return nil, errors.New("Pi did not finish exactly one user/assistant turn")
			}
			messages = event.Messages
		case "agent_settled":
			if settled || messages == nil {
				return nil, errors.New("unexpected Pi settlement event")
			}
			settled = true
		}
	}
	if scan.Err() != nil || !settled {
		return nil, errors.New("incomplete or oversized Pi event stream")
	}
	user, assistant := messages[0], messages[1]
	if user.Role != "user" || len(user.Content) != 1 || user.Content[0].Type != "text" || user.Content[0].Text != string(input) {
		return nil, errors.New("Pi did not retain the exact supplied request")
	}
	if assistant.Role != "assistant" || assistant.Provider != provider || assistant.Model != id || assistant.ErrorMessage != "" || assistant.StopReason != "stop" {
		return nil, errors.New("Pi did not complete normally with the requested model")
	}
	switch assistant.RawStopReason {
	case "stop", "end_turn", "completed": // Chat Completions, Anthropic, Responses.
	default:
		return nil, errors.New("Pi did not report a supported provider completion reason")
	}
	var text bytes.Buffer
	for _, part := range assistant.Content {
		switch part.Type {
		case "text":
			if text.Len()+len(part.Text) > maxReplyBytes {
				return nil, errors.New("mathlane agent response too large")
			}
			text.WriteString(part.Text)
		case "thinking":
		default:
			return nil, errors.New("unexpected non-text Pi answer content")
		}
	}
	return text.Bytes(), nil
}
