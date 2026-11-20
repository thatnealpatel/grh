package source

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"os/exec"
)

func run(ctx context.Context, cmd *exec.Cmd, maxStdout int) ([]byte, error) {
	output := boundedBuffer{max: maxStdout}
	cmd.Stdout = &output
	err := cmd.Run()
	if ctx.Err() != nil {
		return nil, ctx.Err()
	}
	if err != nil {
		// Do not return provider/process diagnostics
		// containing credentials or page data.
		return nil, fmt.Errorf("%s: %w", cmd.Args[0], err)
	}
	return output.buf.Bytes(), nil
}

type boundedBuffer struct {
	buf bytes.Buffer
	max int
}

func (b *boundedBuffer) Write(p []byte) (int, error) {
	if len(p) > b.max-b.buf.Len() {
		return 0, errors.New("subprocess output limit exceeded")
	}
	return b.buf.Write(p)
}
