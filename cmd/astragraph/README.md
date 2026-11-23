# Astra graph prototype

From this directory, run the graph against the fixed tailnet proxy at `http://100.75.6.66:9001/v1/responses`:

```sh
printf '%s\n' 'Your task here' | go run .
```

This runs one Gödel work node with no loop or self-improver. Gödel requires a Linux user systemd manager and keeps normal run history under `~/.godel`. Run from this directory so that history has its own source identity. Blank stdin in this mode invokes Gödel's normal history fallback. The proxy receives the task and branch outputs; this is not an offline or anonymous inference mode.

`go run . think 'Answer the question briefly.'` makes one call on stdin. `go run . graph` runs just the coordinator, bypassing Gödel and its history. Each graph worker invokes the same executable in `think` mode. Only the final answer is written to stdout. The client posts to `/v1/responses` with `X-Backend: codex` and the fixed model `gpt-6.2-astra`; no fallback model or automatic retries.

A successful graph costs 34 inference calls. A framing call assigns eight lanes. Four eight-wide layers propose, challenge adjacent proposals, repair using both challenges, and audit repairs three lanes apart. A final call receives all audits and repairs. Every call sees the original task. Each layer waits for the previous one; a failed call cancels sibling work and prevents synthesis. Intermediate prompts and replies are in memory, not saved by this command. `go test .` uses a local fake proxy, not a live model.
