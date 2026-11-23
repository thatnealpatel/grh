# Eve

From the durable GRH checkout after adoption, supply the dynamic user prompt:

```sh
printf '%s\n' 'Prioritize a checked lemma used by both peers.' | go run ./cmd/eve
```

One launch is one pass. The Astra coordinator receives stdin as the user message and the embedded [formalization protocol](formalize.md) via `-append`. It dispatches a fresh Sol history scan, then up to three Sol proof writers in parallel. It reviews and adopts only checked outcomes. It does not run Alice or Bob or schedule its own next invocation.

Use the same checkout and home for a single serialized Gödel history. A concurrent launch from that source fails on the Gödel lock, rather than queuing. Give each launch a nonblank prompt: With blank stdin Gödel falls back to the last nonblank final response, or fails on first use. Prior outputs are not scan cursors.
