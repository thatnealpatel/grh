# Eve

From the durable GRH checkout after adoption, supply the dynamic user prompt:

```sh
printf '%s\n' 'Prioritize a checked lemma used by both peers.' | go run ./cmd/eve
```

One launch is one pass. The Astra coordinator receives stdin as the user message and the embedded [formalization protocol](formalize.md) via `-append`. It dispatches one read-only Sol history scanner by default. Explicitly request two or three parallel seekers to add focused investigations alongside that scanner. Each seeker gets ten minutes of execution and leaves a provisional shortlist as it works. If discovery times out, the coordinator sends one more seeker, with the same limit, to resolve a named gap using the partial results. It does not restart Eve or retry the proof writers. After reconciling the available results, Eve dispatches one parallel batch of Sol proof writers (up to three by default, or up to six on explicit request). The two limits are independent: Asking for three seekers and six writers leaves all six proof slots available. It reviews and adopts only checked outcomes. It does not run Alice or Bob or schedule its own next invocation.

Use the same checkout and home for a single serialized Gödel history. A concurrent launch from that source fails on the Gödel lock, rather than queuing. Give each launch a nonblank prompt: With blank stdin Gödel falls back to the last nonblank final response, or fails on first use. Prior outputs are not scan cursors.
