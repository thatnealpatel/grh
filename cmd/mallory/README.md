# Mallory

One launch tests one implication in accepted work by Alice, Bob, or Eve. One pass has at most two Gödel nodes:

```text
┌────────────────────────┐    evidence    ┌────────────────────────┐
│ g:A1  Investigator/Sol │ ─────────────▶ │ g:J1  Adjudicator/Astra│
└────────────────────────┘                └────────────────────────┘
           │ no target                                │ verdict
           └─────────────────▶ stdout ◀───────────────┘
```

Each node gets the original stdin, its own model, and its own appended instructions. The [investigator](investigate.md) pins the claim and tries to break it. With no eligible target, its explanation ends the pass. Otherwise `Next` passes a bounded evidence brief to the fresh [adjudicator](adjudicate.md), which checks it against the pinned source and reports what survives. Neither node lands results. The final report goes to stdout and Gödel’s ordinary history. The read-only rules are instructions to Yah, not a separate tool sandbox.

After adoption and only from a durable GRH checkout containing the launcher, an example is:

```sh
printf '%s\n' 'Replay d15218cc. Test whether its overlap cuts apply to the retained rows. Do not use later evidence.' | go run ./cmd/mallory
```

Pass nonblank input: Gödel can reuse the prior final response on blank stdin, or fail on first use. `accepted.Enter` rebuilds from the accepted target, so `go run` is not a way to try an unadopted candidate. To check the candidate wiring without starting research, run `go test ./cmd/mallory`. The [shadow replay](../../.godel/experiments/mallory/README.md) describes how to evaluate the behavior separately. No loop, cursor, publication, or self-improvement.
