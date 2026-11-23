# Mallory

One launch tests one implication in accepted work by Alice, Bob, or Eve. One pass has at most two Gödel nodes:

```text
┌────────────────────────┐    evidence    ┌────────────────────────┐
│ g:A1  Investigator/Sol │ ─────────────▶ │ g:J1  Adjudicator/Astra│
└────────────────────────┘                └────────────────────────┘
           │ no target                                │ verdict
           └─────────────────▶ stdout ◀───────────────┘
```

Each node gets the original stdin, its own model, and its own appended instructions. The [investigator](investigate.md) pins the claim and tries to break it. With no eligible target, its explanation ends the pass. Otherwise `Next` passes a bounded evidence brief to the fresh [adjudicator](adjudicate.md), which checks it against the pinned source and reports what survives. On a live pass the investigator first adopts the proposition and proposed test in `.godel/conjectures/open/` (or reuses the same open card). If that fails or the proposition is already closed, the pass stops before adjudication. The adjudicator records useful inconclusive evidence on the open card or moves it to `closed/` on a proof or counterexample. An interruption after opening leaves the question visible. Neither node edits producer work. Replays and explicit no-publication requests stay read-only. These limits are role instructions, not a separate tool sandbox. The final report still goes to stdout and Gödel’s ordinary history.

After adoption and only from a durable GRH checkout containing the launcher, an example is:

```sh
printf '%s\n' 'Replay d15218cc. Test whether its overlap cuts apply to the retained rows. Do not use later evidence.' | go run ./cmd/mallory
```

Pass nonblank input: Gödel can reuse the prior final response on blank stdin, or fail on first use. `accepted.Enter` rebuilds from the accepted target, so `go run` is not a way to try an unadopted candidate. To check the candidate wiring without starting research, run `go test ./cmd/mallory`. The [shadow replay](../../.godel/experiments/mallory/README.md) describes how to evaluate the behavior separately. No loop, cursor, or self-improvement.
