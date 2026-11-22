# Masullo walk ledger (unadopted draft)

`cmd/walk` owns one JSON file per reviewed chapter or appendix:
`chapter-01.json` through `chapter-14.json`, then `appendix-a.json` through
`appendix-e.json`. There are no placeholder files. Each file pins the
[manuscript edition](../sources/masullo/README.md) and contains `records` in
reading order, a `cursor` (last forward-reviewed passage, or `null`), and a
separate `complete` flag. Completion is coverage, not formal resolution.

## Running Walk

Run with no flags from `cmd/walk` in the workspace that owns the ledger.
`GRH_LAUNCH_ROOT` is the absolute path of the stable GRH project workspace
attached to the owning Yah campaign. It can differ from the walker's root.
Use an authenticated `yah` on `PATH` and a working user systemd manager.

```sh
# From the ledger owner's root, with GRH_LAUNCH_ROOT already exported:
cd cmd/walk
printf '%s\n' 'Review the pinned Masullo manuscript in order.' | go run .
```

Gödel needs nonblank stdin on the first run (or whenever there is no saved
nonblank response). To resume, rerun the same command from the same `cmd/walk`
with the same `.godel/walk` ledger, after the earlier writer has stopped.
Supplying nonblank stdin again is safe: It is not the cursor or the next
request. Once Gödel has a saved nonblank response, `go run . </dev/null` also
works from that directory. The ledger, not Gödel's stdin or history, determines
what to review next.

## Reviewer interface

Walk runs a built-in Yah reviewer node from `GRH_LAUNCH_ROOT`. Yah may read
but must not edit the walker's ledger. It uses the pinned PDF and current
accepted project evidence. Each appended prompt carries one JSON request
with `edition`, `chapter`, and `cursor`; the reviewer returns one JSON object
on stdout. Walk retries the same request once if stdout is not valid JSON
syntax, with a short diagnostic in the new prompt. Neither syntax failure
writes the ledger. Process failures and valid JSON that fails review
validation stop without retry.

- **Forward:** Return `chapter` and the next `record`. To finish reading that
  chapter, also return `complete: true`, with or without a final record. Use
  manuscript order within a page and stable `(kind, locator, printed_page)`
  identities, including for unnumbered passages. A failed or invalid review
  does not advance the cursor.
- **Revisit:** The request also has `revisit` (the old record) and `inputs`
  (each old dependency's `requirement` and `current` evidence). Return
  `chapter` and a full replacement `record` for the same passage; omit
  `complete`. Keep each still-applicable dependency and set its `reviewed`
  to the actual current evidence, including `null` when withdrawn or absent.
  Omit an old dependency only if the reviewer finds that it does not apply.
  This replaces the record in place, without advancing or rewinding coverage.

Review one passage per request; land one finding or a short contiguous group
that another reader can assess without access to the live workspace. An open
finding may land if it identifies the printed claim, distinguishes the
rendered and extracted sources, and names the precise missing step (for
example, the closed-embedding argument for the global theta quotient). Do not
wait for chapter completion or a proof of the open claim.

A record contains `passage`, `printed_finding`, `formal`, and optional
`references`, `conclusion_evidence`, and `dependencies`. In `formal`, use
`status` (`open`, `established`, `refuted`, or `not_applicable`), `scope`, and
`argument_provenance`. A heading without a statement is not applicable, not
established. Identify extra hypotheses and whose argument was used; a
specialization or repair does not resolve the broader claim as printed.
`references` name Lean declarations (`kind: "lean"`) or existing audit paths
(`kind: "audit"`) by `target` and `revision`. The walker checks the handoff,
not the mathematics, edition bytes, Lean declarations, or audit contents.

A dependency's `requirement` names a `source` (chapter and passage) and the
exact scoped `conclusion` needed there. The source record may publish one
`conclusion_evidence` entry per such conclusion, with an `evidence` value
containing a `verdict` (`supports` or `contradicts`) and a `reference`. Use the
same conclusion identifier on both sides and keep the evidence revision
stable unless the cited evidence changes; do not use a traversal counter or
an unrelated repository revision. In a forward review, `reviewed: null` can
leave an input for later review.

## Resuming

A sole writer publishes each accepted review by renaming a temporary file
within the ledger directory. Opening the walk reconstructs progress and
finds back-edges by comparing each dependency's stored receipt to the current
source evidence for that precise conclusion. Scheduling does not acknowledge
a receipt. This covers process interruption, not concurrent writers or
power-loss durability; abandoned temporary files are not read as state.

Changed inputs are revisited before forward work, at most once per passage
between forward reviews. No evidence on either side is not a change. A cycle
that changes evidence again leaves the receipt stale for the next forward
checkpoint or a manual reopen. If all coverage is complete and the bound
still defers a review, the draft reports that pending work rather than looping
or marking an open claim resolved.
