# Masullo walk ledger (unadopted draft)

This directory is Walk's repository home for schema, guidance, and accepted
self-contained findings. The mutable chapter and appendix checkpoints live
in the private ledger outside the checkout.

`cmd/walk` owns one JSON file per reviewed chapter or appendix:
`chapter-01.json` through `chapter-14.json`, then `appendix-a.json` through
`appendix-e.json`. There are no placeholder files. Each file pins the
[manuscript edition](../sources/masullo/README.md) and contains `records` in
reading order, a `cursor` (last forward-reviewed passage, or `null`), and a
separate `complete` flag. Completion is coverage, not formal resolution.

## Running Walk

After the Walk entrypoint is accepted and present in the **durable** GRH
checkout, run from that checkout's root (not a campaign session workspace).
Use an authenticated `yah` on `PATH` and a working user systemd manager.
`accepted.Enter` builds and runs Walk from the accepted revision and sets
its working directory to the durable `cmd/walk` for Gödel registration.

```sh
cd /home/exedev/p/grh
printf '%s\n' 'Review the pinned Masullo manuscript in order.' |
    YAH_CAMPAIGN_TARGET=main go run ./cmd/walk
```

The private ledger is `$HOME/.grh-walk-<hash>`, outside the checkout, where
`<hash>` is the lowercase hexadecimal SHA-256 of the canonical absolute
`cmd/walk` directory path (resolved symlinks, no trailing newline). This
keys the ledger to the same source directory Gödel uses for its program
lock. Keep the same checkout path and home on restart. Stop the previous
writer and rerun the launch command with the nonblank seed. Gödel needs a
seed if no saved nonblank response is available. Neither that seed nor
old Gödel runs or their history determine the cursor; only the ledger does.

## Reviewer interface

Walk runs its built-in Yah reviewer from the durable checkout root. Yah may
read but must not edit the private ledger. It reads this README, the schema
in `cmd/walk/store.go`, and project evidence at the accepted revision, and
uses the pinned PDF. Each appended prompt carries one JSON request
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
that another reader can assess without access to the live workspace. For notes
under `.godel/walk/`, use `.godel:` followed by a capitalized imperative naming
the finding, for example, `.godel: Record the global orbital closed-range gap`.
An open finding may land if it identifies the printed claim, distinguishes the
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

To restore an existing ledger, stop all Walk writers and keep them stopped
until the copy is complete. Create the destination ledger directory with
mode `0700` if it does not exist. Copy only the existing `chapter-*.json`
and `appendix-*.json` state files listed above into that directory, without
clobbering any destination file. If a destination file already exists,
resolve the conflict offline before restarting; do not merge or overwrite
state while Walk is running. Do not copy the README, temporary files, or
Gödel history. The restored chapter and appendix files are enough to resume
with the normal launch command.

Walk opens the ledger under Gödel's program lock. The sole writer publishes
each accepted review by renaming a temporary file within the ledger directory.
Opening the walk reconstructs progress and finds back-edges by comparing each
dependency's stored receipt to the current source evidence for that precise
conclusion. Scheduling does not acknowledge a receipt. This covers process
interruption, not concurrent writers or power-loss durability; abandoned
temporary files are not read as state.

Changed inputs are revisited before forward work, at most once per passage
between forward reviews. No evidence on either side is not a change. A cycle
that changes evidence again leaves the receipt stale for the next forward
checkpoint or a manual reopen. If all coverage is complete and the bound
still defers a review, the draft reports that pending work rather than looping
or marking an open claim resolved.
