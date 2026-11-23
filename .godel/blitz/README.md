# Blitz

Blitz assesses classical RH and full Masullo GRH separately. For each target,
it asks whether the accepted formalization supports a bounded proof attempt:
How do the accepted results fit together, and what assumptions would still
be needed? It reads the exact accepted campaign revision, relevant proof and
source notes, and recent main, companion and Blitz work as evidence. It does
not assume that either proof is within reach. Ordinary useful lemma work does
not by itself warrant a blitz.

If the assessment is affirmative, Blitz starts the attempt automatically. It
may use informal mathematics or Lean, with **at most three passes total**,
even if it switches modes. It can stop sooner. It does not launch, direct, or
edit the other drivers and has no self-improvement phase. Keep informal
evidence separate from checked Lean results, and follow the [campaign workflow
and proof checks](../../cmd/godel/README.md) for landing.

## Cadence and history

Assess immediately at launch. After the terminal node records a decline or an
attempt outcome, wait 15 minutes, then let Gödel launch a fresh process. The wait
is from completion, not a fixed wall-clock slot. Changes to the campaign don't
interrupt it. INT or TERM can cancel the wait. A failure stops the loop rather
than silently retrying.

Read the versioned notes in `.godel/blitz/` **on the campaign target** for Blitz's
finalized decisions and attempt outcomes. Only the closing node lands these
through the campaign. Use `~/t/grh` for inconsequential or tangential scratch
outside project history. Nodes pass short context inline and use `~/t/grh/blitz/`
for opening plans and longer transient context within a cycle. Write JSON plan
paths as expanded absolute paths in that directory, not with a literal `~` or
`$HOME`. An accepted attempt note uses the scratch plan's basename. Keep
consequential proofs, decisions, needed evidence, and self-contained handoffs
in accepted history; scratch files are not required evidence. There is no
separate Blitz ledger. For driver diagnostics,
look up the canonical `cmd/blitz` path in `~/.godel/manifest.json`, then read
`~/.godel/<program-id>/runs/*.json`. Gödel still regards the wait as part of the
run: canceling the wait can mark the run failed without undoing an accepted note.
The embedded launch source commit identifies the Blitz program build, not the
accepted proof revision available to an assessment; check campaign status for
that revision.

## Launch

Use a durable GRH jj workspace that contains `cmd/blitz` and shares the owning
campaign repository. Use the accepted-build and runtime prerequisites described
in the [main driver guide](../../cmd/godel/README.md). Keep this workspace in
place: each iteration runs `go run .` from `cmd/blitz` and resolves the target
anew. The local target defaults to `main`; Blitz takes no arguments.

```sh
cd -P "${GRH_LAUNCH_ROOT:?set the durable launch workspace}"
export YAH_CAMPAIGN_TARGET=main
printf '%s\n' 'Assess the accepted campaign.' | go run ./cmd/blitz
```

The nonblank seed allows a first run without Gödel history. Later iterations
receive the previous terminal node's output, not new operator directives.
Set a time limit for unattended use; stop the job's process group, not just
the outer `go run` wrapper.
