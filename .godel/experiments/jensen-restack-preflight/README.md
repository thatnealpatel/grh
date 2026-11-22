# Replay the Jensen candidate checks

## Work reconstruction

Gödel run `01a20579-fc12-71e8-83b2-89621e3db024` matches Main Yah
`01a20579-fd7d-77f1-98d5-746c75b548e4` by stdin and stdout (seqs. 3,
127). The launch archive `25b4c1b1d280d41e2d5e102d808c3b7d4afa4405`
has the same `cmd/godel` and `internal/godel` trees as the work landing.
The starting accepted commit was `bad504b1a49ce6328c0d60824f996e3e4f33806c`.
Main matched the prior run (`01a20567-41b5-7876-b0ed-5f26863a22b8`),
recognized that its improvement (Yah `01a2056f-8344-7f8c-ab83-1ef134597ce8`)
had landed the strip bound at `bd041db358941d519fccde5c2c734aca4dc193ba`,
and moved on to the same-numerator Jensen estimate. It did not
recover an unlanded artifact. This is another successful handoff
reconciliation, not a reason to replace the work selector.

- Writer allocation used the current base
  `6798c5221434ea2c39bb034ba427ac97b3e6d98d`. The first writer build
  failed on Lean elaboration (phase-zero simplification and coercions,
  the strip exponent comparison, and the Jensen calculation; seq. 45).
  The repaired proof built (seq. 54). Writer output was
  `06740008b5c6a1b2e3feb384aa1dd4acbfa0957c`. Agent `XRCTwYR` independently
  reviewed fixed statements and pinned manuscript Markdown and PDF text
  (seq. 100). Its `6d638ac2d5ed356d0db385f665eb08d213eed9f0` is an empty
  review snapshot, not a competing proof. The source reading did not
  inspect rendered pages.
- `90a75558dcb74d0fb938d49f97f961049685db13` built and passed the fresh
  joint import (seq. 82), but status during the build showed that its
  base had been superseded (seq. 80). It was not submitted for adoption.
- Restack `501762b0c6394898958f7f34ef67da8c8e3a16cd` reused the cache,
  reran the exact-candidate checks (seq. 97), and returned stale on
  adoption (seq. 102).
- The last restack's first check command stopped before Lake (seq. 111).
  With the corrected comparison, the scoped build and fresh joint
  report passed (seq. 124). All six axiom lists were allowed and the
  fresh report matched the second candidate's. Only
  `54fda388fab1f0f948f63d8b8c2fadc828e19b6f` was adopted (seq. 126).
  The [proof handoff](../../obligations/single-place-norm.md#checked-moving-disk-jensen-count)
  states the result and its limits: The count is a contour input for
  the trivial Hecke character, not a horizontal estimate or RH result.

## Small replay and decision

Improvement Yah `01a20582-0a3f-7ec6-ad1e-619d261b4720` compared the exact
base-to-candidate diffs: All three Jensen patches were identical.
The second-to-third candidate delta added only a Walk note and an
independent audit note. The failed pre-build recipe (Main seq. 107)
used `test -z "$(jj diff --stat ...)"` on the tracked Lean inputs.
On those two exact candidates, `--stat` returns `0 files changed,
0 insertions(+), 0 deletions(-)`, so the emptiness test fails.
`--name-only` succeeds with empty stdout. With an explicit check of
`jj`'s exit status, the replacement also rejected a real Lean delta
(the last candidate against its own base) and an unresolved revision.
This is a command-level replay, not a new proof check. The prior
[continuation run](../wrapped-axiom-reports/#live-follow-up-fixed-gaussian-continuation)
also had a pre-build failure, but there the earlier cache was absent.
This case is neither a missing cache nor a Lean failure.

Replayed a single status decision immediately before each build call:

| Main build call | Prior concurrent adoption already recorded | Decision then |
| --- | --- | --- |
| Seq. 73 | Companion Yah `01a2057b-e6bd-7969-ab40-6904eb1c7305`, seq. 54, 30.82 s before the call | Reconcile before building |
| Seq. 91 | Walk Yah `01a2057c-ff9c-746a-a425-0d6b3c9a9588`, seq. 53, 2.11 s before the call | Reconcile before building |
| Seq. 107 | No observed move since integration, through successful adoption in seq. 126 | Build |

The second build was already stale before launch even though another
concurrent adoption followed during the build. This matches the earlier
[positive preflight control](../prebuild-stale-check/) and does not
change its limitation: A status query does not reserve the accepted
branch. The replay does not measure elapsed-time savings or imply both
restacks would also occur under a different schedule.

Keep the existing nodes and proof gates. In the landing guide, place
an optional single status check *after* preparation, immediately before
a build when a concurrent move is plausible. For the optional cache,
require successful `--name-only` and empty output on unchanged tracked
inputs, not empty `--stat`. No polling, new executable, relaxation of
the required checks, or live A/B test.
