# Read complete Lean axiom diagnostics

## Run reconstruction

Gödel run `01a204d4-bbaa-7958-8d25-cf4a5563a5bc` matches the input
and stdout of work session `01a204d4-bcfe-762c-89dc-4e1088d83973`
(events 3 and 195). The executable's archive marker and the work's
initial accepted tip were both `af2e69d9f26188e34fe1b98c901a5c76533edb46`.
The `cmd/godel` tree did not change between that revision and the work's
landing. This improvement is session `01a204e7-042d-7c33-8f2d-3083170320da`.

The input from [the preceding run](../workspace-default/) pointed to
unlanded global box Fourier scratch work. The worker found the matching
improvement report from Yah `01a204cc-1b12-7aec-9ee7-3bcbcd0c5b7f`,
then verified that `654e487c78d896e52647ed0c1375a9520efdc7ad` had landed.
It advanced to additive counting-quotient normalization rather than
replaying the scratch composition. This is another correct skip, not
a recovery of a still-unlanded draft. Both preceding nodes' prompts at
that run are traceable to `1f0fe5e97a69d1fbdba9b9e3632f842bd4e36f53`.
The earlier workspace rejection did not recur in this run's delegated
route; there was no new direct allocation to test the revised default.

Writer `hFaMTwX` produced `a7cd6e1e354af01464f24359c137eb3d91886233`.
Reviewer `UPaVyiI` reviewed the pinned text provisionally, then geometry,
mass, and Weil statements as the writer finished each piece. The writer
recovered from a malformed revset and nonmatching setup and lookup
commands, then completed its own scoped check. The review
resumes registered four empty snapshots, not alternative proof patches.
The reviewer verified the final Lean source on first candidate
`40087805f5850109404cc4e7f5449b634b469934`, base
`d69a8164976ff094b55f2d717f0da7618a516f69`.

The owner built that candidate successfully (events 151–157). A
line-oriented `awk` check rejected its valid joint import because one
`#print axioms` list wrapped at a newline (events 161–165). A multiline
check accepted all 35 reports (167–169). The first adoption was stale
(171–172). The owner restacked the same Lean patch onto
`0a7f05464e5b82cc4061852dfb039f430bfe1627`, verified source and pins, and
reran the warnings-as-errors build and fresh joint import. No previous
Lake cache was copied; each candidate logged 14 rebuilt project modules.
The reports were byte-identical. The replacement
`3b8584b048a2c6a5fa82a87612add28a89e02e02` landed (178–194).
This repeats the [stale-adoption race](../restack-lake-cache/), not the
old allocation failure or the nested-cache copy error. No prebuild
status check was made on the first candidate, and there was no timing
comparison with cache seeding.

The [branch handoff](../../obligations/single-place-norm.md#global-counting-quotient-normalization-for-the-box-fourier-measure)
explains the signed half-open real-cell repair to (A.2.1.1), p. 545,
and the exact checked scopes. It originally recorded the writer checks
but lacked the owning landing evidence. We added the owner session,
candidate IDs, and event ranges so the next worker can verify the
accepted premise without reconstructing session identity from stdout.
The open successor is the general-field dilation step, not another
counting quotient. Neither ramified Gaussian inversion nor GRH follows.

## Small control and decision

In this improvement, run `lake env lean --json` with the same joint
import and check commands used at work events 159 and 182, in the
landed integration workspace. JSON gave 35 signature diagnostics and
35 axiom diagnostics, all informational. The report for
`Masullo.existsUnique_sub_integer_mem_archimedeanIntegralCell` was a
single JSON diagnostic, with newlines inside its `data` field. Match
complete axiom diagnostics to the 35 expected `#print axioms` names
and check exact set membership in the allowlist. A scratch validator
accepted the actual output and rejected three separate mutations: A
missing report, a duplicate report, and `sorryAx` inserted on a
continuation line. This tests report framing and the controls, not a
replacement for statement review or a new proof audit.

Document complete-message checking in the [landing procedure](../../../cmd/godel/README.md#checking-a-proof-candidate),
with JSON as an option, not a parser or new landing gate. Put the owner
session reference in the handoff before integrating, so evidence can
be located without changing a candidate to insert its own hash. Keep
the work/improvement topology: The inherited-input reconciliation,
independent review, and scoped restack worked, and the remaining
failure was report framing. No live routing or executable change.

## Live follow-up: Fixed-Gaussian continuation

Run `01a20567-41b5-7876-b0ed-5f26863a22b8` matches work Yah
`01a20567-4317-7598-a876-3bfb612ca5c2` (input seq. 3, stdout seq. 142).
The archive marker and initial accepted tip were
`6ff80ff6becd42380c7800dddaf81d52477ac50f`. Its `cmd/godel` and
shared Go inputs were unchanged at the work landing. This improvement
is Yah `01a2056f-8344-7f8c-ab83-1ef134597ce8`, with the same marker.
The work followed the matching [previous improvement](../restack-lake-cache/#live-follow-up-corrected-gaussian-mellin-entireness):
It skipped the accepted entire-integral and scalar-mode results and
assembled the missing continuation. It did not recover an unlanded
artifact. It also inspected the intervening audit note, which concerned
an already-closed normalization premise, not the continuation.

- The first writer task stopped before Lean because the prior session's
  recorded cache directories were missing (seqs. 38–49). Switching to
  the available launch cache allowed a build. The next builds found
  local notation capture, missing inherited Borel instances, proof
  elaboration errors, and then unreachable tactics under `--wfail`
  (seqs. 51, 60, 73, 82). These were repaired before the owner build.
- Direct output `abc29e6ffc30d87fda2560b704a881f81a0dad6d` integrated
  on `e7cf12509d9926d58b33c64fcc9be7b8e356ed99` as
  `e593c9ce04bdff9151644ea015358d2e45685d3d`. Reviewer `bSxnAsU`
  checked the frozen endpoint and exact first candidate without a build
  (seqs. 115, 126). Its output `a01a969abf619b02a34e809b4ec480e54fddc8ff`
  was a read-only snapshot, not a competing proof. The reviewer used
  pinned Markdown, layout, and limited Braille raster transcriptions.
  These are text-mode controls, not a direct rendered-page image review.
- The first owning build passed (seq. 108). A JSON checker rejected
  valid signatures because `#check @Name` printed `@Name` and the code
  matched `Name` (109–114). Unlike the earlier wrapped-list failure,
  this was signature matching, not axiom framing. The later status
  found a different accepted parent; the owner did not attempt stale
  adoption of this candidate (120–130). No prebuild check was made
  at this decision, and the record does not establish that one would
  then have found the move.
- The restack on `a2f09a7a1fc08da97e122ad19cb64890e1d321a8` preserved
  the proof patch. Its warning-failing build rebuilt the endpoint in
  its own workspace and the fresh full joint diagnostic matched the
  first full report. The owner adopted
  `5401cebe488cc9a65902161f0054ca7c0e223c70` (131–141). See the
  [theorem handoff](../../obligations/single-place-norm.md#meromorphic-continuation-of-the-fixed-gaussian-euler-product)
  for the normalization, scope, and the separate contour obligation.

**Bounded replay:** On the actual first-candidate JSON output, match
signature diagnostics after removing at most one leading `@`, then
require exactly one signature, defining module, and complete allowed
axiom report for each of the three expected declarations. The original
prefix test failed; the corrected test passed, and it rejected a missing
signature, a duplicate signature, and `sorryAx` on a continuation line.
This tests report matching, not the reviewed statements or a new proof.

**Decision:** Clarify the optional signature matcher and distinguish a
missing prior cache from a bad copy layout. Keep the exact-candidate
checks, optional preflight, and current topology. No live router,
standalone parser, or timing experiment was run.
