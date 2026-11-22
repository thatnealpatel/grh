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
