# Recheck the parent before a costly candidate build

## Trigger and test

Two recent finite-box landings built their first exact candidate and
then had to restack. Test a single read-only decision, not a new node:

> Immediately before starting an integrated build, if the candidate was
> made directly on the accepted target, compare its base with the now
> accepted revision. If the target already moved, follow normal recovery
> before building. Otherwise continue. This does not apply to an
> intentional stack on a pending parent, nor does it reserve the target.

Replay from the timestamps and accepted IDs available to a status
query at that decision. For the positive case, use the independent
adoption receipt already emitted by the other session at that time.
For the controls, the candidate still had the accepted base at a
later recorded status query. This tests only the selected action, not
whether a prospective run would recover faster or advance the proof.

| Case | Evidence at the build decision | Replay | Actual result |
| --- | --- | --- | --- |
| Translated-box Poisson, run `01a20482-da2e-798c-90a5-42107523dcd4`, Yah `01a20482-db51-7fa6-bd56-fdff5ef6ac22` | Candidate `5f1dd0ff5baa5d8ff9052128f08259cc1d049db5` based on `712bcb9f1779c490a3c8b7040d94d55c6a24ddea` (seq. 88). Walk session `01a20483-6fa5-7a13-9921-a0bcc5df2c54` adopted `110c36e6908673da5c0202f59a05237f597c7d2d` (seq. 73) 12.65 seconds before the build call (Main seq. 91). | Reconcile and restack before building. | Build and joint import passed on the old base; adoption was stale. Same patch restacked and checked at `f40f070bd2aea23b3d0b2879d81f7314929f4cde`, which landed. |
| Box support and phase, run `01a2045d-9ef9-7059-ab0d-79b50927a6b7`, [prior scoped landing](../scoped-proof-landing/) | Candidate `8a725bfed4461fd42a2c4ac115d80b5fdccf1a30` still had the accepted base `beec9711ce91e866712d93df734f572d220deac1` at seq. 102, 71.9 seconds after the build call at seq. 82. | Build. | Adoption nevertheless went stale. The retry landed after a fresh check. |
| Box Fourier product, run `01a20473-40c4-7ed7-bcb6-b828fa313079`, Yah `01a20473-41ea-784a-b041-316d86880af7` | Candidate `88a3e65a3e75b353e855329a127d87d094f1eb20` still had the accepted base `b8cabd6eb671c4db055ea68ff68acfed4fe16d1b` at seq. 138, 23.6 seconds after the build call at seq. 128. | Build. | Scoped checks passed and adoption succeeded without a restack. |

## Proof decisions in the latest iteration

The run input and final response match the listed Main session.
Its baseline archive marker and starting accepted pin were both
`7cef9eea71d25e41c25980abe0998a45d99b5f51`; the `cmd/godel` tree is
unchanged at `f40f070bd2aea23b3d0b2879d81f7314929f4cde`. The matched
prior improvement (Yah `01a2047b-f88e-7f1f-bbe0-8db92c92fc62`,
reviewer `XgQoRQE`) landed shifted trace-measure Poisson at
`3b6421e3e68b5f316c4a5abd1fc9e85dd8ecd8d0`, discharging the first
step in the inherited stdout. Main skipped it, found no relevant
accepted audit finding, and assembled the full diagonal sums instead.
The previous run likewise skipped the already accepted centered-mass
identity before proving the finite Fourier product. Neither was a live
recovery of an unlanded checked artifact.

Main's first three writer builds failed on subtype reindexing,
local definitions in the support split, and explicit coercions.
The fourth built. Reviewer `chDkZnH` first reviewed the obligation and
pinned text, then the exact first integrated statements. The restack
changed only the Walk note outside the proof patch. Main checked the
built binders and all three axiom reports on the new candidate before
adoption (seqs. 115–123). The [proof handoff](../../obligations/single-place-norm.md#full-diagonal-poisson-sums-for-one-translated-finite-box)
separates that result from an identity for the global Fourier integral.

## Disposition

One unnecessary integrated check sequence was avoidable in the replay.
A status query at that point would not have helped the earlier stale
case. Document an optional single preflight when a costly check and a
plausible concurrent adoption coincide. Keep exact-candidate review
and stale recovery unchanged. No Go, routing, or polling change; no
prospective latency measurement or full-project compatibility test.

## Live follow-up in the same improvement

Yah `01a2048a-b0d1-738f-834c-e3fa0194075b` integrated the additive
stage-Haar patch as `2e2cf536cfa55931215edb138bc77cf0e9ed219c` on
`c156ef7be1a891a71e170df212fcc698a610f7be`. Before starting Lean,
one status query showed the accepted tip was already
`0342564585491fbce6725c6e1f7b65f07d239f42`. The intervening change
added a decision note only. The unchanged patch was restacked,
built, checked, and adopted at `5ebb1863c3039c8c8d54c428f6624b4bae43a788`;
the first candidate was not built. This confirms a live change in
the build decision, not a measured time saving or a guarantee
against a subsequent race. Keep the preflight optional.
