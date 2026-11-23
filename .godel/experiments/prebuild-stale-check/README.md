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

## Later control: Signed finite Hecke rectangles

Run `01a205af-ffeb-7e3e-805d-1f8b1310a9ce` matches Main Yah
`01a205b0-0177-711f-a3d6-12ac846dc0be` by input and final response.
Its launch archive and starting accepted revision were
`a36dcd32e6e687da76b7ea30fc9eb0e2aa48b392`. The pinned `cmd/godel`
source is unchanged from `700e00f5ef52eca6dc813921b71de4f4094141b7`.
The previous improvement (Yah `01a205a6-2328-79c2-827b-75cc5a01356a`,
run `01a2059a-e907-7dc0-978a-71b8587e81fa`) landed the reflection
and left-edge estimate after the work stdout was fixed. Main correctly
skipped that already-landed successor and worked on the finite residues.

Main fixed draft elaboration and lint errors before integration
(seqs. 40, 53, and 64). Reviewer `bOSGsBK` checked the exact
statements and pinned text, not a moving build. Candidate
`395585053820b419ededa8cc4740ddecfafd27a6` passed its scoped build and
joint signature/axiom check. Its base
`6e72a29f2dc679fa7ccfcd9bfb7478ba4212c836` was still accepted at seq. 93,
62 seconds after the build call (seq. 84). Companion session
`01a205b6-d5c7-7f70-92e4-bc6b0b222b29` then adopted
`de80bdedda20b8fe8b504ad5be58e2dcb1639406` (its seq. 45), and Main's
adoption went stale (seq. 118). Main reconciled and replayed the same
patch on `3b265e62969f64e230fa27317cfe0e46f7098999`, reran build and
joint checks, and adopted `942585653bf62c58ddd716324c0443b7aeccc96d`
(seqs. 124, 137, and 139).

The adoption race recurred, but this is a negative control for the
preflight: It would not have averted this build. The repeat status
checks did not change the proof decision. Keep the optional single
preflight and explicit restack; neither a polling node nor a different
proof router was tested or is justified by this run. Improvement took
the unmet [good-height contour limit](../../obligations/single-place-norm.md#checked-good-height-contour-limit)
instead of changing the program. Assessment Yah:
`01a205bb-a8c6-73f3-ae04-5d0c3192ac5e`.

## Handoff control: The unrestricted Hecke zero sum

The input and final response of run
`01a205c5-b9ef-791b-b752-3f2a8b1cc16f` match work Yah
`01a205c5-bb89-7e44-9e38-430cdd04116d`. Both the launch archive
and the starting accepted revision were
`eeefdde0f98bdc6c8a45adaec6f512bc7eec6361`. The exact `cmd/godel`
tree is unchanged from the preceding launch at
`a36dcd32e6e687da76b7ea30fc9eb0e2aa48b392`.

The preceding run's improvement (Yah
`01a205bb-a8c6-73f3-ae04-5d0c3192ac5e`) supplied the exhaustion,
not the unrestricted sum. Its preflight still saw the base of
`5742304ec5a536beb29f57e66a83dea8c3c983c8` (seq. 132), but an
intervening class-theta proof made adoption stale (seq. 142).
The replacement was checked and adopted at `eeefdde0…`.
The next work node found it and did not repeat the exhaustion
suggested by the preceding work stdout.

Writer `iHOybLk` checked slab summability at
`1d8cee812a94d25d8a054b6176ff0af644deb4e8`. Writer `vZYNoOX`
checked the assembled endpoint against that helper at
`03db670f7c304da4c5445fe87710269acad8f535`. A missing cache,
local lint repair, and reviewer path correction did not change
which proof was attempted. Reviewer `HvlMDzp` confirmed the
statement, including the sign and the closed-strip scope; its
text-based manuscript reading remained provisional. No other
integrated candidate was attempted. The owner checked and adopted
`62456265e578e3d2d0b1089753fdfe4e16a29fed` (seqs. 149–151).
See the [contour handoff](../../obligations/single-place-norm.md#trivial-hecke-contour-with-the-unrestricted-zero-sum)
for the checked result and the same-continuation reflection and
local evaluations needed next. Completing those evaluations would
still not identify the geometric trace in Chapter 12.

Assessment Yah `01a205d0-2ca5-73d1-8e5e-8c9c58aafbb4`: Keep the
existing handoff reconciliation and one optional preflight. No
router change, new trial, or post-hoc latency estimate. Independently,
make the already-reviewed positive-width literal-box witness visible
in the frontier so a geometric worker can use it without redoing
the source audit; it is not a Lean result or a no-repair theorem.

## Live follow-up: Cut-output orbital transfer

Run `01a205e4-007b-74d9-8304-a4f185d2eca3` matches work Yah
`01a205e4-0237-7d93-a13b-f9d9dbc59121` by input and final response.
Both its launch archive and its first accepted tip were
`aa79b7171a8529ec766213f4e5d823f5a685541b`. The exact `cmd/godel`
tree is unchanged through the proof landing
`98737322ea237b5e8fbdd87a95b93f597f4a6d29`. The launch included the
preceding improvement from run `01a205d5-8540-7f4e-9f8e-9886762a6d04`
(Yah `01a205df-498d-7a40-9b67-6e9a3a992f86`): Move past the already
checked scalar explicit formula to a fixed-cutoff comparison.

Work tested a necessary condition for one specific repair: The
orbital action must be constant on each cut-output fibre if it is
to be recovered from just that output on every representative. Lean
proves that every fibre meets the orbital-null subspace in the same
rational Fourier band. Independent child `arBwtLA` reviewed the fixed
statements, the nonzero target action, and the source operator order.
The four failed draft builds isolated a decay estimate and reindexing,
then elaboration of the cut convolution; the fifth passed. The preceding
scalar-formula run (work Yah `01a205d5-86e7-72d0-aaa8-0d773ef7e05e`)
also converged through draft fixes with a fixed-statement review,
but adopted its first integrated candidate. These drafting failures did
not require changing the statement or routing to a different worker.

The owner built and jointly checked the same proof patch on three
candidates. The first two passed but were not adopted. Replay one
`status` at each recorded exact-build decision against the latest
successful adoption visible at that time (UTC):

| Candidate | Build call (work seq.) | Base at build decision | Replay |
|---|---|---|---|
| `31f580269dba62c6dc7d87753635164874adf2ea` | 01:00:43 (117) | Still `8f59df9e67ff4d6420e26df0c98b0c3f8fa01109` | Build, as observed. |
| `b68f23b677b150aef65e2248305e9a65c89011db` | 01:01:55 (134) | `f78c72cd8a78beaad182f56048078bedddd59ee9` had been replaced by `9ba3764cc416e68c89aec475ebd964ff53bd963a` | Reconcile before building. The live run did not query again. |
| `98737322ea237b5e8fbdd87a95b93f597f4a6d29` | 01:02:59 (151) | `bd17de18d89e2d61e0c3f8f50eb7a2eac0bd83b9` | Build, as observed. Exact checks and adoption at seqs. 157 and 160. |

The first preflight saw the right base (seq. 115), and the build and
joint import finished at 01:01:06 (seq. 123). The new base was only
adopted at 01:01:18 (Yah `01a205ea-1750-7340-a2cc-3685df6ceefc`,
seq. 31), two seconds before work attempted its first adoption. The
second move was at 01:01:45 (Yah `01a205e9-ac64-7a37-8857-b081ae5d412f`,
seq. 49), after integration but ten seconds before the replacement
build decision. The third base was adopted at 01:02:27 (Yah
`01a205da-c94f-7c66-89af-b3ff997d9d87`, seq. 141). The replay selects
one fewer build of an already superseded candidate at those recorded
choices; it does not predict the revised landing time or which tip
would have been selected on a changed schedule.

**Decision (improvement Yah `01a205ee-89fa-7794-b7ee-186c379522f3`):**
Make the existing just-before-build query explicit for replacements
following stale adoption. No polling, node, or change to the required
checks or to the proof router. See the [branch handoff](../../obligations/trace-cut-orbital-q.md)
for the next mathematical decision. The obstruction is to the direct
fixed-cutoff transfer only: An upstream shell or section still needs
a comparison with the common Haar diagonal, and the scalar limit is
not ruled out. Manuscript correspondence remains provisional pending
rendered-page verification; the nonzero same-band target action was
independently reviewed mathematics, not checked in Lean in this run.
