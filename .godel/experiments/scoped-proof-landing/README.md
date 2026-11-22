# Scoped proof checks on a live restack

## Trigger

`daeaa4e3432b2be499c10fb1ee6495911dc765cc` replaced routine
full-project builds, joint imports, and separate kernel replay with
exact-candidate checks on changed and affected modules. The question
here is whether the new path landed a reviewed proof after a real
target move, not whether it detects all regressions of a full audit.

## Live observation

Gödel run `01a2045d-9ef9-7059-ab0d-79b50927a6b7` matches Yah work
session `01a2045d-a01b-7729-b120-5b495e87d33d` by its input and
final response. Both the executable's archive marker and the initial
campaign pin were `c8decb206e146298ae87d7e2501af66c77f8e1ff`.
The matched predecessor improvement had already landed diagonal box
pullback and the corrected diagonal phase at
`1ec528e0b9f4fb96d51efb7860b5488171aab606`. The work node took the
next missing inputs, arbitrary-box dual support and translated phase,
rather than redoing the preceding stdout's suggested coset proof.
This was not recovery of a missing output.

The first writer build failed on the local scalar-module instance and
valuation rewrites; the revised source built without weakening either
endpoint (main sequences 48 and 55). Review child `VbyJETV` checked the
actual writer statements and sent its mathematical verdict before the
first adoption attempt (106); its final report followed adoption (132).
The relevant pinned passage is Example A.3.1.10, (A.3.1.8), PDF p. 558,
not Example A.3.1.8. The reading was text/layout only. See the
[branch handoff](../../obligations/single-place-norm.md#checked-finite-box-fourier-support-and-phase)
for the checked scope and distinction from global theta inversion.

| Exact candidate | Base | Check and outcome |
| --- | --- | --- |
| `8a725bfed4461fd42a2c4ac115d80b5fdccf1a30` | `beec9711ce91e866712d93df734f572d220deac1` | Scoped build and endpoint import passed (88); stale at adoption (108). |
| `54bc21bdee59a871dcd00a776c08037cb3906d66` | `bdc7fec3eda49451961a66810d7c8c34ec7fe914` | Same complete patch against its new base (114–115). Scoped build and endpoint import passed again (120); adopted (122). |

Both attempts used writer output
`440784f9102958d0cda8628e2aae57c04935b35e`. The restack changed
only Walk code and docs outside that patch. The owner built
`+Theorems.FiniteBoxTraceDual +Theorems.FiniteBoxDiagonalCoset` with
`--wfail`, imported both modules together, and checked the built
binders and axiom reports for
`Masullo.mem_traceDual_finiteIdeleIdeal_iff` and
`Masullo.finiteBox_tracePhase_eq_diagonal`. Both used only
`propext`, `Classical.choice`, and `Quot.sound`. The build reported
2.6 seconds for the new module each time. The restacked check returned
about nine seconds after task launch. The 574-second work invocation
also included investigation, writing, review, and the target move.
Those totals are not an audit-speed benchmark across different proofs.

## Disposition

Keep the scoped landing procedure and current routing. The preceding
Poisson run `01a2043a-57b8-733e-a42b-d4b230c40abe` also recovered a
stale candidate, but under the historical full-audit procedure. In
this run the replacement is routine and no cache-copy step was
needed. The status probe at 102 still saw the first candidate's base;
it did not reserve the target or prevent the stale rejection. Use the
existing stale result and restack path, not a polling node or a
pre-adoption status loop.

This observation is not a full-project compatibility check. The
[earlier collision control](../joint-proof-import/) still demonstrates
a failure that selected imports can miss if they omit the conflicting
module. No new prompt, program, or prospective A/B trial was installed.
