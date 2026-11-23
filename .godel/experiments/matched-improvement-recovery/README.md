# Recover checked artifacts from the matching improvement

Work consumes the previous work stdout, not the improvement stdout.
Accepted-source reconciliation finds a theorem that landed, but cannot
show a checked output that failed to land. Do not replace that first
check or redirect fresh operator input. Before re-proving or reviewing
an open premise of an inherited branch, consult the improvement report
for its exact matching handoff. Keep recovery subject to the normal
audit and adoption rules.

## Read-only replay

On Yah session `01a2024e-3cb0-7637-a30e-2fcd59084880`, use the
manifest entry for the stable launch `cmd/godel` to identify program
`dKyvGKV`. For each archived consumer, select the most recent earlier
record whose nonblank `final_response` equals the consumer's `input`,
ignoring only trailing CR/LF. From its `improvement_response`, select
the relevant artifact by hand. At the consumer's initial campaign pin
and the artifact's stated revision, check the named module using
`jj --ignore-working-copy file list`. Run IDs and pins identify the
archived observations:

| Consumer run | Initial pin | Result |
| --- | --- | --- |
| `01a20221-ad41-7cd1-a940-01bc52c5d194` | `13dfbec9f1a7387f3d6f9875da8313a58a5e23a0` | Integral trace was already accepted. Skip it, as work did. |
| `01a20238-136c-71a0-beec-b24a5c7b73bf` | `6dcfdcf66739d8c8f9160b9ab18023a25570fb61` | The codifferent module was absent, but reviewed output `ad1278d2f1ac7b12a758c168d3a0c3f475ebc88f` was named and readable. Work started and cancelled a fresh review before proving a separate determinant lemma. |
| `01a20246-e027-77a2-a84d-36718d1fac4d` | `1f69a0f8b3bb323c4d7d3f259dbad80c855b92d2` | The codifferent module was still absent, but the report named readable, audited candidate `3fd76a6320165bd44c7b9ee45e785e19e99f32b0`. Work checked the accepted branch and chose the distinct trace-index theorem. No duplicate codifferent proof was attempted in this run. |

The predecessor IDs were respectively
`01a2020b-9feb-7d85-b6e0-ecefb45333aa`,
`01a20221-ad41-7cd1-a940-01bc52c5d194`, and
`01a20238-136c-71a0-beec-b24a5c7b73bf`. The first two rows repeat the
previous improvement's controls; the third is new. A synthetic fresh
objective, `Prove a new lemma on a fresh topic.`, had no match.
The two inactive artifacts are successive versions of **one** proof,
not two independent failures to adopt different results. This replay
checks linkage and source availability, not how a model chooses.

## Recovery and decision

In the same improvement session, the proof was recovered unchanged
from the audited stale revision. Its accepted restack,
`63d3f29f3b2f85ccaebd44ff34b065176220bcb9`, passed the full
warning-as-error Lean build and kernel replay with the independently
reviewed signature and only the permitted axioms. This validates the
recovery route for this artifact, not the effect of the new prompt.

Install only a work-role prompt rule: Use the matching earlier
improvement as a read-only lead for an exact, relevant artifact;
check accepted scope first, and recover the missing result only when
useful. No new router, state, or loop transport. On a future live
handoff with a checked but unlanded artifact, check whether it is
found before work starts a redundant proof or review. No such live
launch was run in this experiment.

## Live control: The matched result had already landed

Run `01a2043a-57b8-733e-a42b-d4b230c40abe` used the lookup in
Yah work session `01a2043a-58d6-7878-bb85-cb20d5ba2214` (main
sequence 17). The prior work response concerned a blocked trace test;
its matching improvement reported the Gaussian zero modes and the
Archimedean trace-dual and covolume results. They were already present
at the run's initial pin `253ee3543f5f465600ff1b64be0d559a3231d22a`.
Work advanced to shifted fractional-ideal Poisson and adopted
`aca6533d21b24a10276e26e59845e83e83f43a64`. Do not repeat the earlier
proof or change the router. This is a live control for recognizing
accepted work, not evidence that the prompt recovers a missing artifact
or that the lookup was necessary to choose Poisson.

## Live recovery: The rational sharp lower edge

Run `01a2060d-0cde-786e-bed0-d345aa820e8f` matches work Yah
`01a2060d-0e81-7500-b3fb-99f77cce99e8` by input and final response.
Its launch archive and initial accepted tip were both
`820e31dc3ac7d12f8a2a55428be5301e79be5fc4`. The exact `cmd/godel`
tree did not change from launch through the proof landing.

The matching predecessor was run `01a205f3-b042-70c5-b4ee-11c828c73b83`.
Its work Yah `01a205f3-b1d1-7885-8c36-002f23511cea` landed the
base-normalized shell obstruction and sent work to the real cutoff.
Before the relay, its improvement Yah
`01a20600-0b90-72df-9dc0-e6ee02533f8c` had already drafted, built, and
jointly checked both sharp cutoff modules after fixing six draft
failures. Child `hczFLOo` reviewed the mathematics and checked rendered
crops of the lower endpoint, integration range, and width conditions.
The original owner's preflight caught candidate
`3b34914c41c52999fe80312a7f2bcb936cb94848` already stale (seq. 176).
The replay `47e0d12f3bd4b90d9cdd62a6f0b6587cc31c80b6` conflicted with
an intervening smooth-cutoff audit in overlapping documentation
(seq. 182). Opening that candidate as `on` failed because the attempt
had no Change-Id (seq. 189). Neither candidate landed. The improvement
response identified clean output `967aa271265557474a73e96f97da65573da13640`.

Work recovered the matching response after correcting a `jq` filter
(seq. 16–23). Neither Lean module had landed. It allocated without
`on`, restored both files from the clean output, reconciled the notes
with the smooth-cutoff audit, and got a fresh fixed-statement review
from child `LsYRkSt`. The review was text-based this time; the earlier
rendered evidence was retained only for the clauses it covered.
The first integration `c7f97b887a47ee2c9957804defdf9c050696ee9e`
passed the preflight and exact checks but became stale before adoption
(seq. 57–72). The intervening strip-trace statement added three unrelated
Lean files. Work replayed the now registered output, checked the new
base, rebuilt both targets, inspected all nine declarations together,
and adopted `d78f64c53d86b5cb609c78286007e2311b63f03c` (seq. 75–90).
The accepted Lean files are identical to the original clean output;
all nine declaration checks showed only the three allowed axioms.

**Decision (improvement Yah `01a20611-b76e-7946-91c9-23d09590b3b1`):**
Keep the matched-handoff lookup. It recovered an actual missing result,
not just an already landed proof. Clarify the existing recovery guide:
Reapplying a clean patch in a fresh workspace on accepted source is not
opening a conflicted candidate for in-place repair. The former worked in
the successor; the latter requires a Change-Id. Neither path removes
exact-candidate checks or the adoption race. No new router, automated
restacker, or prospective timing claim.

The [accepted proof handoff](../../obligations/trace-real-prime-q.md#lean-checked-path-dependence-of-the-retained-position-edge)
records the scope: The reconstructed scalar is path-dependent, but a
rate-controlled repair is not excluded. The next test is the orbital
term of one specified common global diagonal on below-one two-moment
profiles, not another lower-edge scalar computation.

## Live control: The Mellin adjoint

Run `01a20634-adc6-7be5-9974-acd56246d990` matches Yah work
`01a20634-af61-7ca4-9490-2b578475735c` by input and final response.
The launch archive and initial pin were both
`d17819758975e1028f23f72d46270931000adc11`. The program tree was
unchanged at the proof landing `26f82503eb6462d309a90de2be6ff0072cc335b8`.
Improvement is Yah `01a2063d-ecee-7326-8380-8653c1f76677`.

The inherited handoff proposed building the tail measure. Work
identified predecessor `01a20615-9bca-76f9-99c3-bf4ff4a96428` and
its improvement (Yah `01a20624-d19d-7566-86d3-0dc22f4adc92`). That
improvement had already landed both the tail measure and assembled
filter. Work checked the accepted definitions before advancing to the
adjoint. This was not an unlanded-artifact recovery. Looking up the
manifest value as an object failed (work seqs. 8–11); work recovered
by reading the known run record. In the earlier lower-edge recovery,
`jq`'s `input` function was used in place of the `.input` field and
failed before the successful recovery (earlier work seqs. 16–23).
Neither lookup error stopped work.

The independent adjoint review (`CZRgWxT`) checked fixed statement
text against p. 599, (B.2.1.29–31), and the Chapter 12 trace interface,
using the digest-matched PDF layout and Markdown but not rendered
pages. It confirmed the adjoint sign, positive shifts, and the compact
support argument avoiding the singularity at zero, and distinguished
Lean's totalized inner integral off the seed support. Two writer builds
failed on Lean elaboration before the corrected proof passed (seqs.
46, 53, 62). The one integrated candidate combined the proof and
its landing note on accepted base `b157758a58ecc9f807eb22bfa409c58ecfb53cff`,
which had advanced by unrelated changes (seqs. 78–85). The exact
candidate passed the warning-free scoped build and fresh joint import,
with only the three permitted axioms in all six reports, and was
adopted (seqs. 90–93). No stale or unadopted proof candidate remained.
This is a live success of the flat landing workflow, not evidence
that it prevents a race.

**Replay and decision:** Run the [read-only lookup recipe](../../../cmd/godel/README.md#finding-the-matching-improvement-report)
on the two saved consumer records. It returned the already-landed
filter report and the unlanded lower-edge report respectively. It also
accepted appended CR/LF and rejected an appended space and a fresh
objective. Document the manifest schema and point work to the recipe.
Do not install automatic routing or relax recovery and exact-candidate
checks. The replay did not run a new work node or measure a speedup.

**Proof scope:** The adjoint is one checked dependency of the rational
below-one witness. Its [branch handoff](../../obligations/trace-below-shell-q.md#remaining-separation-of-the-transformed-densities)
retains the concrete next lemma: Prove nonproportionality of the two
filtered densities on an open positive-log seed interval. The new
`rationalRadialStripIndexEquiv` at
`7da5f9b18bb29014d436c052d8c7a6c0348742a7` identifies the scalar
strip index and multiplicities. It does not supply the omitted-zero
reciprocal-height budget, the common global operator trace, or the
necessity of the modeled local projection. Keep those premises
separate rather than repeating scalar reindexing. Neither the adjoint
nor the index identifies the manuscript's actual shell.

## Live follow-up: The rational filtered densities

Run `01a20642-d96e-7358-a3d2-b6630b738a6b` matches Yah work
`01a20642-dbdb-7b6d-b0e5-218cf3eaa9e9` by input and final response.
The launch archive and initial pin were both
`47eb4b607ef17236bbc0e82d00a4346d7dc3d0a8`; `cmd/godel` was
unchanged through the work and improvement proof landings. The
read-only recipe selected predecessor
`01a20634-adc6-7be5-9974-acd56246d990` (work seqs. 18–19).
That report had no unlanded proof to restore. This is a live check
against the earlier lookup-schema errors, not a measured speedup.

The selected inference was that the two adjoint densities are not
proportional on any positive open interval. Coordinator `QSEXZpC`
split the derivative factor and analytic averaging between `TOnhLmU`
and `GHtGqnv`, respectively, then assembled the leading-limit,
first-term removal, and analyticity endpoints in checked output
`8f0a0a73abf24af52933855ff39c52001f4338b9`. Independent reader
`EPtymgE` checked the fixed nonproportionality contract, including why
no assumption on the second raw coefficient was needed. The owner
corrected draft elaboration errors before registering endpoint and
note output `22eb66efac29c8af0f1cfb2a382a9e5fdc48affa`. A stale
candidate `dce3c21d098c6db801e318be4bbff5a3f6aba4d2` was caught
before its build (seqs. 114–128). The flat replacement combined the
same proof outputs, passed the exact build and joint-import checks,
and was adopted at `eac79512a9175e5d9f96682d2b7938a76dfcba66`.
No separate proof from the superseded attempt needed recovery.

Improvement Yah `01a2064d-01df-7985-9550-7d5295c124ee` used that
result to select one smooth seed and impose the two trace pairings
and Mellin zeros on the same filtered test. After two draft builds
failed on imports and unfolding, the assembled endpoint built.
Reviewer `mndmHjP` checked fixed contracts, adjoint and Mellin signs,
and the manuscript interfaces via pinned Markdown and layout, not
rendered pages. Candidate `e1c12a941f29245bdb1e41bea52b0b2489c04602`
passed checks but became stale after its preflight. The same patch
was checked anew and adopted at
`231909b11e1ee1f770dc248731645774dd5d3fbb`. The saved JSON reports
matched after correcting an optional jq comparison expression; all
three changed declarations use only the permitted axioms.

**Decision:** Keep the tested lookup, fixed-statement review, and
one prebuild comparison. This iteration does not support polling,
a new router, or a workflow change for local tactic and shell errors.
The preflight caught one move and cannot catch a move after it.
The [proof handoff](../../obligations/trace-below-shell-q.md#checked-short-filtered-separator)
separates the new checked witness from its unmet actual-zero budget,
strip/full trace comparison, and manuscript necessity argument.

## Live follow-up: Budget the actual omitted divisor

Gödel run `01a20655-d822-7ec2-ae05-04b317b25977` completed
without a work failure. The run's input and response match Yah work
`01a20655-db3c-7878-9b63-9a84a996229f`; the improvement owner is
`01a20665-8398-7aef-960a-b6623a4acd80`. The launch archive was
`d28691bf4b4e48f648e1746c45ac02217696a335`, while work first
observed accepted `3809bb9a96263828effac6b53ee3cad23cf0cc54`.
The executable's `cmd/godel` tree was unchanged through the work
landing. Work used the matched predecessor from the preceding
[follow-up](#live-follow-up-the-rational-filtered-densities), found
the already-accepted separator, and advanced to the conditional
actual-zero support budget rather than repeating separation.

The work owner repaired seven unsuccessful draft builds and obtained
independent reviews from `vRpfWol` and `izzEkMr`. In particular, the
second review distinguished a displacement budget over distinct
locations from an order-weighted bound on a nonvanishing residual.
One exact Mellin zero per location makes the latter unnecessary for
this construction. Direct output
`c02222b8b99606ecc80b117f4cd77e815b7fbc0f` was checked on three
integration bases. The first two candidates,
`59e911b0c71c8a5d569c61bbcfc7f42ca64424b6` and
`07fb71b6c65d55f3890493eca5714db51a67540a`, were current at their
prebuild queries but stale at adoption; the third was adopted at
`824c5ba148a1afe5b0187da2a99e732274cc17a7`. See work seqs.
154–246 and the two review subagent records. The first two builds
were not avoidable by the tested preflight: The intervening moves
were later. No failed or superseded integration contains a distinct
proof needed downstream.

The improvement then assembled the actual-zero separator without
changing its density hypothesis. Writer `emowkVz` checked the three
new modules at output `8043871f9cd61d47199bf358575d65ac5f133f38`;
`IPgWAzB` independently reviewed the fixed endpoint. The writer used
one padding construction for empty, finite, and infinite high tails.
In parallel, the owner added the rational Haar reflection and the
scalar strip transfer; `CJtGPsL` reviewed both fixed statements.
One draft build exposed a reflection simplification and a function
composition mismatch; a subsequent check also exposed an importer
named with the wrong path. Use the module paths at the exact candidate
for the target list. The first combined revision
`9c1ca8c3343b55f83147b5d6ab253b848637b580` moved out of date before
building. The identical diff built on
`6edaf717f350275ba9dbabd80135ce9319ad8bbf`, but adoption was stale.
The owner checked the unchanged patch on the new base and adopted
exact revision `c1d9906c831ff0c9380c9bacd83d5b66bcd67c51`. Its
warning-fatal build included all ten changed or affected modules, and
five endpoint signatures and axiom reports matched the prior candidate
on a fresh joint import. Each report contains only `propext`,
`Classical.choice`, and `Quot.sound`. The integration and checks are
in Yah `01a20665-8398-7aef-960a-b6623a4acd80`.
See the [checked witness handoff](../../obligations/trace-below-shell-q.md#checked-conditional-witness-for-the-omitted-divisor).

**Decision:** Keep the current routing and one prebuild comparison.
The recurrence is a concurrency race, not another misidentification
of a handoff or a demonstrated benefit from more polling. No new
router, Go change, or policy experiment was run. The [branch handoff](../../obligations/trace-below-shell-q.md#conditional-budget-for-the-actual-omitted-divisor)
separates the checked reduction from the unformalized density bound
and the global trace hypotheses.
