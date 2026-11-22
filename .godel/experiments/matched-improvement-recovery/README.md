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
or that the lookup was necessary to choose Poisson. The live test with
an unlanded artifact is still outstanding.
