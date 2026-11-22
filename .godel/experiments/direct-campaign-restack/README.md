# Integrate direct work on the live accepted target

## Observed trial

Gödel run `01a20155-9314-70be-8882-05b214b2a62c` matches Yah work
session `01a20155-93ad-7c7b-992e-29bf8853720f` by input and stdout.
The recorded prompt was built from
`bc42366a909bae97277a6a159e45bd7d02493a91`, also the initial accepted
base. The handoff's earlier `6452ac9c56d2c28caec6264ae4c0c68a979adef8`
was an ancestor, not the workspace to edit.

With the finite local zeta draft elaborated, but before the integration
candidate audit, the work node called `integrate` with `on` set to the
initial base. The target had advanced to
`1520ccc0cb8b5c37c6c89fc8b8c1f0ad6ac50f24` through companion and
rational theta Gram work (no Lean changes). The call failed with
`resolve integration base: unknown integration candidate`. With the
same pending direct edit, `integrate` with only `description` finalized
output `1f0b68ab474b3f81385e4859a26487ff02128810` and replayed it on the
new target as `27c8b9bc1d779e7988cf1cbc19e24271bdb94d3d`. The worker
checked equality of the Lean inputs across the replay and ran the full
local candidate audit before adoption. See work transcript events
78–97 and the [proof handoff](../../obligations/hecke-right-line-majorant.md#finite-local-zeta-pairings-with-the-haar-unit-mass-retained).
Independent statement review `mlDzIRC` is retained in output
`f48eaa338965ce0b79cba685588b9017d0f07526`, not a patch to adopt.

## Nearby cases

- Run `01a20131-bbf1-74ac-b0dd-0fa5ec9e1d87`, work session
  `01a20131-bd05-7fe0-b8e3-88674066ebad`, used the description-only
  route when a companion edit intervened. It replayed the complex
  Gaussian result on the new base and adopted audited candidate
  `a575167bc66f178a8bc4d014d69e692f50fc6a80`.
- Run `01a20142-a865-7340-a39e-165e0b452070`, work session
  `01a20142-a90c-7a38-889f-08e70ffe556e`, used the same route on a
  stable base and adopted `6452ac9c56d2c28caec6264ae4c0c68a979adef8`.
  Its improvement session `01a2014a-1914-7e8c-809c-e2bb981aa990`
  hit `resolve direct base: unknown integration candidate` at `new`,
  not at `integrate`. No direct edit existed to replay in that case;
  the new instruction does not diagnose or recover that failure.
- Run `01a20123-4ac1-706e-bb55-84200d92bc24`, work session
  `01a20123-4c3f-750c-8714-234a6bcf4091`, used description-only direct
  integration for the real-place character classification. Its audited
  candidate `f5de9afe9f7ccc921ca7089a5b49a7f0f6bc8598` subsequently
  became stale at adoption. The same output was restacked and audited
  on the fresh base as `795fe749ff84f4d6e5c7f1b9062ff4bbb3e5ab1d`.
  Omitting `on` at first integration would not address this later race.

## Decision

Put the description-only invocation for a routine direct edit in both
node prompts and the local workflow, with a check of the replayed patch
before any audit. Retain explicit candidate-stack and conflict-repair
rules. This is a workflow clarification backed by live success and
failure cases, not a routing experiment or a reason to relax the Lean
audit. It does not prevent the target moving after the candidate is
built, or recover an output from a different campaign.
