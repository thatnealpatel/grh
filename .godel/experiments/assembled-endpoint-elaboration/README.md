# Elaborate the assembled endpoint

**Decision:** Clarify the existing writer-workspace advice: Check the
assembled endpoint with its intended imports and supporting modules as
soon as they are available together. If that first happens at integration,
the required candidate build is the check. Keep the exact-candidate review,
build, joint import, and axiom gate. Add neither a node nor a second build
requirement.

## Observed work

Gödel run `01a204ec-e3e8-70cc-ac4c-4a03ae276a24`, work Yah session
`01a204ec-e522-72e2-899d-3d969158c45b`, launched from
`c39dc760e774083bf3154616de7f568b90c9c50e`. The counting quotient was
already normalized, so work took up the additive Haar dilation needed
for pointwise theta inversion, not a renormalization of the Fourier
measure. The Archimedean and finite-stage writers returned checked outputs
`5228df142b4bbe08f4b398e0a79abd519623e4db` and
`2986113c78beb01bce757df1e0513cb24856ebe0`. Independent reviewer
`tvjBEhf` checked the statements of the two supporting results and the
assembled global result. The owner appended the global calibration and
Haar uniqueness argument after the scratch helper check (event 116).

| Candidate | Outcome |
| --- | --- |
| `afe25eb0b93cdd5eea813a5efe08f3409ee810b9` | Owner assembly alone; no check or adoption claimed (event 124). |
| `c1ae9dd3a079b9038cf103e09696b6097e02da25` | Joint build rejected two missing instances in `Theorems.AdeleAdditiveDilation`; both supporting modules built (event 138). |
| `2c5dc76cb35d430a043a81bfd6f6ec23966d5b27` | Owner repair alone; no check or adoption claimed (event 160). |
| `9cd4a86e72a2fb969092a97d3bd1ac10b787bcbc` | Repaired build and import passed; stale adoption (events 169, 171). |
| `2467f8e0970b5cd339529ff4e0230ba1c2c16902` | Fresh checks passed on restack; stale adoption (events 182, 184). |
| `9012d9ed33a1c6be2c2a3f4793dd044f61b7d289` | Three-target build and five endpoint signature and axiom checks passed, then adopted (events 193, 195). |

The repair uses the actual infinite adele ring's local compactness
instance and transports the Hausdorff instance via its Euclidean
homeomorphism. It changes no statement. The accepted result is the Haar
image law for all number fields, and its comap and pushforward forms, not
theta inversion. See the [proof handoff][handoff] for mathematical scope.

## Bounded replay

Improvement Yah session `01a204fb-743c-77fe-90d7-c26d94ced3b8`, task
`module-boundary-replay`. Compare the failed joint candidate `c1ae9dd...`
and the accepted `9012d9e...` above. The two support files, pinned
Lean/Lake inputs, and endpoint module header/imports matched. Extract
`Proofs/Theorems/AdeleAdditiveDilation.lean` at each revision with
`jj --ignore-working-copy file show -r 'commit_id("...")'` into scratch.
Use the same built support for both: In the retained accepted integration
workspace, `lake env lean -DwarningAsError=true` on each extracted file
is the equivalent check. The replay used the accepted workspace's built
project imports and the work build's Mathlib paths with Lean 4.36.0.

The earlier file failed on `LocallyCompactSpace` for the Euclidean mixed
space and `T2Space` for the infinite adele ring. The repaired file
elaborated. Thus a check of the assembled source can detect these defects
once its dependencies are available. This is not a diagnosis of Lean's
module system. It does not show that the check was available before
integration in this run, that it would prevent stale adoption, or that
the advice saves time in a live run.

## Prior controls

The preceding counting-quotient work
(`01a204d4-bbaa-7958-8d25-cf4a5563a5bc`) passed the integrated build;
its reported failure was [line-oriented parsing of an axiom report][axioms].
The earlier box Fourier work (`01a204c2-4e06-7b99-99f8-5aeeddb2ff5c`,
Yah `01a204c2-4f2b-73b9-ad63-5fdca6cd4879`, events 121, 128, 143)
did catch composition errors in a draft, after one missing-support import.
Neither is another observed instance of the accepted gate being the
first check of a module appended after its helpers passed. Stale adoption
is recurrent, but the live failures here do not show that an additional
preflight, cache policy, or routing node would have helped.

[handoff]: ../../obligations/single-place-norm.md#additive-idelic-change-of-variables-for-the-box-fourier-measure
[axioms]: ../wrapped-axiom-reports/
