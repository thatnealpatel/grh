# Seed the replacement Lake cache without nesting it

## Trigger: An additive Haar landing, not a proof stall

Gödel run `01a20499-68ae-7e8d-9829-cfa0ccd36764` matches the input
and final response of Main Yah session
`01a20499-69f0-72e1-8653-addac09cd2dc`. Its archive marker and initial
accepted tip were both `616d0d9cf09c353ffb2c1ad48c640bdf50bd7e5d`.
The `cmd/godel` tree at that revision is unchanged at the work handoff
`876b4e389391d1c337d4a89c25a359cb6c92721c`. This assessment is the
improvement session `01a204ae-bdcf-7f6f-956d-d795cc54529a`.

Main reconciled stale stdout from the preceding Poisson run
`01a20482-da2e-798c-90a5-42107523dcd4` with that run's matching
improvement (Yah `01a2048a-b0d1-738f-834c-e3fa0194075b`). The latter
had landed stage Haar at `5ebb1863c3039c8c8d54c428f6624b4bae43a788`.
Main skipped reconstructing it and chose cofinal stage comparison on
the actual adeles. This is another successful skip of already-landed
work, not recovery of an unlanded artifact.

Writer `dJpXzLv` finalized `2943cd5cdaa893255a0f3d02e365f84d46d97e2c`
after draft errors with local compactness, missing imports, a Haar
comap instance, and measure/coercion rewrites. Reader `lOZnIHc`
reviewed the endpoint signatures and calibration, not the build.
The adopted theorem constructs regular additive Haar with the prescribed
stage comaps, unique among all Borel measures with those comaps. It
retains non-unit finite masses and does not prove the counting-quotient
normalization. The [proof handoff](../../obligations/single-place-norm.md#restricted-product-additive-haar-on-the-actual-adeles)
records its provisional source readings and runnable successor: The
continuous finite-adele trace character and the translated-box global
Fourier integral. Neither ramified Gaussian inversion nor the trace
comparison needed for GRH follows from this landing.

## Observed restacks

All five candidates had byte-identical patches against their respective
bases. The first preflight at Main seq. 96 was current; the first build
was necessary at that decision. Four intervening adoptions then made
candidates stale. Neither the preflight nor a cache can reserve the tip.
Compare with the [earlier preflight control](../prebuild-stale-check/),
where a status query found a move **before** the build, and the
[earlier post-build stale adoption](../scoped-proof-landing/).

| Candidate | Cache action | Project modules logged `Built` | Adoption |
| --- | --- | ---: | --- |
| `8a8807b73c3a9ce0f8607dc5f030ddf4c0681019` | Initial build | 65 | Stale, seq. 126 |
| `8f58012ff0801c62b63f4f3fc836b1affc0e1b5d` | Copied whole `build` onto existing `build` | 65 | Stale, seq. 158 |
| `50327388403c47679280e258f5ac721a9d52b533` | Same copy | 65 | Stale, seq. 192 |
| `81cc28fca42768ac0623ee6f383dd5cf4287240b` | Copied `lib` and `ir` into `build` | 0 | Stale, seq. 213 |
| `c363549d11af7aa056a75a8ab0b71160a60bdf49` | Same child-directory copy | 0 | Adopted, seq. 225 |

The second and third integration workspaces contained nested
`.lake/build/build` directories. The final two inherited the built
Lean artifacts into the correct paths. The final candidate still ran
`lake build --wfail` on 67 targets and a fresh joint import in its own
workspace. Its signature and axiom report matched the first checked
candidate's byte for byte; all 20 reports had only the allowed axioms.
“No modules rebuilt” means cache reuse, not that any landing check was
waived. The live run did not compare elapsed times on matched inputs.

## Small replay outside the project

In scratch, with Lean `v4.36.0`, make a Lake package with a `Control`
Lean library. Give `Control/Seed.lean` the definition
`def cachedValue : Nat := 1`, and give `Control.lean` the import
`import Control.Seed` and the theorem
`theorem cachedValue_spec : cachedValue = 1 := rfl`. Build `+Control`
with `lake build --wfail`. Make three source-only copies and create
`.lake/build` in each before copying any artifacts:

1. Run `cp -a "$prior/.lake/build" .lake/build`. The `.olean` was found
   under `build/build/lib` and Lake rebuilt both modules.
2. Run `cp -a "$prior/.lake/build/"{lib,ir} .lake/build/`. The `.olean`
   was found under `build/lib`, the same Lake command rebuilt neither
   module, and `lake env lean` freshly imported `Control`, checked
   `@cachedValue_spec`, and reported no axioms.
3. Repeat the second copy and change `cachedValue` in `Seed.lean` to
   `2`. The same Lake command rebuilt `Control.Seed` and rejected the
   now-false `Control` theorem with a type mismatch. The cache did not
   make this edited dependency's dependent theorem pass.

The control isolates the destination layout and one invalidation case.
It is not a general validation of Lake cache invalidation or of arbitrary
reuse across changed inputs.

## Decision

Document the correct optional copy for a restack with unchanged Lean
source, pins, and build environment. Continue comparing the exact patch
and running the build and fresh import on the replacement candidate.
Do not learn a polling rule from this run or treat the previous verdict
as evidence for the replacement. No executable, routing, or proof change.
