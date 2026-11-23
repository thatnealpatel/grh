# Review the statement, not the moving build

**Run:** `01a2051b-4b79-74e1-8535-a16c72e19054`, work session
`01a2051b-4cd7-7e71-b5a0-ab4e42a64c13` (matching input and final
handoff, launch marker `28c88313a9505a1ea576a746358f64e94fc4e5a5`).
Review agent `XioDpBF`; improvement session
`01a20522-cddb-7b0c-a62a-3ee14581e0f1`.

## Observed decision

The worker correctly reconciled the prior handoff with the adopted
finite-local decomposition and assembled the finite-stage tensor, rather
than rebuilding that decomposition. The writer base moved to
`024282224262c66e8aeb20a18ade8bebc664ae50` before allocation, and the
integrated base moved to `9426c6794d413b5a30436ba0d8d67409bd04c4e2`.
Neither delta modified the proof inputs. Four writer attempts reported
Lean elaboration or linter failures involving dependent local coordinates,
indicator and integer-ring coercions, or simplification. The fifth build
passed. The clean writer output `fab930cac48d9e2fb8e20721bf83803e4c3b8cdf`
was replayed on the new base. The first exact-candidate build and fresh
joint import succeeded at `8131a11dd83f7dc0498eb55b548ecf2fe2a1c5e3`;
all nine axiom reports passed, and adoption was not stale.

The independent reviewer correctly distinguished the five intended
statements from the full Gaussian identification, and compared their
scope to Definition 3.4.3.2(3), (3.4.3.7)–(9), p. 152, using Markdown
and numbered layout (provisional). But it also ran two builds that
were not needed for statement review. The first had the wrong working
directory; the second tested an intermediate writer proof. By the time
its final report said the candidate did not elaborate, the writer build
had passed. The reviewer's finalized output
`faa8d2512d4f05101b44821cad9d63a49589d2dd` has no source delta and was
not an input to integration. Its mathematical review and the owner's
exact-candidate build are distinct evidence.

## Bounded replay

In improvement, extract the five public headers from the actual Lean
reads in review events 4 and 5, and compare them with the corresponding
source at `8131a11dd83f7dc0498eb55b548ecf2fe2a1c5e3`. Compare the whole
`adeleHeckeTest` definition too, since the theorem headers refer to it.
All five headers and that definition are identical. Read the owning
joint-import signatures to confirm the binders and omitted-place guard.
Thus the early statement review applies to the successful build despite
the changed proof terms. No replacement build or source re-review ran.

The preceding box inversion and its finite-local successor used parallel
independent reviews without reviewer builds (work session
`01a20503-084a-723f-a5ef-b59603c0635d`, review `GxoPgJb`; improvement
session `01a2050d-6f88-7afe-bc8b-1581241c134e`, review `TNqqgXh`). The
previous Haar-dilation run's integrated elaboration failure was a
different problem: The owner really did need the assembled module check,
not a second build by a statement reviewer. See
[assembled endpoint elaboration](../assembled-endpoint-elaboration/).

**Decision:** Keep the same nodes, owner checks, and independent review.
Clarify the landing guide to give reviewers fixed statement text or an
exact revision and leave the build of a moving proof to its owner. A
changed statement still needs independent review. This replay establishes
which evidence transferred, not a live time saving or a proof advance.

**Live follow-up, same improvement session.** For the corrected Hecke
Gaussian, reviewer `GjxnVNh` first checked the manuscript correspondence,
then the three fixed writer source hashes, without building. Those
hashes and the signatures agreed at both the stale owner candidate
`1ee2d1cfbaec17c4b427f5acc549860c2c80fdee` and the adopted restack
`91a1e59ccd12a3b51dbc5e16f8366d31ca552b0d`. The owner reran the build,
import, and axiom checks on the restack; no second statement review was
needed. See the [proof handoff](../../obligations/single-place-norm.md#corrected-archimedean-schwartz-factor-and-pointwise-hecke-theta-inversion).
This exercises the separation on a landing, not a benchmark of it.

## Follow-up: Weighted small-norm Gaussian

Run `01a20546-eaa7-7d18-a842-172deb3eb3a4` matches work session
`01a20546-ebfe-7af6-b8e4-93c438e74314` by input and final response.
Its launch prompt names `68a509c25584718e1aa34b0ba36f1e75b3dc9daa`.
The worker correctly skipped the pointwise estimate already landed by
improvement at `9eaebdf11efdf33b8b510e8550e686cf2bedaf27` and worked on
weighted averaging. Three draft builds failed (notation and instance
elaboration, then rewriting and subtraction), and the fourth passed.
The work reviewer `VDZDFkA` did not build the moving proof. It separated
the additive Fourier Haar prerequisite from multiplicative Haar in the
existing radial package and flagged the inverse-translation prose on
p. 96. The final handoff identifies a checked, independent construction
of the additive measure and declares the translation convention.

Replay in improvement session `01a20550-d5a6-78a3-9def-ba66465b8227`:
Extract the public theorem header from reviewer events 8 and 24, and
compare it with the source at the three candidate IDs. All five headers
match exactly. The owning worker checked `e028767607868f3572792f254362747962d1e5df`
before the review was complete; it was not adopted. After reconciling
the review and concurrent changes, `407a8986a00f849fdae134c00d96856028422cf1`
passed but adoption returned stale. The exact restack
`1939a522d23548256b8700abf1a7cd1f672d7d33` has byte-identical Lean
source to the second candidate and passed the fresh checks including
all eight signatures and axiom reports. Only that restack landed.
The reviewer output `79103afe70ef0912c98d837d24a271d8aac01d9b` was
review evidence, not integrated source. The incidental invalid `new`
call with a description was corrected immediately; no Lake target
typo or reviewer build failure recurred.

**Decision:** The current separation worked on a fixed statement and
surfaced a meaningful instantiation question. Do not add a node, a
second review, or an adoption retry path for this case. This replay
does not establish a speedup. See the [accepted mathematical handoff](../../obligations/single-place-norm.md#weighted-gaussian-decay-at-small-norm).

## Follow-up: Trivial Hecke scalar formula

Run `01a205d5-8540-7f4e-9f8e-9886762a6d04` matches work session
`01a205d5-86e7-72d0-aaa8-0d773ef7e05e` by both input and final response.
The launch marker and initial accepted tip were
`db84a60a6fb6c114c3c27cf8698c8f8794612f96`. The `cmd/godel` tree
and its shared `internal/godel` inputs are unchanged in the proof
landing. The preceding work run `01a205c5-b9ef-791b-b752-3f2a8b1cc16f`
(session `01a205c5-bb89-7e44-9e38-430cdd04116d`) had already exhausted
the trivial Hecke contour with full multiplicities. Its improver
(session `01a205d0-2ca5-73d1-8e5e-8c9c58aafbb4`) added a frontier
pointer for the separate trace obstruction, not the scalar assembly.
The current worker correctly used the existing contour and checked
local terms to close that assembly.

The worker allocated after refreshing to
`dffe6e3491d1d3899b6e4b1ff8b582ad81eabe1c`, which did not change the
Lean inputs. Seven assembled draft builds failed (imports and notation,
parsing, a local notation binder, then integrand and kernel conversions).
The eighth passed. Reviewer `HSQJGyI` read the fixed statements and
dependencies, not the moving proof. A comparison with the adopted
source found that the three reviewed statements and both definition
bodies are unchanged, apart from renaming the conductor notation
and inlining the alias for the finite-place index in four binders.
The review has provisional source status, with targeted raster
corroboration, not complete rendered-page verification. Its read-only
output `2d3ccc410fbd7496d71c95612aa8162444b649e3` had no source delta
and was not integrated.

The checked writer output `e36004d071ea10a8ecccc4a4581b3d92b07fc3be`
replayed onto `cf66b7847d0163851b9dc995d52807f375911b24`. Intervening
Lean additions did not overlap the formula inputs. The first
integrated candidate, `a1789f83871c2448dbffff58de4892f64040fd28`,
passed its exact build, joint import, signature inspection, and all
three axiom reports (work events 136–152), then adopted without a stale
attempt. This is another live control for separating review from
elaboration, not evidence for a speedup or a need to automate retries.

**Decision:** Keep the proof checks, review split, and nodes. The
[rational trace handoff](../../obligations/trace-carving-weight-q.md#next-comparison-and-checks)
now points to the already checked rational radial scalar formula
instead of an obsolete contour-limit task. The next decision is about
a specific shell or local comparison at fixed cutoffs, not another
scalar derivation or a row-sum test on the unsplit kernel.
