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
