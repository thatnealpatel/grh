# Blitz decision: Decline classical RH and full Masullo GRH

**Outcome: NOT_ATTEMPTED.** Neither target warrants a bounded blitz now.
No proof pass, fresh Lean audit, or intervention in either proof loop
occurred. Neither diagnostic has its required inputs, and neither is
confirmed to be unassigned.

**Pinned assessment evidence:** `8fa08a83fc7120f12fba0263b06ee73f44c4a812`.
All ten earlier decision notes at this pin are declines, not attempts.
The previous decision, `decision-01a20262-e00c-791a-adac-0b795fe38683.md`,
landed at `8d7000251a06cce16dca70e4caf6786852256790` on evidence
`04f0e94dc20349a4dc844436cf07e8f2823a7c2f`. The new Haar, Gaussian,
and norm-section landings materially change the GRH assessment, so the
previous note is not reused. The rational proof modules are unchanged.

The pin uses Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Citations are one-based PDF
pages of Alessandro Maria Masullo's *The Music of the Primes*, the
pinned 940-page edition with SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Closure checked the digest, the Lean statements, and the cited Lean
landings at their exact revisions. Rendered readings below are
attributed to their existing review records, not to this closure.
Unverified manuscript interfaces are identified as provisional.

## Classical RH

The target is Mathlib `RiemannHypothesis` for the Riemann zeta function.
`Masullo.rationalIdeleRadial_explicit_formula`
(`Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:66–75`) gives
an unconditional, absolutely summable full-order zero sum on normalized
rational idele-class Haar: The two polar Mellin moments at $s=0,1$ minus
the real and finite local terms. This is a scalar repair, not a Chapter
12 operator trace. Its correspondence to PDF p. 614, (B.4.2.2), and
p. 623, (B.4.4.16), is provisional.

`Masullo.riemannHypothesis_of_strip_test_agreement`
(`Proofs/Props/ZetaTestSumComparison.lean:30–39,77–109`) implies actual
RH only if, at arbitrarily small positive half-widths, there is one
family of natural weights per width, bounded by full orders and zero
outside the closed centered strip, whose sum agrees with the full sum
on **every** smooth, compactly supported positive-log test of integral
zero. Agreement at one width gives only a location bound. The separate
capped-order implication does not supply this premise.

The rendered review in `.godel/obligations/trace-assembly.json` verifies
the algebra of combining two evaluations of one Haar diagonal (PDF
pp. 519–520, Thm. 12.5.1.1, (12.5.1.1–4)), not the analytic evaluations
or common test class. `decision-01a20240-39f6-7778-8369-892e00fbbf16.md`
attributes direct rendered inspection of the insertion marker (PDF
p. 514, §12.3) and the missing terminal right projection in the claimed
limits (PDF pp. 488–489, (11.2.1.4), (11.2.1.9)). The fixed-position
repair retains that projection (`.godel/obligations/trace-hardy-diagonal-q.md:234–257`),
but does not identify the actual global $S$-piece, shell lift, or right
orbital cutoff. The geometric dependencies are provisional (PDF
pp. 494–496, (11.3.1.4), (11.3.2.3); pp. 517–519, (12.4.1.8–12),
(12.4.1.23–28)). Common Sobolev and edge admissibility is unproved;
the dependency reading is provisional (PDF p. 454, (10.3.2.3–4),
p. 463, Thm. 10.4.2.8, and p. 473, Def. 10.4.3.7).

The short-bump test already separates the joint local substitute from
the required two-pole evaluation (`.godel/obligations/trace-to-zeros.md:84–134`).
The derivative of a nonzero nonnegative smooth bump in $(0,\log 2)$
has zero mass and vanishing prime samples but a nonzero $+1/2$ Mellin
moment. The joint local projection supplies only the $-1/2$ subtraction.
Vanishing prime samples does not establish orbital vanishing. The joint
local limit cannot substitute for the level-first global comparison.

**Reopen RH** once the actual rational global $S$-piece and right
orbital cutoff are identified with the terminal right projection intact,
and one common admissible half-width $0<\alpha<1/2$ is established. Then
compare the actual orbital contribution and both Mellin subtractions
against the strip evaluation on that bump derivative, taking the level
limit at fixed position support before exhausting position.

## Full Masullo GRH

The target is location on $\Re s=1/2$ of every nontrivial Hecke zero for
every number field and every continuous unitary idele-class character.
The rendered scope review is attributed in
`decision-01a20149-6c55-768f-9fd2-b751564c1bca.md:73–86` (PDF p. 6,
Acknowledgements, and p. 528, §14.1.2). The noncentral multiplicity
claim and broader automorphic conjecture are separate (PDF pp. 528–529,
§14.1.2, Conj. 14.1.2.1). Neither rational specialization nor a
conditional result discharges the target.

The Lean advances at the pin are substantive but separate:

- `89b5f3ecde2f4a9c88eda26d36959f71f1a54eaa`,
  `Proofs/Theorems/FiniteCompletionDifferentExtension.lean:59–85`,
  extends the global different to the finite completion and identifies
  its exponent and discriminant scale.
- `002582a9c417a34219ff7c000b722972067b021f`,
  `Proofs/Theorems/DiscriminantNormalizedIdeleHaar.lean:39–52`,
  constructs regular Haar on actual ideles with prescribed product
  comaps on stages containing the different support and finite-unit
  calibration factor $|\operatorname{disc} K|^{-1/2}$. This is upstairs
  calibration, not the norm-one quotient volume (PDF pp. 559–560,
  (A.3.2.1)). The combined normalization reading remains provisional
  (PDF pp. 556, 558, 560, (A.3.1.2), (A.3.1.8), (A.3.2.2), (A.3.2.5)),
  apart from the previously attributed rendered square-root prescription.
- `9686ddf56f31de989478bca96b0898d52a9314bc`,
  `Proofs/Theorems/FiniteHeckeRamification.lean:25–27` and
  `Proofs/Theorems/DiscriminantNormalizedIdeleHeckeGaussian.lean:37–54`,
  establish finite ramification and an absolutely integrable corrected
  raw Gaussian pairing for every unitary character on $\Re s>1$. Its
  value is the completed **Euler product** times
  $|\operatorname{disc} K|^{-1/2}$, not a continued completion or an
  eigendistribution. The opposite complex angular weight is a repair
  (rendered comparison attributed in `.godel/obligations/complex-gaussian-angular.md`;
  PDF pp. 124, 130, 151–153, (3.2.2.1), (3.3.1.7), (3.4.3.1),
  (3.4.3.5), (3.4.3.11)). The combined pairing and normalization
  interface is provisional (PDF pp. 122–123, (3.2.1.1–5), p. 152,
  (3.4.3.8), and p. 636, §B.6.1.2).
- `8fa08a83fc7120f12fba0263b06ee73f44c4a812`,
  `Proofs/Theorems/IdeleLogSection.lean:35–86`, gives a continuous
  homomorphic norm section on ideles and classes at any infinite place.
  It inserts $\exp(x)$ at a real place or $\exp(x/2)$ at a complex place
  to give norm $\exp(x)$. The manuscript's root and apparent
  intermediate no-root expression remain provisional (PDF p. 542,
  (A.1.3.6), and p. 547, (A.2.2.10), (A.2.2.12));
  `.godel/obligations/single-place-norm.md` records statement review, not
  rendered inspection. The section is not a topological product
  equivalence, compactness, or quotient Haar calibration.

A general-character completed contour remains missing. The conditional
reflection lemmas (`Proofs/Props/HeckeContourReflection.lean:28–32,55–70`)
assume a functional-equation germ or reflected log derivative, and
right-line integrability for the reflected integral. They do not
supply continuation, conductor and reflection data, divisor and pole
data, or controlled contour exhaustion. The dependency reading remains
provisional (PDF pp. 124–127, Thm. 3.2.2.1; pp. 135–141, §3.3;
pp. 614–615, (B.4.2.1–4)). A normalized common global trace diagonal is
also missing. The inherited rendered review in
`.godel/obligations/divisor-heading.json` found only a heading, an
unresolved reference, and an insertion note, not a divisor theorem
(PDF pp. 522–523, Thm. 13.3.1.2). The preceding capped critical-line
trace (PDF p. 522, Thm. 13.3.1.1, (13.3.1.1–5)) does not give the
full divisor or the required positive-width comparison.

**Reopen full GRH** once a general-character completed contour and a
normalized common global diagonal permit comparing full-order and
strip-supported residues on one admissible ramified-isotype test at
one positive width. Track central and identity terms separately.

## Loop overlap and stopping condition

Manuscript runs `01a20254-2af3-7397-8f2c-014dc4c22bca`,
`01a20265-375e-7f27-b09b-8093775cf6e0`, and
`01a20275-aefa-720f-99b0-f8f425d92cd1` report exact-candidate builds,
module replays, signature checks, and the ordinary three axioms for the
recent landings. These checks were not replayed here. The recorded
successor is product splitting toward quotient calibration, not the
positive-width comparison. Companion work at the pin analyzes circle
compression and a singleton angular operator in one Gaussian-field
isotype, not the common trace. The later `aceedd47ecbce262ef762eb415ee425b35c47399`
records an ordinary-mathematics Gaussian theta-closure inclusion at
singleton width in that isotype. It is outside the evidence pin, not
Lean, and not a positive-width or trace-class result. The recorded
successor concerns finite-rank row summability.

These records establish overlap on prerequisites, not the current
assignments for the exact diagnostics. Confirm that the selected
diagnostic is unassigned before reopening either route. A mismatch on
one test rejects the proposed comparison; a match warrants broader
testing, not a claim of either hypothesis.
