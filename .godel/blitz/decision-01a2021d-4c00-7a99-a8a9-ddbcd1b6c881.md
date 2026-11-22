# Blitz decision: Decline classical RH and full Masullo GRH

**Outcome: NOT_ATTEMPTED.** Neither target warrants a bounded blitz now.
No attempt was opened, no proof pass or fresh Lean audit ran, and this
cycle did not direct or modify either proof loop.

**Pinned assessment evidence:** `cd5e0c6c6744873460f27852d1e8a19a43deacc0`.
The pin contains seven prior declines. The latest,
`decision-01a201f7-ab1a-7909-9c44-4e250b02ca97.md`, landed at
`5b0d45e9b9100f6e64c22cda0d4d21eb07b33c57` on assessment evidence
`5e1d71ff8fedf313776314f6d554f8484e238f2e`. The new local arithmetic
and class-group results materially change the GRH evidence, but neither
reopening condition is met. There is no rational trace change in the
pinned diff from the previous assessment. Later independent landings
noted below do not change this cycle's pin.

The pin uses Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Manuscript citations use
one-based PDF pages in the pinned 940-page edition of Alessandro Maria
Masullo's *The Music of the Primes*, SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Rendered readings below are attributed to their reviews. Closure checked
repository references and accepted declarations, not fresh raster or
Lean proof checks.

## Classical RH

The target is Mathlib `RiemannHypothesis` for the Riemann zeta function.
`Masullo.rationalIdeleRadial_explicit_formula`
(`Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:66`) identifies
the absolutely summable full-order zero sum on actual rational quotient
Haar with the two polar Mellin terms at $s=0,1$ minus the real and finite
local terms. This unconditional scalar contour and normalization repair
is not a trace evaluation.
`Masullo.riemannHypothesis_of_strip_test_agreement`
(`Proofs/Props/ZetaTestSumComparison.lean:30,94`) proves RH conditional
on agreement at arbitrarily small positive half-widths. At each width
one family of natural weights bounded by the full orders and supported
in the closed centered strip must give the full-order sum on **every**
smooth, compactly supported positive-log test of integral zero.

RH is closer, but the scalar formula and conditional implication do not
supply the two evaluations of the **same global Haar diagonal** on
common tests, measures, and widths. The independent rendered reviews
in `.godel/obligations/trace-assembly.json` confirm the final algebra
(PDF pp. 519–520, Thm. 12.5.1.1, (12.5.1.1–4)), not the invoked
geometric split, orbital vanishing, normalized $S$-piece with both
Mellin subtractions, or spectral evaluation. The rendered review in
`decision-01a201d4-11f4-7985-b299-2ad2cc1b87bc.md` finds a heading and
insertion marker at PDF p. 514, §12.3. The shell lift, right cutoff,
comparison of the level-first global limit with the joint local limit,
and shared Sobolev admissibility and strip-edge conventions remain
provisional (PDF pp. 488–496, §§11.2.1–11.3.2; pp. 517–519,
(12.4.1.8–12), (12.4.1.23–28); p. 454, (10.3.2.4); p. 463,
Thm. 10.4.2.8; p. 473, Def. 10.4.3.7). The cycle reader's limited
raster check distinguishes the printed left cutoff in (11.2.1.4,9)
from the repaired fixed-position limit, which retains the terminal
right projection (`.godel/obligations/trace-hardy-diagonal-q.md:234–257`).
It does not verify the comparison.

The derivative of a nonzero nonnegative smooth bump in $(0,\log 2)$
has zero mass and vanishing finite prime samples, but a nonzero
$+1/2$ Mellin moment that the joint local replacement omits
(`.godel/obligations/trace-to-zeros.md:84–134` and
`trace-joint-local-q.md`). The companion's real-prime normalization
check (`.godel/obligations/trace-real-prime-q.md:136–252`, inherited
rendered review of PDF pp. 518–519, (12.4.1.24–25), and pp. 619–620,
(B.4.3.13), (B.4.4.1–2)) also concerns a local term, not the global
operator. Repeating either diagnostic cannot test the missing bridge.

**Reopen RH** when the actual rational global $S$-piece and right
orbital cutoff are specified with the terminal right projection intact
and a demonstrably common admissible positive half-width is identified.
Then compare both Mellin subtractions and the actual orbital contribution
against the strip evaluation on the short bump derivative, taking the
level limit at fixed position support before exhausting position.

## Full Masullo GRH

The target is location on $\Re s=1/2$ of every nontrivial Hecke zero
for every number field and every continuous unitary idele-class
character. The rendered scope review in
`decision-01a20149-6c55-768f-9fd2-b751564c1bca.md` cites PDF p. 6,
Acknowledgements, and p. 528, §14.1.2. The multiplicity bound and
broader automorphic conjecture are separate (PDF pp. 528–529,
§14.1.2 and Conj. 14.1.2.1). Neither conditional GRH nor a rational or
single-isotype specialization discharges the target.

At the pin, `Masullo.ideleHeckeGaussian_zetaIntegral`
(`Proofs/Theorems/IdeleHeckeGaussian.lean:104,177`) evaluates the raw
upstairs integral of the corrected Gaussian on $\Re s>1$ with actual
finite unit masses, subject to exact stage comaps and unit mass one
and unramifiedness outside the exceptional set. It does not identify
a normalized quotient trace. The aggregate different scale
(`Proofs/Theorems/DifferentUnitScales.lean:23,31,51`) is not a placewise
Haar calibration. The new arithmetic declarations, inspected at their
landings, give compatible p-adic base maps and finite dimension
(`51a5c4aa5a77bd43a58c32b658de1881a60cc61a`), a finite free integral
lattice and localization (`2ccc9dba544d6af4ae523367eb6e6f87601376c6`),
prime-power quotients (`1dd33472117fa8dce69001e5a65044a66e4fcc53`),
and canonical completed CRT reductions including modulo $p$
(`082b56977d1fd143b3bb67b1810eb55c2e7f072b`). They do not identify the
trace-dual lattice or self-dual local Haar masses. The primitive
$\mathbb Q_p$ conductor shells (`Proofs/Theorems/PadicConductorFourier.lean:142,179,193`)
do not give general-character conductor reflection. General meromorphic
completion, reflection, divisor and pole data, contour exhaustion, and
a normalized common trace-to-divisor comparison remain missing.
Calibration and general contour assembly readings remain provisional
(PDF pp. 124–127, Thm. 3.2.2.1; pp. 135–141, §3.3; pp. 558–560,
(A.3.1.8), (A.3.2.1–5); pp. 614–615, (B.4.2.1–4)). The independent
rendered reviews in `.godel/obligations/divisor-heading.json` found
only a heading, unresolved reference, and insertion notes at Thm.
13.3.1.2 (PDF pp. 522–523). The preceding capped critical-line formula
(PDF p. 522, Thm. 13.3.1.1, (13.3.1.1–5)) does not supply the missing
positive-width comparison.

The pin itself adds discriminant $-20$ and the norm-one-or-two
representative bound over $\mathbb Q(\sqrt{-5})$
(`Proofs/Theorems/IdealClassSmallRepresentative.lean:22,56`), not the
all-prime Euler factor identity for that isotype. Closing reconciliation
verified two later, out-of-pin landings: Integral base change at
`880fe15e856270259ea8a0168bc6aecfc612e28a`
(`Proofs/Lemmas/FiniteCompletionIntegralBaseChange.lean:227,232`), and
the quadratic two-class dichotomy and odd degree-one sign theorem at
`e48a1fb6d22863ed05409c89fd885719209d9119`
(`Proofs/Theorems/IdealClassTwoClasses.lean:22,37`). Trace compatibility
for local calibration is the manuscript loop's stated successor to
base change. The two-class theorem advances the companion's isotype
repair but is neither its all-prime factorization nor general GRH.
Neither branch supplies the missing comparison, and extending either
would not constitute a distinct full-GRH attempt.

**Reopen full GRH** when a general-character completed-contour
interface and an explicit normalized common trace or divisor identity
allow comparison of full-order and strip-supported residue weights
on one admissible ramified-isotype test at one positive width, tracking
the central and identity terms separately.

For either target, confirm that the diagnostic is not already assigned
to a proof loop. Agreement on one test would justify continuation, not
prove the target.
