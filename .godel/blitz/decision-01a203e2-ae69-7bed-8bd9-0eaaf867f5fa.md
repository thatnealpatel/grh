# Blitz decision: Decline classical RH and full Masullo GRH

**Outcome: NOT_ATTEMPTED.** Neither comparison has the inputs for a
bounded test, and the visible loop records do not establish that the
exact comparisons are unowned. Neither target was attempted, proved,
or refuted. No proof pass, fresh Lean audit, or new rendered manuscript
review ran in this cycle, and neither loop was changed.

**Pinned evidence:** `4c2a98cb4ed6424dd0cff759d9bf42bd219ffad2`.
Campaign status established this pin independently of the launch
archive, which happens to have the same ID. The pin uses Lean 4.36.0
and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Citations are to
one-based PDF pages of the pinned 940-page *The Music of the Primes*;
the local copy matches SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Rendered findings and proof audits below are inherited and attributed.

The pin contains 18 prior `NOT_ATTEMPTED` decisions. The latest,
`decision-01a2037f-43f4-72dd-ba61-1695d86e252e.md`, landed at
`ae87362a34a34db3ad1505c66d3ec10700992ccb`, assessed
`3aabb7895701fa7c4edc59802f1b8bdee7539051`, and was subsequently reused.
It predates the audited uniform Gaussian bound and good-height disk
bound below. Those landings close material prerequisites, but neither
comparison.

## Classical RH for the Riemann zeta function

The strongest unconditional input is the project repair
`Masullo.rationalIdeleRadial_explicit_formula`, landed at
`9330ec2f38fe508354301080f8110dc70989458a`
(`Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:34–75`;
historical replay in `.godel/obligations/rational-explicit-formula.md:1374–1428`).
On actual rational quotient Haar, for a smooth compact log profile
in the trivial compact isotype, the absolutely summable full-order
open-strip zeta zero sum is the two polar Mellin moments at $0$ and
$1$, minus the normalized real and finite local terms. This is a
scalar formula, not an operator trace. Alignment with PDF p. 623
(B.4.4.16) is provisional.

`Masullo.riemannHypothesis_of_strip_test_agreement`
(`Proofs/Props/ZetaTestSumComparison.lean:30–39,77–109`) is conditional.
It needs agreement at arbitrarily small positive half-widths, with
one family of weights per width, dominated by full zero orders and
supported on the closed centered strip. Each family must work for
**every** smooth, compactly supported positive-log test of integral
zero. Agreement on all such tests at a single width gives a strip
bound, not RH. Rational jet and theta-density repairs are spectral
input, not the common geometry.

The inherited rendered review in `.godel/obligations/trace-assembly.json`
verifies the final algebra at PDF pp. 519–520, Thm. 12.5.1.1, not the
two evaluations of one diagonal. The inherited rendered findings
in `decision-01a20240-39f6-7778-8369-892e00fbbf16.md:42–60` record an
insertion marker at PDF p. 514 §12.3 and no terminal right projection
in the printed limits at PDF pp. 488–489 (11.2.1.4), (11.2.1.9).
The project repair retains that projection
(`.godel/obligations/trace-hardy-diagonal-q.md:234–257`). There is not
yet even one common admissible positive width with the actual global
$S$-piece, shell lift, projected right orbital cutoff, and tail at
compatible cutoffs. The operator readings at PDF pp. 494–496
(11.3.1.4), (11.3.2.3), and pp. 517–519 (12.4.1.8–12), (12.4.1.23–28)
remain provisional. The level-first global limit is distinct from the
joint local limit.

**Reopen RH** after confirming nonduplication and exhibiting one common
admissible positive half-width with the global $S$-piece, shell lift,
and actual right orbital cutoff identified at fixed cutoffs, retaining
the terminal right projection. For a nonzero nonnegative smooth bump
$b$ supported in $(0,\log 2)$, test $F=b'$, taking the level limit before
position exhaustion. Mass and prime samples vanish, but the $+1/2$
Mellin moment is $-\tfrac12\int e^{x/2}b(x)\,dx\ne0$. Evaluate the
actual orbital contribution rather than inferring that it vanishes.
The diagnostic in `.godel/obligations/trace-to-zeros.md:84–134` was not run.

## Full Masullo GRH

The target places every nontrivial Hecke zero on $\Re s=1/2$ for every
continuous unitary idele-class character over every number field,
including ramified characters. The rendered scope reading of PDF p. 6,
Acknowledgements, and p. 528 §14.1.2 is inherited from
`decision-01a202cd-7acf-7edb-97ce-044d9614d43e.md:78–87`. The inherited
two-reader rendered review in `.godel/obligations/divisor-heading.json`
finds a missing reference and insertion notes at PDF pp. 522–523,
Thm. 13.3.1.2, not a divisor theorem. The preceding Thm. 13.3.1.1 has
a critical-line cap and Mellin-jet restrictions, not full-order equality.

- The counting-normalized Borel Gaussian periodization identifies the
  discriminant-scaled completed Euler product only for $\Re s>1$
  (`Proofs/Theorems/IdeleClassGaussianRadial.lean:89–119,178–188`). At
  `c18f5d2f78a8d8df37b6c69129c8c021dcd10fca`, the accepted
  `ideleHeckeGaussian_periodization_rapidDecay` proves uniform absolute
  orbit-sum decay $O_N(t^{-N})$ at every $t\ge1$ for the corrected Gaussian
  (`Proofs/Theorems/IdeleClassGaussianRapidDecay.lean:48–56`), using the
  scalar dilation and fixed support lattice. The exact-candidate audit
  and inherited rendered distinction between this repair and the printed
  claims at PDF pp. 83–84, Thm. 2.2.3.4(1), and p. 547, Lemma A.2.2.4,
  are recorded in `.godel/obligations/single-place-norm.md:910–978`.
  Pointwise norm-one slice integrability and small-norm inversion with
  both zero modes remain separate. For a nontrivial norm-one restriction,
  cancellation is after averaging, not pointwise; for a trivial
  restriction, the two Mellin contributions must be kept. Alignment of
  continuation to PDF pp. 97–98, Thm. 2.2.5.4(2), (4), and pp. 126–127,
  Thm. 3.2.2.1, remains provisional.
- Companion's `Proofs/Theorems/IdealClassEulerFactorization.lean:19–44`
  identifies the finite Euler product of one everywhere finite-unramified
  class character of $\mathbb Q(\sqrt{-5})$ with an entire Dirichlet
  product on $\Re s>1$. At `edca34eca146e3f6340c7a7f05d8cf5a0a4308b3`,
  the accepted `qSqrtNegFiveDirichletProduct_good_height_disks` gives a
  single height per unit interval, closed-disk nonvanishing around the
  whole horizontal segment, and a polynomial reciprocal bound for that
  explicit product (`Proofs/Theorems/IdealClassGoodHeightDisks.lean:43–51`).
  The exact-candidate audit is recorded in
  `.godel/obligations/isotypic-good-heights-q-sqrt-minus-five.md:185–243`.
  The disk result does not itself give higher reciprocal derivatives,
  a completed ramified contour, or a diagonal comparison.

For even one named admissible ramified test, the completed contour needs
continuation, conductor reflection, poles, full-order residues, and
horizontal exhaustion. `Proofs/Props/HeckeContourReflection.lean:28–32,55–70`
assumes the functional-equation germ, or the reflected derivative and
right-line integrability. The contour alignment at PDF pp. 135–141 §3.3
and pp. 614–615 (B.4.2.1–4) remains provisional. The reviewed width-zero
angular models and raw-Haar pole obstruction do not establish a
normalized common positive-width diagonal for the same test.

**Reopen full GRH** after confirming nonduplication and supplying both a
completed contour and a normalized common positive-width diagonal for
the same named admissible ramified test. Then compare the full-order and
strip-supported sums, keeping central and identity terms separate.
Neither a rational specialization nor conditional GRH discharges the
target.

## Overlap and stopping condition

The assessment's visible Main and Companion runs
`01a203dd-15d7-7de3-956f-7268ee372ca0` and
`01a203dd-15ff-7e2d-a7f2-31d9c546fdb1` had live driver children and no
saved invocation result at inspection. Their inputs name nonnegative-radius
Gaussian slice integrability and same-height reciprocal Cauchy estimates,
respectively. Those are adjacent scopes, not confirmation of ownership
or nonduplication of either exact comparison. The two earlier runs
`01a2035d-84a2-7672-ad19-6a30dccb32c6` and
`01a2034d-7dcf-75b6-ad7b-e3095762018d` still had running records with
blank output, but recovery session `01a203d3-a354-7089-ae50-bcb5f1d71d4d`,
journal seq 66, attributed both interruptions to ENOSPC. The two accepted
prerequisites above were audited and adopted in recovery, not established
by those interrupted invocations.

Closure separately observed post-pin acceptance of
`aecf6de8fc2ef566569bceaf15e175d62a320fba` and checked its exact statement
in `Proofs/Theorems/IdealClassGoodHeightDerivatives.lean:20–25`. It gives
all-order reciprocal bounds at the same good heights for the same
explicit finite product. It does not supply the reflected identity,
vertical bounds, a ramified contour, or a common diagonal, and does not
change the assessment pin.

Neither target warranted a blitz at that pin. For either diagnostic, a
mismatch rejects the comparison, not the hypothesis, and one match
warrants broader testing, not a proof claim.
