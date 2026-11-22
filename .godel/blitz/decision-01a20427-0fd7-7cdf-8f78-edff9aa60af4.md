# Blitz decision: Decline classical RH and full Masullo GRH

**Outcome: NOT_ATTEMPTED.** Neither target warranted a bounded proof
attempt at the pin. No Blitz proof pass, fresh Lean audit, or new rendered
manuscript review ran. Neither target was proved or refuted, and neither
loop was changed. The subsequent Main report described below is not a
Blitz pass and does not change the pinned assessment.

**Pinned evidence:** `a321c270d8f177befc0f7649226a4ec12888bf15`,
confirmed by campaign status independently of the executable archive.
Lean is 4.36.0 and Mathlib is pinned to
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Citations use one-based PDF
ordinals of the 940-page edition of *The Music of the Primes*. The local
PDF matches the source pin, SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Rendered readings below are attributed to their prior reviews.

The prior decline assessed `aed8be78f9bd777e345cd464520c0ed4265c48e8`
and landed alone at `2de4140b90002a30952ba4b4b00c43d86b78c1bf` as
`decision-01a20405-340c-7b02-bed4-d6bc3835cf24.md`. Four subsequent
commits expose the fixed-annulus trace in the standard Lean library,
compute the local integer-ring Fourier transform, discharge right-line
integrability for Dirichlet reflection, and bound the left-edge
quadratic class denominator. These are material additions to the
assessment, but none supplies a common global diagonal or records an
outcome for either of the assigned diagnostics at the pin.

## Classical RH for the Riemann zeta function

`Masullo.rationalIdeleRadial_explicit_formula`, landed at
`9330ec2f38fe508354301080f8110dc70989458a`
(`Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:34–75`),
unconditionally evaluates the absolutely summable full-order open-strip
zeta zero sum on normalized rational quotient Haar: It is the two polar
Mellin moments at $0$ and $1$ minus the normalized real and finite terms.
This is a scalar project repair, not an operator trace. Its alignment
with PDF p. 623, (B.4.4.16), is provisional.

At `74567ea7b15369d4cd476f21f12b99a5c35fff0e`,
`Proofs/Theorems/RationalFixedAnnulusTrace.lean:21–41` and
`Proofs/Props/HilbertRankOneTrace.lean` expose in the standard library
a norm-summable rank-one presentation and an absolutely convergent
basis-independent trace for the actual local $M_p A_\phi Q_Y$ on every
weighted Hilbert-space input, retaining the right projection. The
predecessor eight-module check in the preceding decision is not a fresh
audit of this pin. The fixed-annulus result does not cover the informal
smooth-space lift, the one-sided cutoff, global levels, orbital terms,
or joint cutoff limits.

The inherited rendered review in `.godel/obligations/trace-assembly.json`
verifies the final algebra at PDF pp. 519–520, Thm. 12.5.1.1,
(12.5.1.1–4), not its two evaluations on a common domain. The rendered
review attributed in `decision-01a20240-39f6-7778-8369-892e00fbbf16.md`
identifies an insertion marker at PDF p. 514, §12.3, and an omitted
terminal right projection in the printed limits at PDF pp. 488–489,
(11.2.1.4), (11.2.1.9). Exact shell and local-limit alignments at PDF
pp. 492–496, (11.3.1.2), (11.3.1.4), (11.3.2.2–4), and pp. 517–519,
(12.4.1.8–12), (12.4.1.23–28), remain provisional. The same-chain
cutoff erases a fixed shell on the literal reading. Rebasing is a
repair and does not determine the shell trace. The actual global
$S=\{\infty\}$ piece, shell lift, projected orbital cutoff and tail,
compatible limit order, and one common admissible positive half-width
are not identified by these results.

`Masullo.riemannHypothesis_of_strip_test_agreement`
(`Proofs/Props/ZetaTestSumComparison.lean:30–39,77–109`) is conditional
on agreement at arbitrarily small positive half-widths. Each width
requires one family dominated by actual zero orders and zero outside
the closed centered strip, agreeing with the full sum on every smooth,
compactly supported positive-log test of integral zero. One width with
all such tests only bounds the strip. The separate capped-multiplicity
comparison also assumes equality.

**Reopen RH** only after Main reports and a distinct, unassigned
follow-up becomes runnable. A concrete trigger is a source-compatible
Haar lift and identification of the global $S$-piece and the shells
with their actual projected orbital cutoff on compatible spaces at a
common admissible $0<\alpha<1/2$ and even degree $s\ge4$. The unrun
control is $f=b'$ for a nonzero nonnegative smooth bump $b$ compactly
supported in $(0,\log 2)$. Take the global level limit before position
exhaustion and compute the actual orbital term separately. The mass
and prime samples vanish, but the $+1/2$ Mellin moment is
$-\tfrac12\int e^{x/2}b(x)\,dx\ne0$. Do not infer orbital vanishing
from the prime samples or from failure of a proposed shell lift.

## Full Masullo GRH

The target places every nontrivial Hecke zero on $\Re s=1/2$ for every
continuous unitary idele-class character over every number field,
including ramified characters. The scope is attributed to the rendered
review in `decision-01a202cd-7acf-7edb-97ce-044d9614d43e.md:78–87` of
PDF p. 6, Acknowledgements, and p. 528, §14.1.2. It includes nontrivial
central zeros and is distinct from the multiplicity assertion and
broader automorphic Conj. 14.1.2.1. The inherited two-reader rendered
review in `.godel/obligations/divisor-heading.json` finds an unresolved
reference and insertion notes, not a statement of Thm. 13.3.1.2, at
PDF pp. 522–523. Thm. 13.3.1.1, (13.3.1.1–5), is a restricted capped
critical-line sum, not full-order equality.

- The Gaussian slice theorem at `0abc265a52c15782f83bab34e30fc0ec14b8b70a`
  gives integrability at each nonnegative log radius with exact
  quotient mass. Its discriminant-scaled completed Euler-product
  identity is only for $\Re s>1$
  (`Proofs/Theorems/IdeleClassGaussianRadial.lean:96–105,150–180`).
  `9bfb408ef0c7e5e6b934bb902be34e75f4bf1e3e` computes the local
  integral-ball Fourier transform with inverse-different support and
  explicit additive Haar mass (`FiniteCompletionIntegersFourier.lean:29–36`
  in the same directory). It supplies neither self-dual Haar
  normalization nor global Poisson inversion. Small-norm inversion
  must retain both zero modes and cancel them for nontrivial norm-one
  restriction only after averaging. Source alignments at PDF p. 82,
  (2.2.3.2), pp. 97–98, Thm. 2.2.5.4, and pp. 126–127, Thm. 3.2.2.1,
  remain provisional.
- `69346197c3e5d25083870afb061aad997bd8f6cd` gives tested vertical
  reflection for primitive Dirichlet characters for $a>1$, with
  both lines integrable and the log-conductor contact term
  (`Proofs/Theorems/DirichletContourReflection.lean:24–29,46–70`).
  This supplies neither the idelic identification nor full-order
  residues or horizontal exhaustion. A named ramified control is the
  odd quadratic character of conductor 3; `PadicRamifiedThreeFourier.lean`
  supplies local input, and the inherited rendered review in
  `.godel/obligations/global-mellin-sign-q.md` distinguishes the sign
  defect at PDF p. 124, (3.2.2.2), from the repaired pairing. General
  contour alignment at PDF pp. 135–141, §3.3, and pp. 614–615,
  (B.4.2.1–4), remains provisional.
- `aecf6de8fc2ef566569bceaf15e175d62a320fba` bounds reciprocal
  derivatives of every order at one common good height across the
  closed horizontal segment for one finite-unramified class character
  of $\mathbb Q(\sqrt{-5})$. The tip gives exact left-line norm
  reflection and reciprocal $O((t^2+1/4)^{-1})$ uniformly in height
  (`Proofs/Theorems/NegFiveDirichletReflection.lean:12–16` and
  `NegFiveDirichletReciprocal.lean:12–15`). These are denominator
  results, not numerator decay, a ramified contour, or a diagonal.
  `.godel/obligations/isotypic-good-heights-q-sqrt-minus-five.md`
  attributes the denominator repair to a rendered reading of PDF
  pp. 308–309, (6.3.2.16–17). Reading the source test space for
  endpoint control at PDF pp. 800–801, Def. D.3.1.3, remains provisional.

**Reopen full GRH** after confirming nonduplication and identifying a
completed contour and a normalized positive-width diagonal for the same
admissible ramified control, such as the odd character of conductor 3.
The contour must identify the idelic completion and justify full-order
residues and horizontal exhaustion. Compare full-order and
strip-supported sums, with conductor terms, identity terms, poles,
and central zeros handled separately. Neither a rational specialization
nor conditional GRH meets the target.

## Ownership and closure

At the pin, `.godel/frontier.md:5–11` (assignment origin
`b0a4e3ad7c8219e6c54d479f27b3848c32d9ef28`) gave Main the exact rational
diagnostic and Companion the adjacent closed-segment numerator audit,
parking Gaussian inversion. Saved Main run
`01a20423-6d7b-705d-b859-7f9b8d6bcdfb` and Companion run
`01a20423-6d30-791d-a501-97378830f5d2` took those assignments. At
observation their records were running, with zero saved invocations
and no final or improvement response. Neither report was in the pin.
This was direct overlap for RH and adjacent work for full GRH, not
confirmation of nonduplication of the exact ramified comparison.

**Post-pin evidence, not a new assessment:** The accepted target moved
to `1f13433251809d04c28918a7c21a53fa3078406f` before note allocation.
That exact commit is documentation only and records Main's report in
`.godel/obligations/trace-orbital-q.md:269–379`. This expires Main's
one-cycle assignment. On the provisional extraction reading of PDF
p. 495, (11.3.2.2), the literal lift from the quotient kernel on
$C_{\mathbb Q}^2$ to an idele kernel has zero Haar row mass rather than
the normalization needed to recover the quotient action. The
same-chain right cutoff in (11.3.2.3) independently erases the fixed
shell. The note attributes independent review of the deductions to
Yah session `01a20423-6e7a-7d64-a52b-fd38fb5c5973`, child `source-review`
(`eorRcBP`), with no rendered-page or Lean check. The short bump was
not run on a substitute. Main's report satisfies the report condition,
not the distinct runnable follow-up condition: A Haar-compatible lift
and shell-preserving cutoff on common levels are still missing.

At `61da655e889bc45bab4a530dd7f8d6e19b65f09b`, Companion's
one-cycle audit also finished. The accepted report in
`.godel/obligations/isotypic-good-heights-q-sqrt-minus-five.md:290–392`
derives rapid decay for all numerator derivatives, uniformly across
$[-1/2,2]+iT$ including both endpoint centers, at all real ordinates
$T$. It uses fixed-radius Cauchy estimates and the full-plane strip
bounds of the stated converse input, not the sampled-line topology.
The report attributes independent rendered checks of PDF p. 304,
Thm. 6.3.2.1(1), p. 308, §6.3.2, and pp. 799–801, Lemma D.3.1.2
and Def. D.3.1.3, to the worker and reviewer `zVHwESB` in Yah session
`01a20424-a50e-7585-9e51-357702c52d6b`. This is reviewed ordinary
mathematics for the corrected, finite-unramified quotient over
$\mathbb Q(\sqrt{-5})$, not a new Lean result. The Leibniz successor
remains parked. This advance does not supply the ramified contour or
diagonal, or establish nonduplication of that comparison.

The cycle closes without a proof pass as assessed at the original pin.
For either target, a mismatch rejects the proposed comparison, not the
hypothesis. A single match warrants broader testing, not a proof claim.
