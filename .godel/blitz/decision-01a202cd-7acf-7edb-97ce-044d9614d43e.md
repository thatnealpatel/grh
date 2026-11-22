# Blitz decision: Decline classical RH and full Masullo GRH

**Outcome: NOT_ATTEMPTED.** Neither target warrants a bounded blitz now.
Neither comparison is runnable on the pinned evidence or confirmed to be
unassigned. No proof pass, fresh Lean audit, or intervention in either
proof loop occurred.

**Pinned assessment evidence:** `4ff17b4d1ffbfe4aac5532afb6fe56752987df8f`.
The prior decline, `decision-01a202a8-e499-748d-8aa3-83e8efa39adb.md`,
landed alone at `c90f70a88582acdab307e754307454db599ffdf6` on evidence
`2c9b7906b3d85c3a2dd116ccf80d302984346b5e`. All 12 earlier accepted blitz
decisions were declines. This decision records materially new GRH
prerequisites at the new pin, not a change in the rational comparison
or a repeat of the prior inventory.

The pin uses Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Manuscript locators are
one-based PDF ordinals of the pinned 940-page *The Music of the Primes*
(SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`).
Rendered readings below are attributed to the evidence readers. Closure
checked the accepted artifacts, not the kernel audits or rendered pages
anew.

## Classical RH for the Riemann zeta function

The accepted Lean theorem `Masullo.rationalIdeleRadial_explicit_formula`
(`Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:34–49,66–75`,
original landing `9330ec2f38fe508354301080f8110dc70989458a`; review and
audit record in `.godel/obligations/rational-explicit-formula.md:1374–1428`)
is unconditional. For smooth compact log profiles it gives the absolutely
summable zeta zero sum with full analytic orders as the polar Mellin
moments at $s=0,1$ minus the real and finite local terms, on normalized
rational idele-class Haar. It is a scalar project result, not an
operator trace. Manuscript correspondence remains provisional (PDF
p. 614, (B.4.2.2); p. 623, (B.4.4.16); p. 625, (B.4.4.20)).

`Masullo.riemannHypothesis_of_strip_test_agreement`
(`Proofs/Props/ZetaTestSumComparison.lean:30–39,77–109`) is conditional.
At each of arbitrarily small positive half-widths, one family of natural
weights bounded by the actual orders and vanishing outside the closed
centered strip must reproduce the full sums on **every** smooth,
compactly supported positive-log test of integral zero. Agreement for
the entire class at one width would give a strip bound, not RH. The
rational jet/theta model's spectral admissibility does not supply a
width common with the geometry.

The inherited two-reader rendered review in
`.godel/obligations/trace-assembly.json` verifies the algebra of
combining two evaluations of the same Haar diagonal and transposing
both Mellin terms (PDF pp. 519–520, Thm. 12.5.1.1, (12.5.1.1–4)), not
the analytic evaluations or their common domain. The rendered review
attributed in `decision-01a20240-39f6-7778-8369-892e00fbbf16.md:42–60`
finds an insertion marker (PDF p. 514, §12.3) and a missing terminal
right projection in the printed limits (PDF pp. 488–489, (11.2.1.4),
(11.2.1.9)). The fixed-position project repair retains the projection
(`.godel/obligations/trace-hardy-diagonal-q.md:234–257`), but does not
identify the actual rational global $S$-piece, shell lift, and right
orbital cutoff or establish any common admissible positive width.
The geometric and width dependencies remain provisional (PDF
pp. 494–496, (11.3.1.4), (11.3.2.3); pp. 517–519, (12.4.1.8–12),
(12.4.1.23–28); p. 454, (10.3.2.3–4); p. 463, Thm. 10.4.2.8;
p. 473, Def. 10.4.3.7).

**Reopen RH** after confirming the diagnostic is unassigned, identifying
those three global objects with the terminal right projection retained,
and establishing one common admissible positive half-width. In the
trivial compact isotype over $\mathbb Q$, compare the strip evaluation
with the actual right orbital contribution and both Mellin subtractions
on $b'$, for a nonzero nonnegative smooth bump $b$ supported in
$(0,\log 2)$. Take the level limit at fixed position support before
exhausting position. The existing control in
`.godel/obligations/trace-to-zeros.md:84–134` has zero mass and prime
samples, but its $+1/2$ Mellin moment is
$-\tfrac12\int e^{x/2}b(x)\,dx\ne0$. The specified joint local substitute
supplies the $-1/2$ subtraction but misses the $+1/2$ one. Prime-sample
vanishing is not orbital vanishing.

## Full Masullo GRH

The target is $\Re s=1/2$ for every nontrivial Hecke zero of every
continuous unitary idele-class character of every number field,
including ramified characters. The cycle evidence reader inspected
rendered crops at PDF p. 6 (Acknowledgements) and p. 528, §14.1.2.
The noncentral multiplicity bound and broader automorphic conjecture
are separate (PDF pp. 528–529, §14.1.2 and Conj. 14.1.2.1). A rational
specialization, conditional GRH implication, or isolated lemma is not
the target.

The following are accepted prerequisites, not a continued contour or
an evaluated global trace:

- `DiscriminantNormalizedIdeleHaar.lean:39–52` and
  `DiscriminantNormalizedIdeleHeckeGaussian.lean:37–54` construct
  calibrated upstairs Haar and give the absolutely integrable Gaussian
  pairing for every unitary character in $\Re s>1$. The pairing gives
  the completed Euler **product** times the discriminant scalar, not
  a meromorphic continuation. The opposite complex angular weight is
  a project repair (inherited rendered review in
  `.godel/obligations/complex-gaussian-angular.md`, PDF pp. 124, 130,
  151–153, (3.2.2.1), (3.3.1.7), (3.4.3.1), (3.4.3.5), (3.4.3.11)).
- Strict ideal-class quotient maps landed at
  `d171b684ba31797bdcdb50b71ebbdf4f6dc7eaed`, principal-idelic separation
  at `5a585d2dd809948ae15885ff32ca2a49b76de371`, and compact Hausdorffness
  of actual norm-one classes at `4177334d1f1c181aea409cc3d1de38a827a0204a`.
  Actual complex log-polar Haar landed at
  `4d544ed53817b1bd2db4be30907e85e318f16655` and signed real log Haar at
  the pin, each real sign with mass one. Exact review and audit locators
  are in `.godel/obligations/single-place-norm.md:181–392`. The compact
  cover is not a disjoint fundamental domain. The weighted log-coordinate
  measure split, half-open regulator box, torsion slice, and quotient
  Haar calibration are not supplied by these results. The manuscript
  comparison is provisional (PDF pp. 548–552, (A.2.3.3–5),
  (A.2.3.20–24), Prop. A.2.3.10; pp. 556, 559–560, Defs. A.3.1.2,
  A.3.2.1–2).
- `PadicConductorFourier.lean` supplies the primitive Fourier modulus
  and, at `3a54959e15a9d741e3d2aff3fa2c33ee93a25f6e`, the exact
  pulled-back unit conductor on $\mathbb Q_p$, not a phase, local
  functional equation, or global contour. `IdealClassHeckeCharacter.lean`
  at `47fe1b63817ea8043bda0dc6a020c7b724df1578` realizes continuous
  ideal-class pullbacks unramified at every finite place and identifies
  the per-place uniformizer coefficient. This is not a ramified
  comparison. See `.godel/obligations/hecke-right-line-majorant.md:521–610`
  and `.godel/obligations/isotypic-euler-factorization-q-sqrt-minus-five.md:202–260`
  for the source and review attribution.
- The reviewed theta-density, trace-class, and value/first-derivative
  descent notes at `aceedd47ecbce262ef762eb415ee425b35c47399`,
  `b529450077af23872e7c38ebdb87739e35af5850`, and
  `d668388c053856ee44823abc6202705076b206bb` are ordinary mathematics,
  not Lean. They concern the left-action conjugate weight-four isotype
  over $\mathbb Q(i)$ with $I=\{0\}$ and Sobolev index $4$. They do not
  establish the reverse closure inclusion, scalar trace evaluation, or
  transfer to positive width.

`Proofs/Props/HeckeContourReflection.lean:28–32,55–70` assumes the
functional-equation input and, for the contour integral, right-line
integrability. The general continued contour, including the reflected
log derivative, shifted polar/divisor data, and exhaustion, is still
missing (provisional dependencies: PDF pp. 124–127, Thm. 3.2.2.1;
pp. 135–141, §3.3; pp. 614–615, (B.4.2.1–4)). There is no normalized
common global diagonal on a specified admissible positive-width ramified
test. The cycle evidence reader's rendered crops corroborate the
inherited two-reader record `.godel/obligations/divisor-heading.json`:
PDF pp. 522–523, Thm. 13.3.1.2, has a heading and insertion note, not
a stated divisor theorem. The preceding capped trace (PDF p. 522,
Thm. 13.3.1.1, (13.3.1.1–5)) is not the all-zero conclusion.

**Reopen full GRH** after confirming the diagnostic is unassigned and
supplying both evaluations on one named admissible positive-width
ramified-isotype test: The completed contour and the normalized common
global diagonal. Compare full-order and strip-supported residues,
tracking central and identity terms separately.

## Overlap and stopping condition

Manuscript run `01a202bc-28b2-7b0f-b1ee-be8f46e5d318` landed the real
Haar theorem at the pin. Its handoff points to the Archimedean log-coordinate
measure split, also identified by the assessment's live observation;
that observation does not establish an accepted result or assignment of
either exact comparison. Companion run `01a202c3-de92-71ae-baa3-296ac2a6d107`
was working on the inert-prime factor during assessment. By closure it
had landed at `62aa183dce3d82128d01f90c0140449dda4c5ce6`, verified in
`Proofs/Theorems/IdealClassInertPrimeFactor.lean`: If $(p)$ is prime,
the fiber is a singleton and the class-character denominator is
$1-X^{[K:\mathbb Q]}$, in particular $1-X^2$ over $\mathbb Q(\sqrt{-5})$.
This post-pin result is off-scope for both comparisons and does not
move the assessment pin. Neither loop was directed or modified.

A mismatch on either diagnostic rejects the proposed comparison, not
the hypothesis. A match warrants broader testing, not a claim of RH or
GRH. Neither hypothesis was proved, refuted, or attempted in this cycle.
