# Compact support of the global theta periodization

**Printed passage.** Masullo, *The Music of the Primes*, claim in
§1.7.1, printed p. 33, first bullet, from “By far the most important
difference” through “the Paley-Wiener Theorem.” For a number field $F$
and Schwartz–Bruhat input $f$ with $f(0)=\widehat f(0)=0$, the sum
$\Phi_F(f)(g)=\sum_{\xi\in F^\times} f(\xi g)$ on $C_F$ is said to
be Schwartz–Bruhat and, unless identically zero, never compactly
supported. The parenthesis extends the Schwartz–Bruhat assertion to
global function fields; it does not extend noncompactness. The
author cites Tate for removing the poles of the raw zeta integral,
and suggests Stirling, convexity, and Paley–Wiener for the support
assertion. “Caveat ??” is unresolved in print, not an identified
source of evidence for an earlier calculation.

The [pinned PDF](../sources/masullo/README.md) matches the recorded
SHA-256. The chapter Markdown and PDF layout extraction located the
passage. OCR on the rendered crop and direct inspection of the pixel
crops spot-checked the unresolved reference, the scope of the function
field parenthesis, and the noncompact-support conclusion. The forward
citations below were located by extraction; their use is provisional
pending rendered-page review.

**Schwartz–Bruhat assertion.** In the number-field case, this is weaker
than the weighted membership preview in §1.1.4, p. 12. Masullo's
Theorem 2.2.3.4(3), pp. 82–84, concerns pointwise decay at both norm
ends. To obtain full Schwartz–Bruhat membership, one still needs
smooth descent to a single quotient of $C_F$ by a compact subgroup
with compactly generated annihilator, and decay of all the required
derivatives there. A finite-idelic open unit subgroup fixing $f$ is
the natural candidate for the quotient. The proposed derivative check
uses Lemmas 2.2.4.3, pp. 88–91, and 2.2.4.5(1), pp. 91–92, to
iterate differentiation on two-zero-mode inputs before applying the
decay estimate. In the function-field case, compact additive support
and the product formula give an upper bound for the idelic norm on
the support of the sum. Given the two-zero-mode Poisson identity, the
same argument for $\widehat f$ bounds the norm away from zero. With a
compact norm-one kernel and discrete norm image, the surviving norm
fibres form a compact set. Local constancy follows if the sum descends
through a fixed open unit stabilizer of $f$. This is a conditional
check of the function-field branch, not an accepted proof of those
inputs.

**Noncompactness assertion.** Rapid decay, even to all exponential
orders in log norm, does not exclude compact support. Nor do Stirling
and convexity for the completed and finite Hecke factors give
exponential decay for the Mellin transform of an arbitrary $f$:
Weil's factorization includes a test-dependent multiplier. Even if
that multiplier is holomorphic, no requisite growth control follows
from holomorphy alone. A direct decay argument would have to prove
such control and then exclude a nonzero compactly supported log
profile by Fourier inversion and analyticity. The passage supplies
neither that control nor an alternate contradiction.

A separate, conditional route is to split the norm and project a
putative nonzero compactly supported periodization onto a nonzero
$C_F^1$ Fourier coefficient. Compact-abelian Fourier uniqueness gives
such a coefficient, and the log norm of the support bounds its
support in a finite interval. Its log-Mellin transform is nonzero by
Fourier uniqueness and entire of exponential type by the elementary
compact-support bound (the forward direction of the Paley–Wiener
statement in Theorem 4.2.2.1, pp. 170–171). Jensen's formula gives
$O(T)$ zeros with multiplicity in a disk of radius $T$, by centring
at a point where the transform does not vanish and applying Jensen
at twice the radius. Masullo's Theorem 3.2.2.1, pp. 124–127, identifies
the Mellin transform with the raw zeta integral continued on that
character component. Theorem 3.4.3.3(2), (3.4.3.15), pp. 152–153,
would force the transform to inherit the completed Hecke factor's
zeros with multiplicity if the multiplier is holomorphic there. The
remaining input for this route is a checked superlinear zero count
(for example a $T\log T$ lower bound with multiplicity in a fixed
vertical strip) for the fixed completed Hecke factor of whichever
character is selected by the projection. No estimate uniform over
characters is needed. This is the reviewer's conditional argument,
not a derivation supplied in the letter. The polynomial bound on the
finite factor in Proposition B.1.1.3, p. 591, is not itself that
zero count. No zero-count locator is assigned to the unresolved
“Caveat ??” citation.

**Accepted evidence and limits.** At
`a388a0824177684ea01ff4dddc2d6f085d74e33f`,
`Masullo.idele_periodization_rapidDecay_of_support` in
`Proofs/Theorems/IdeleClassRapidDecay.lean` controls the large-norm
absolute sum for number fields under explicit finite-support and
Archimedean weight hypotheses, using a scalar section rather than the
printed scaling calculation. It is not a two-ended Schwartz–Bruhat
membership or support theorem. In
`Proofs/Theorems/RationalAdeleLFThetaTails.lean`,
`Masullo.rationalAdeleLF_uniform_theta_log_bound` gives the two-ended
pointwise bound for the rational Schwartz LF space on bounded sets
when both zero modes vanish, not general membership or noncompactness.
`Masullo.integral_ideleClass_Weil_weighted` in
`Proofs/Theorems/IdeleClassWeil.lean` is weighted unfolding for
integrable input in the indicated split measures, not the Hecke
factorization. These are comparisons with accepted source signatures,
not a fresh independent verification of the general passage. The
formal finding is open.
