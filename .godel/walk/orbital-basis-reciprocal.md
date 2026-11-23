# Reciprocal outside-S Mellin multiplication and orbital bases

**Status: Open at the printed scope.** Masullo, *The Music of the
Primes*, §1.4.7, printed p. 31, argument preview from “To propagate
the orbital Schauder bases” through “growing boxes with fixed
horizontal width.” Masullo takes a local basis element represented
by a theta function, applies the transition $p_S$, and proposes to
undo its Mellin multiplier by $1/L^S(s,\chi)$ on the strength of
nonvanishing on $1+i\mathbb R$, using the Residue Theorem on the
indicated boxes. The ensuing list of growth inputs is not reviewed
here.

Chapter Markdown and PDF layout extraction located the passage in the
[digest-verified edition](../sources/masullo/README.md). OCR of the
rendered raster checked the prose, and direct inspection of rendered
pixel crops checked the line, the reciprocal, and the box phrase.
Later passages are identified below by extraction or by separately
credited accepted source audits.

**What cancellation gives.** On the unramified components where the
[preceding transition comparison](transition-mellin-multiplier.md)
has been justified with compatible Haar normalization, division on
the known image recovers the local transform meromorphically. With
unscaled measures the omitted unit-mass product must also be divided
out. This is only cancellation, not a continuous inverse on a
specified space of global transforms. For unitary $\chi$, the finite
reciprocal Euler factors removed from $L_f$ are nonzero on $\Re s=1$:
At an unramified place the subtracted term has modulus $q_v^{-1}$,
and at a character-ramified place the factor is $1$. Thus the
boundary no-zero input concerns zeros, not poles. At the shifted
Dedekind pole for a norm twist of the trivial character,
$1/L^S$ extends with a zero; an ordinary invertible jet comparison
there does not follow from pointwise nonvanishing elsewhere.

**What the transport still needs.** For the topological division
route, prove that after cancellation to the required orders the
quotients retain the defining weighted seminorm bounds on closed
interior strips. The finite-box argument needs control on all sides,
not just selected horizontal edges or a bound on $\Re s=1$. The
accepted [forward-division audit](../obligations/isotypic-forward-division-q-sqrt-minus-five.md)
checks the proof of Theorem 6.3.2.1 after (6.3.2.13), p. 306: The cited
Asymptotic Residue Theorem requires its own vertical-line inputs, and
its integral identity does not by itself give the uniform quotient
estimate. That audit supplies a separate interior-circle repair for
one class character of $\mathbb Q(\sqrt{-5})$, not the claimed basis
transport.

For basis transport one further needs a continuous comparison on the
actual orbital subquotients, including compatibility with the
principal-value ranges, and control of the inverse coordinate change
in the topology in which the basis expansions converge. A
provisional extraction reading of Theorem 7.5.0.1, pp. 374–378, makes
this concrete for the finite-prime comparison: The blocks in
(7.5.0.9)–(13) require inverse bounds uniform up to a polynomial in
height, and finite invertibility with justified jet orders at the
exceptional reflected frequency. In the trivial character the local
reciprocal Euler factor can vanish at $s_c=0$, so the reflected point
is $1$. The ordinary Leibniz matrix with an unregularized multiplier
at that pole is not justified by the boundary input; the two vanishing
moments must be used and the resulting jet orders checked. See the
[boundary preview](boundary-nonvanishing-preview.md). This is a
precise missing step, not a refutation of the later comparison.

**Provenance and formal scope.** The proposed contour and basis
arguments are Masullo's. The distinction between cancellation and
basis transport is the reviewer's audit. The existing Lean theorem
`Masullo.norm_pow_mul_le_on_strip_of_separated_heights`
(`Proofs/Lemmas/SeparatedHeightStripBound.lean`, accepted candidate
`da4e9339f373d04b782a4e346dfbafe993c07e34`) gives a weighted scalar
maximum-modulus estimate for a function holomorphic inside and
continuous up to a strip, given common bounds on both vertical edges
and arbitrarily distant horizontal edges. It assumes those bounds
and holomorphy; it does not prove the needed Hecke estimates, Mellin
divisibility, or a basis theorem. The accepted
[inverse-range audit](../obligations/isotypic-inverse-range-q-sqrt-minus-five.md)
documents its checked scope and the specialized application. No new
Lean result or resolution of the general preview is claimed.
