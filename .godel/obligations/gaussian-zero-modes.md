# Integrate the removed Gaussian zero modes

[`integral_logMellin_zeroModes`](../../Proofs/Theorems/IdeleClassMellinZeroModes.lean)
evaluates the two removed terms with the character on the section still
present. Put $x=\log t$ in (3.2.2.4)–(5), PDF p. 125. In the notation
of [weighted Gaussian decay](single-place-norm.md#weighted-gaussian-decay-at-small-norm),
set $A=m(C_K^1)\delta_\omega\widehat f(0)$ and
$B=m(C_K^1)\delta_\omega f(0)$. The measure in $\widehat f$ is additive;
$m$ is the counting-normalized multiplicative quotient measure. Neither
can be replaced by the other or by a probability normalization.

Equation (2.2.5.10), p. 97, supplies the signs and the two powers on the
small-norm side; its proof on p. 98 passes the pointwise estimate
through the finite norm-one Haar. Theorem 3.2.2.1(1a), p. 124, states
the residues in quasicharacter coordinates, citing the general zeta
continuation in the proof on p. 126. Lean instead computes the actual
subtraction integral in the radial coordinates of (3.2.2.4)–(5): If
the section phase is $e^{i\lambda x}$, then for $\Re s>1$ the integrand
below is absolutely integrable and

$$
\int_{\mathbb R} 1_{x<0}(e^{-x}A-B)e^{i\lambda x}e^{sx}\,dx
= \frac{A}{s+i\lambda-1}-\frac{B}{s+i\lambda}.
$$

The proof combines the exponentials first, then uses the one-sided
complex exponential integral for $s+i\lambda-1$ and $s+i\lambda$,
whose real parts are positive in this domain. The strict cutoff matches
the corrected profile convention; including $x=0$ would not change the
integral. The statement does not assume that the entire weighted class
integral is absolutely convergent outside the right half-plane.

**Evidence:** Accepted candidate
`867506623c5f4e04ff9002f6e75bd7db1381eadf`, owning Yah session
`01a20550-d5a6-78a3-9def-ba66465b8227`. The warning-failing build and
fresh signature and axiom check passed, with only the allowed axioms.
Independent reviewer `vpqNcax` (report
`078537ae74629095a2942c495a1026daa2dc41ce`) inspected tight Braille
raster crops of PDF pp. 97, 124, and 125 for the signs, Fourier hat,
and radial factor. The wider reading, including p. 98 and the
normalization dependencies, is provisional from Markdown and layout.

**Next: Assemble the continuation.** Use
`existsUnique_unitary_oneParameterCharacter` on the actual continuous
norm section composed with $\chi$; use that frequency to instantiate the
scalar theorem. For the same fixed-stage witnesses, add the two rational
terms to the entire corrected Mellin integral and use integral addition
on $\Re s>1$ to recover the already checked uncorrected radial value
there. Keep the inverse square root of the absolute discriminant until
rescaling to the completed Euler product. Prove meromorphy of the sum
and holomorphy off the two possible poles (everywhere if $\omega$ is
nontrivial). The scalar evaluation alone is not the continuation, the
functional equation, or an assertion about the zeros.
