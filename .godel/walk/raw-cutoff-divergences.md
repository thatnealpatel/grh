# The two divergences invoked in the letter to Sarnak

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 35,
§1.7.2, first bullet, paragraph from “This assumption cannot be
removed” through “that (1.7.2.1) holds.” He says that vanishing on the
whole norm-one subgroup must be kept until GRH is deduced from the
trace formula, and that two divergence phenomena can be resolved only
under that condition. The paragraph does not identify either divergence.
This reading stops before the claim about convolution squares.

Chapter Markdown and PDF layout extraction located the paragraph in
the [digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the paragraph, and direct inspection of rendered crops checked
“cannot be removed,” “two divergence phenomena,” “only be resolved,”
and the reference to (1.7.2.1). Rendered crops also checked the global
subtraction in (10.4.2.10), p. 460, the identity-value hypothesis and
sign in the argument around (12.1.1.23), p. 503, and the local logarithm
in (12.4.1.3), p. 514. The surrounding arguments were read from the
chapter transcription and PDF extraction.

**Two candidate cutoff terms, not an identification of the pair.**

- **Global:** Remark 10.4.2.3 displays a subtraction of the geometric
  cutoff trace from $2\log(\Lambda)\overline\mu_1(C_F^1)\varphi(1)$.
  Theorem 12.1.1.3, pp. 502–503, uses $\varphi(1)=0$ to identify the
  smoothed geometric diagonal with the negative spectral diagonal.
  Where the claimed diagonal identification and spectral integrability
  are available, the unsuppressed summand is the constant $\varphi(1)$.
  Its integral against the position cutoff grows with the log-norm
  length of the cutoff, giving the raw global divergence when
  $\varphi(1)\ne 0$. This reasoning uses the integrability under the
  hypotheses of the localization argument, which prints $s\ge 3$;
  it does not establish that integrability at degree zero.
- **Local:** Theorem 12.4.1.1, p. 514, states a normalized $S$-local
  position-and-Fourier-cutoff asymptotic with
  $+\varphi(1)\log(\lambda\lambda')$. This is a different operator
  and cutoff from the global position truncation. The [geometric
  audit](../obligations/trace-geometric.md) separates justification of
  this asymptotic from identification with the global residual diagonal.

Both displayed logarithms vanish already when $\varphi(1)=0$.
That condition is strictly weaker than (1.7.2.1): On the rational
idèle class group, multiply a compact smooth log-norm bump equal to
one at zero by one minus the nontrivial mod-3 character on the compact
unit factor. The result vanishes at the identity but not on the whole
fibre. This distinguishes the hypotheses; it does not evaluate the
remaining orbital terms on the larger class.

**Missing step.** To support the claimed necessity, identify the two
limits meant here and exhibit an obstruction on tests with
$\varphi(1)=0$ but $\varphi|_{C_F^1}\ne0$, after using the actual
orbit sums, local principal values, and any cancellations in the
specified cutoff comparison. Alternatively, an extension using
subtraction would need to match the global and local cutoff regimes,
Haar factors, and finite parts, not just discard the two logs. The
[earlier a posteriori claim](unrestricted-trace-preview.md) separates
changing the zero sum from constructing such a finite-part trace.
Zero location, even if established, would change the indexing of the
sum, not remove either raw cutoff term.

The assertion of necessity and the two cutoff calculations are
Masullo’s. The pairing of the displayed terms as candidates, the
identity-versus-fibre distinction, and the missing comparison are
reviewer analysis. The accepted
[`Masullo.rationalIdeleRadial_explicit_formula`](../obligations/rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula)
allows smooth compact radial log profiles nonzero at log norm zero.
It gives a scalar formula over $\mathbb Q$ with trivial compact
isotype and the full zeta zero sum counted by order. It does not
identify either operator cutoff limit or decide the printed general
claim. No new Lean result is claimed.
