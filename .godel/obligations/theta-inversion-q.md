# Rational theta inversion at the unramified tensor

**Status:** The [real-lattice theorem](../../Proofs/Theorems/RationalThetaInversion.lean)
is in Lean as `Masullo.rationalTheta_inversion`, with an independent Yah
statement review against text extracted from the digest-matched
[pinned edition](../sources/masullo/README.md). The reading is provisional,
not visual. The adelic reduction itself is not formalized.

## Manuscript statement and rational reduction

Definition 2.2.3.1, (2.2.3.1), pp. 81–82, omits zero from the global
adelic theta sum. Theorem 2.2.3.2, (2.2.3.2)–(2.2.3.3), p. 82,
relates the theta function at an idele class to the Fourier-side theta
function at its inverse, with two zero-mode corrections. Remark 2.2.3.3
sets the additive quotient volume to one. Example A.3.1.5, p. 557, uses
Lebesgue measure and the real Fourier kernel $e^{-2\pi ixy}$; Examples
A.3.1.6–8, pp. 557–558, give self-duality of $\mathbf1_{\mathbb Z_p}$
with unit additive volume and the rational global normalization.

Take $F=\mathbb Q$, the tensor $b\otimes\prod_p\mathbf1_{\mathbb Z_p}$
for $b\in\mathcal S(\mathbb R,\mathbb C)$, and the real section
$(t,1,1,\ldots)$ of norm $t>0$. The finite support condition reduces the
nonzero rational indices to nonzero integers. The finite Fourier
factors are unchanged, so the Fourier-side sum has the same reduction
at $t^{-1}$. With
$\theta_b(t)=\sum_{n\in\mathbb Z\setminus\{0\}}b(tn)$, the resulting
real-lattice statement is

$$
\theta_b(t)=t^{-1}\theta_{\widehat b}(t^{-1})
           +t^{-1}\widehat b(0)-b(0).
$$

Retain both zero modes for arbitrary complex Schwartz $b$. Neither
evenness nor a Gaussian hypothesis is needed. The two-moment case
$b(0)=\widehat b(0)=0$ is a corollary, not the inversion statement.
The identification of the finite factors, tensor Fourier transform,
and norm section above explains why the checked real statement models
this passage. It gives no theorem for other finite inputs or number
fields.

## Checked real-lattice inversion

The [scaled Poisson lemmas](../../Proofs/Lemmas/ScaledPoisson.lean)
specialize `SchwartzMap.tsum_eq_tsum_fourier` at zero to $x\mapsto b(tx)$.
The Fourier dilation uses the Lebesgue change of variables and $t>0$, so
the transform is $t^{-1}\widehat b(t^{-1}u)$. Schwartz decay at exponent
$-2$ and `Int.tendsto_coe_cofinite` give absolute summability of the
integer samples. The theorem applies `Summable.sum_add_tsum_compl`
with $\{0\}$ to each side before rearranging. This proof uses Mathlib's
real Poisson summation; the manuscript invokes adelic Poisson summation.

## Next runnable step: Prove the fixed-function two-tail estimates

Theorem 2.2.3.4, (2.2.3.4)–(2.2.3.7), pp. 82–83, uses inversion to
reduce the small-norm estimate to large-norm Schwartz decay on the
Fourier side. For each fixed $b\in\mathcal S(\mathbb R,\mathbb C)$ and
$N\in\mathbb N$, prove the rational lattice estimates with some $C>0$:

- At $t\ge1$, $|\theta_b(t)|\le C/t^N$.
- At $0<t\le1$, $|\theta_b(t)-t^{-1}\widehat b(0)+b(0)|\le C t^N$.

For the first bound use `SchwartzMap.decay` at $(k,d)=(N+2,0)$.
At every nonzero integer $n$, the resulting bound is
$C_b t^{-(N+2)}|n|^{-(N+2)}$. Compare the sum of norms against this
majorant: `Real.summable_abs_int_rpow` restricts to the nonzero
subtype, `Real.rpow_neg` and `Real.rpow_natCast` connect the powers,
and `norm_tsum_le_tsum_norm` applies using the absolute convergence
lemma above. For the second bound, apply the first to $\widehat b$
at scale $t^{-1}\ge1$ and exponent $N+1$, not $N$, to absorb the
factor $t^{-1}$ in inversion. Enlarge $C$ to cover both estimates.
These estimates require no moment hypotheses on $b$; the two moments
vanish only in the corollary for bare theta at small scales.

This is a fixed-function version, not the uniform bounded-family
assertions (4)–(5). The two-moment specialization would support
log-tail estimates in the [rational orbital theta lifts](trace-orbital-q.md#genuine-global-theta-lifts)
without assuming a trace formula. It would not prove density, identify
a Paley–Wiener projection, or compute the global trace's Mellin
corrections.
