# Rational theta inversion at the unramified tensor

**Status:** Independent Chapter 2 formalization target. The lattice
statement below has an independent Yah statement review against text
extracted from the digest-matched [pinned edition](../sources/masullo/README.md).
The reading is provisional, not visual. Nothing from this handoff is an
adopted Lean theorem.

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
This specialization does not formalize the adelic reduction itself:
The identification of the finite factors, tensor Fourier transform,
and norm section above describes why the real statement models this
passage. It gives no theorem for other finite inputs or number fields.

## Next runnable step: Split the zero modes in scaled Poisson summation

In pinned Mathlib specialize `SchwartzMap.tsum_eq_tsum_fourier` at zero
to the dilation $x\mapsto b(tx)$. Build that Schwartz map using
`SchwartzMap.compCLMOfContinuousLinearEquiv` and the equivalence for
multiplication by the unit `Units.mk0 t ht.ne'`. Use
`Real.fourier_real_eq_integral_exp_smul` and
`MeasureTheory.Measure.integral_comp_mul_left` to compute its transform
as $t^{-1}\widehat b(t^{-1}u)$; positivity of $t$ removes the absolute
value. The Schwartz decay bound `isBigO_cocompact_rpow` at exponent $-2$
and `Int.tendsto_coe_cofinite` give absolute summability of the two
lattice sums. Use `Summable.sum_add_tsum_compl` with $\{0\}$ to remove
exactly one term from each. Put the corrected inversion statement in
`Proofs/Theorems/` and its supporting machinery in `Proofs/Lemmas/` as
needed. The project endpoint still needs the local candidate checks.

**Feasibility check:** A disposable `lake env lean` probe in a campaign
workspace based on `585fe1d17f6d` elaborated the scaled formula with
all integer indices,
$\sum_{n\in\mathbb Z}b(tn)=t^{-1}\sum_{n\in\mathbb Z}\widehat b(t^{-1}n)$,
for arbitrary complex Schwartz $b$ and $t>0$. It used the dilation and
change of variables above, then `tsum_mul_left` to take the scalar
outside the sum. This was not a Lake build or axiom audit of a project
declaration, and it did not split out the zero modes.

Theorem 2.2.3.4, (2.2.3.5)–(2.2.3.7), p. 83, uses inversion to
reduce the small-norm estimate to large-norm Schwartz decay on the
Fourier side. Its rational two-moment bound is a useful next consumer:
It would support the log-tail estimates in the [rational orbital theta
lifts](trace-orbital-q.md#genuine-global-theta-lifts) without assuming
a trace formula. It would not prove density, identify a Paley–Wiener
projection, or compute the global geometric trace's Mellin corrections.
