# Summability of the rational zero divisor

**Status:** Project route for the multiplicity-weighted summability premise of [conditional uniqueness](../../Proofs/Props/ZeroMassUniqueness.lean). The [factorial growth estimate](../../Proofs/Lemmas/CompletedZetaGrowth.lean) is a Lean lemma. The transfer of orders, Jensen bound, and final summability are not yet in Lean. None of these steps needs the capped trace comparison.

## Match the weight, not just convergence of the explicit formula

In the digest-matched layout extraction, (B.4.2.2), p. 614, counts the full zeros with multiplicity and takes a height-exhausted limit against a Schwartz Mellin transform. Its cited slow-growth condition (Definition B.3.1.1, p. 604) controls the logarithmic derivative on contours; the residue theorem on pp. 605–606 takes the limit of such contour integrals. These statements do not give absolute summability against the specific quadratic weight in `weight_eq_zero_of_zero_mass_annihilation`. Likewise, the convergence assertion on p. 522 follows a sum over capped critical-line weights, not the full multiplicity-weighted sum. These are provisional text readings; the arithmetic estimate below is independent of them.

For distinct zeros $\rho$ with $0<\Re\rho<1$, the needed target is

$$\sum_\rho\frac{\operatorname{ord}_\rho\zeta}{1+|\rho-1/2|^2}<\infty.$$

With finite positive orders, this bounds the absolute weights of the full-minus-capped sum: Subtracting the critical-line indicator changes a positive integer $m$ only to $m-1$ or leaves it unchanged. Discreteness alone does not bound this series. The index type `Masullo.criticalStripZetaZeros` and its [compact-preimage finiteness](trace-divisor-uniqueness.md#checked-separation-of-the-shifted-zeta-zeros) are now in Lean. Use this same family for orders and the bounded inner disk. Neither its local finiteness nor countability controls the weighted outer shells.

## Checked growth estimate

Write $\Lambda_0$ for Mathlib's `completedRiemannZeta₀`, not the meromorphic `completedRiemannZeta`. Its modified theta kernel is real nonnegative: For $t>1$ this follows from the Gaussian sum after removing the constant term, and for $t<1$ it follows by theta inversion. On $1-m\le\Re s\le m$, the Mellin integrand's absolute value is dominated by the sum of the real integrands at $1-m$ and $m$. Their integrals are equal by the functional equation. Take $m=2(n+1)$ when $|\Re s|\le n$. At $m$ the Dirichlet series is bounded by $\sum_{k\ge1} k^{-2}$, the gamma factor is $n!$, the power of $\pi$ is at most one, and each polar correction is bounded by one. This yields `Masullo.completedZeta₀_factorial_growth`: There is a fixed $C\ge1$ with $|\Lambda_0(s)|\le C n!$ under that real-part bound, uniformly in the imaginary part.

## Next runnable step: Transfer orders to an entire function

Use the entire function $F(s)=1+s(s-1)\Lambda_0(s)$, which satisfies $F(1)=1$. On the open critical strip, `completedRiemannZeta_eq` and `riemannZeta_def_of_ne_zero` give

$$F(s)=s(s-1)\Gamma_{\mathbb R}(s)\zeta(s).$$

The factor $s(s-1)\Gamma_{\mathbb R}(s)$ is analytic and nonzero there. For the order identity use equality on a neighborhood of each strip point, not just equality at the point. Use `analyticOrderAt_mul` and the order-zero criterion for a nonvanishing analytic factor; take the natural-valued order only after ruling out infinite order using the nonzero entire function $F$. Avoid using $s(s-1)\Lambda_0(s)$ without the $1$: That function does not preserve the zero divisor.

Then use `AnalyticOnNhd.sum_divisor_le` from `Mathlib.Analysis.Complex.JensenFormula` on disks centered at $1$, with radii $R$ and $2R$ for integers $R\ge1$. On the larger disk take $n=2R+1$ in the growth estimate and bound $|s(s-1)|\le (2R+1)2R$. Thus the logarithm of the norm bound is $O(R\log(2+R))$ by $n!\le n^n$. Keep orders in the count: `AnalyticOnNhd.divisor_apply` reads the multiplicity, and the contributions from other points of the disk are nonnegative. On the shell $2^j\le|\rho-1/2|<2^{j+1}$, $|\rho-1|\le 2^{j+1}+1$, and dividing the disk count by $2^{2j}$ gives a summable bound of order $(j+1)2^{-j}$. The bounded inner disk is locally finite. This proves the mathematical route to the quadratic summability input; neither Mathlib's local finiteness theorem nor existence of the manuscript's explicit-formula limit alone replaces these steps.
