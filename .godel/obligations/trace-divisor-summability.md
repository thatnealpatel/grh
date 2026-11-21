# Summability of the rational zero divisor

**Status:** Project route for the multiplicity-weighted summability premise of [conditional uniqueness](../../Proofs/Props/ZeroMassUniqueness.lean). The [factorial growth estimate](../../Proofs/Lemmas/CompletedZetaGrowth.lean), [order transfer](../../Proofs/Lemmas/ZetaZeroOrders.lean), and [Jensen disk count](../../Proofs/Lemmas/ZetaZeroDiskCount.lean) are in Lean. Dyadic-shell summability is not yet in Lean. None of these steps needs the capped trace comparison.

## Match the weight, not just convergence of the explicit formula

In the digest-matched layout extraction, (B.4.2.2), p. 614, counts the full zeros with multiplicity and takes a height-exhausted limit against a Schwartz Mellin transform. Its cited slow-growth condition (Definition B.3.1.1, p. 604) controls the logarithmic derivative on contours; the residue theorem on pp. 605–606 takes the limit of such contour integrals. These statements do not give absolute summability against the specific quadratic weight in `weight_eq_zero_of_zero_mass_annihilation`. Likewise, the convergence assertion on p. 522 follows a sum over capped critical-line weights, not the full multiplicity-weighted sum. These are provisional text readings; the arithmetic estimate below is independent of them.

For distinct zeros $\rho$ with $0<\Re\rho<1$, the needed target is

$$\sum_\rho\frac{\operatorname{ord}_\rho\zeta}{1+|\rho-1/2|^2}<\infty.$$

With finite positive orders, this bounds the absolute weights of the full-minus-capped sum: Subtracting the critical-line indicator changes a positive integer $m$ only to $m-1$ or leaves it unchanged. Discreteness alone does not bound this series. The index type `Masullo.criticalStripZetaZeros` and its [compact-preimage finiteness](trace-divisor-uniqueness.md#checked-separation-of-the-shifted-zeta-zeros) are now in Lean. Use this same family for orders and the bounded inner disk. Neither its local finiteness nor countability controls the weighted outer shells.

## Checked growth estimate

Write $\Lambda_0$ for Mathlib's `completedRiemannZeta₀`, not the meromorphic `completedRiemannZeta`. Its modified theta kernel is real nonnegative: For $t>1$ this follows from the Gaussian sum after removing the constant term, and for $t<1$ it follows by theta inversion. On $1-m\le\Re s\le m$, the Mellin integrand's absolute value is dominated by the sum of the real integrands at $1-m$ and $m$. Their integrals are equal by the functional equation. Take $m=2(n+1)$ when $|\Re s|\le n$. At $m$ the Dirichlet series is bounded by $\sum_{k\ge1} k^{-2}$, the gamma factor is $n!$, the power of $\pi$ is at most one, and each polar correction is bounded by one. This yields `Masullo.completedZeta₀_factorial_growth`: There is a fixed $C\ge1$ with $|\Lambda_0(s)|\le C n!$ under that real-part bound, uniformly in the imaginary part.

## Checked transfer of orders to an entire function

In the digest-matched layout extraction of p. 123, Definition 3.2.1.2 uses the completed product (3.2.1.2), whose rational trivial-character real factor in (3.2.1.4) is $\pi^{-s/2}\Gamma(s/2)$. The rational strip orders in the p. 614 sum thus concern the completed function, not the poles of the gamma factor outside the strip. This is a provisional text reading. The Lean bridge below works with Mathlib's rational zeta functions, not a formalized adelic $L$-function.

The project uses the entire function `Masullo.entireZeta`, $F(s)=1+s(s-1)\Lambda_0(s)$, with $F(1)=1$. On the open critical strip, `completedRiemannZeta_eq` and `riemannZeta_def_of_ne_zero` give

$$F(s)=s(s-1)\Gamma_{\mathbb R}(s)\zeta(s).$$

`Masullo.analyticOrderAt_entireZeta_eq` uses this equality on a neighborhood of each strip point. The analytic factor $s(s-1)\Gamma_{\mathbb R}(s)$ is nonzero there, so it does not change the order. The identity theorem and $F(1)=1$ exclude infinite order. For each existing `criticalStripZetaZeros` index $\rho$, `Masullo.zetaZeroOrder_pos` verifies that the natural-valued `zetaZeroOrder` is positive, and `Masullo.divisor_entireZeta_apply` identifies it with the divisor coefficient on any set containing $\rho$. The coercion in that last step uses finiteness before converting to a natural number. An order transfer for $s(s-1)\Lambda_0(s)$ without the $1$ would not preserve the zero divisor.

## Checked disk count with Jensen

For an integer $R\ge1$, put $n=2R+1$ and $M_R=1+n(2R) C n!$, using the same $C$ for all radii and finite sets. `Masullo.sum_zetaZeroOrder_le_jensen` proves that every finite set $A$ of `criticalStripZetaZeros` contained in $|\rho-1|\le R$ satisfies

$$\sum_{\rho\in A} \operatorname{zetaZeroOrder}(\rho) \le \frac{\log M_R}{\log 2}.$$

The proof uses `AnalyticOnNhd.sum_divisor_le` at center $1$ with radii $R$ and $2R$, and $F(1)=1$. On the outer sphere $|s-1|=2R$, the bound $|\Re s|\le |s|\le n$ supplies the hypothesis of `completedZeta₀_factorial_growth`, so $|F(s)|\le M_R$. On the inner closed disk, map $A$ by the injective subtype coercion and use `divisor_entireZeta_apply`. The total divisor has finite support by compactness, and omitted terms are nonnegative by analyticity. The estimate includes zeros on the inner boundary and does not require classifying the other zeros of $F$. Independent Yah statement review checked the uniform constant, both disk boundaries, the finite-subset comparison, and the attribution against the digest-matched p. 614 extraction. This is a project estimate, not a formalization of the p. 614 contour argument.

## Next runnable step: Prove dyadic-shell summability

First specialize the count to $R=2^{j+1}+1$ for $j\in\mathbb N$. Use `Nat.factorial_le_pow` to get $M_R\le(C+1)n^{n+2}$. Since $n=2^{j+2}+3\le2^{j+3}$ and $n+2\le2^{j+4}$, `Real.log_le_log`, `Real.log_mul`, and `Real.log_pow` give a bound of the form $K(j+3)2^j$ for the count, with $K$ independent of $j$ and the finite subset.

On the shell $2^j\le|\rho-1/2|<2^{j+1}$, $|\rho-1|\le R$ and the quadratic denominator is at least $2^{2j}$. Apply the specialized count to the whole shell, which is finite by `shiftedZetaZero_preimage_finite` and containment in a closed disk. Its weighted sum is at most $K(j+3)/2^j$, a summable bound by `summable_pow_mul_geometric_of_norm_lt_one` at $k=1$ together with the geometric series. Include the finite disk $|\rho-1/2|<1$ separately. One Lean route is to identify the outer indices with the sigma type of the shells and apply `summable_sigma_of_nonneg`; the bound on the least dyadic upper radius gives existence and uniqueness of the index. The endpoint must use `zetaZeroOrder` over `criticalStripZetaZeros` and the quadratic weight in the proposition, not just the cardinality of the shells or the summability of a faster-decaying test.
