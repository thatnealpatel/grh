---
evidence_revision: e97a8a47fbd771a5d2d069a46a8792a4b0c0f902
outcome: established
---

# Identify the mod-eight endpoint budget by residues

For the even primitive character $\chi_8$, use the entire conductor-normalized completion $\Lambda=$ `Chi8Entire.Λ`, and put $D=\Lambda'/\Lambda$. Index the zeros by `Chi8ZeroKernel.Zero`, the distinct zeros in the open critical strip, with their analytic multiplicities $m(\rho)$. The target is that, assuming every such zero has real part $1/2$, the unordered series has sum

$$
\sum_\rho \frac{m(\rho)}{|\rho|^2}=C,\qquad C=\operatorname{Re}(D(1)-D(0)).
$$

[Chi8ZeroBudget](../../../Proofs/Examples/Chi8ZeroBudget.lean) already proves the endpoint identity, $C<3/2$, and unconditional summability of the weights. Its identifications of the sum require additional analytic hypotheses. This card asks to remove those hypotheses, not to prove the critical-line hypothesis or an eventual race sign.

**Next discriminating test:** Integrate $D(s)/[s(1-s)]$ on a positively oriented rectangle $R$ with $0,1$ inside and no zero on its boundary. Prove the finite identity first, without a zero-location assumption:

$$
\frac{1}{2\pi i}\oint_{\partial R}\frac{D(s)}{s(1-s)}\,ds
=D(0)-D(1)+\sum_{\rho\in\mathrm{int}(R)}\frac{m(\rho)}{\rho(1-\rho)}.
$$

At $0$ use the nonvanishing entire continuation, not the pointwise Gamma-times-$L$ product. At $1$ the kernel has residue $-1$. On the critical line $1-\rho=\bar\rho$, so the last sum is exactly the finite real weight sum. Compare the [rectangle residue machinery](../../../Proofs/Props/RectangleResidue.lean) and its [mod-three application](../../../Proofs/Theorems/DirichletThreeRectangleResidues.lean); do not assume their edge estimates apply to this kernel.

**Global test:** Exhibit rectangles that eventually contain each strip zero and for which the normalized boundary integral tends to zero (its real part suffices). Separate the two horizontal and two vertical edges, or justify any paired cancellation. Good heights alone do not remove fixed vertical edges. Under the critical-line hypothesis the landed summability then identifies the exhausted finite sums with the unordered sum. A finite rectangle theorem is useful partial progress, not closure of this card. If exhaustion stalls, record the specific unproved edge or cancellation estimate and the contour family it concerns.

## Resolution

[Chi8RectangleResidues](../../../Proofs/Examples/Chi8RectangleResidues.lean) proves `Chi8ZeroBudget.rectangleIntegral_eq_endpoint_sub_add_sum` for any rectangle with the stated interior and boundary conditions, without a zero-location hypothesis. Both endpoints are nonzeros of the entire completion. The factors at the endpoints are $D(s)/(1-s)$ divided by $s$, and $-D(s)/s$ divided by $s-1$, respectively. Each interior zero of the completion is indexed exactly once by `Chi8ZeroKernel.Zero`, with analytic order preserved by the nonvanishing completion factors in the strip. The oriented boundary is bottom plus right minus top minus left (vertical parameters carry the factor $i$), and the integral is divided by $2\pi i$.

[Chi8RectangleLimit](../../../Proofs/Examples/Chi8RectangleLimit.lean) proves an unconditional $O(T^{-1/2})$ boundary bound on $[1-T,T]+i[-T,T]$, choosing a common zero-avoiding height $T\in(H,H+1)$ for each $H\ge 2$. On the fixed horizontal middle $-1\le\operatorname{Re}s\le 2$, the moving-disk divisor mass and separation give a bare logarithmic derivative bound $O(T^{3/2})$. On the right half of the contour, the completed derivative includes the conductor term $\tfrac12\log 8$ and the Gamma logarithmic derivative; the latter is $O(\sqrt T)$. In $\operatorname{Re}s\ge 2$ the bare logarithmic derivative is uniformly bounded by its absolutely convergent series. The left-side bounds follow from $D(1-s)=-D(s)$. Thus the middle contributes $O(T^{-1/2})$ on each horizontal edge after division by $s(1-s)$. The shoulders and each vertical edge have length $O(T)$ and integrand $O(T^{-3/2})$, so all four edges decay without cancellation.

With $T_n\in(n+2,n+3)$, every finite subset of strip zeros is eventually inside the rectangles. The normalized integral tends to zero in $\mathbb C$. Under the critical-line hypothesis, its real part is the finite weight sum minus $C$. Cofinality and unconditional summability then identify the unordered sum in `Chi8ZeroBudget.hasSum_weight_of_criticalLine`. The only hypothesis of that theorem is the stated critical-line condition, not the contour convergence. The Lean residue, limit, and sum declarations were checked with `#print axioms`; they depend only on `propext`, `Classical.choice`, and `Quot.sound`. This resolves the endpoint identity, not the critical-line hypothesis or a prime-race sign.
