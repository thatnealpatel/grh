---
evidence_revision: e97a8a47fbd771a5d2d069a46a8792a4b0c0f902
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
