---
evidence_revision: a684299f2b54e602be826969b35b7c1f30742700
outcome: refuted
---

# Strict inclusion of the rational one-prime closed cut ranges

Specialize (11.1.2.6) to $F=\mathbb Q$, the trivial compact isotype, $S=\{\infty\}$, and insertion of one prime $p$ into the empty restriction set. For $s\ge2$, the claim is strict inclusion of the closed images after the lower or annular position cutoff along a subsequence of cutoff sizes.

**Refuted:** Both closed ranges are equal at every $\Lambda>0$. This is not a statement about the uncut ranges.

Write $x=\log|g|$, $L=\log p$, and $D u=u-u(\cdot+L)$ on raw profiles. For every represented radial class-theta profile $u$, the sum $c_N=\sum_{j=0}^{N-1}u(\cdot+jL)$ is again represented. Then $Dc_N=u-u(\cdot+NL)$, and the last term tends to zero in the cut polynomially weighted norm on any measurable window bounded below. The reverse inclusion holds on generators. The inputs vary with the cutoff and approximation; taking strong limits of cutoffs does not recover an uncut preimage.

[Lean](../../../Proofs/Theorems/RationalThetaRadialCut.lean), `Masullo.rationalThetaRadialPrimeDifferenceCut_haar_closure`, checks the equality in normalized class Haar $L^2$ for all $s\ge0$. Its `_haar_ae` representative identifies the actual inverse-uniformizer difference. The [identification with the printed trivial isotype](../../obligations/trace-cut-range-q.md) uses the manuscript's theta-image dictionary and local unit averaging. No equality of kernel traces follows.
