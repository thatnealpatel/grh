---
evidence_revision: 0310a071f9cb4685281a0d9fde9f1ce23f5d774f
---

# Can Lean exclude right-hand poles from a translated residual bound?

**Formalization target:** Let the distinct $w_j\in\mathbb C$ form a locally
finite set with $\Re w_j\le b$, let $\sum_j|a_j|<\infty$, and set
$F(L)=\sum_j a_j e^{Lw_j}$ for $L\ge0$. For any real $\alpha$, prove that
$F(L)=O(e^{\alpha L})$ as $L\to\infty$ forces $a_j=0$ whenever
$\Re w_j>\alpha$. This is a paper implication awaiting a Lean proof, not
an open claim about the zeros or a proof of the growth bound.

**Discriminating test:** First prove the continuation-to-coefficient
endpoint. Suppose $G$ is holomorphic on $\Re s>\alpha$ and agrees with
$\sum_j a_j/(s-w_j)$ on $\Re s>\max(b,\alpha)$. Separate one pole and show
that $(s-w_j)\sum_k a_k/(s-w_k)\to a_j$ as $s\to w_j$ through a punctured
neighborhood. Continue the equality on the half-plane with the poles
removed, then use holomorphy of $G$ at $w_j$. Next construct $G$ by the
positive-half-line Laplace integral: The tail bound gives holomorphy, and
absolute integrability on the starting half-plane justifies exchanging
sum and integral. Do not require global holomorphy of $G$.

**Checked starting points:** [`Masullo.subtractedResolvent_weight_eq_zero`](../../../Proofs/Lemmas/SubtractedResolvent.lean)
checks isolated coefficient recovery for a subtracted resolvent and a
different analyticity domain. [`Masullo.weight_eq_zero_of_zero_mass_annihilation`](../../../Proofs/Props/ZeroMassUniqueness.lean)
uses that result under exact annihilation on a whole test class, not an
exponential tail bound. [`RationalWeilWindows.lean`](../../../Proofs/Theorems/RationalWeilWindows.lean)
checks the autocorrelation transform and summability of the zero side.

**Payoff and stopping point:** For the [edge bump](../../primers/weil-complements.md),
use $w_j=\rho-1/2$ and $a_j=m_\rho\Psi_\phi(w_j)$. For a strip residual,
replace $m_\rho$ by the omitted multiplicity. Specialize first under the
hypothesis that the fixed bump sees the relevant zeros. A checked
half-plane exclusion lemma is useful in both settings. Constructing the
bump in Lean, checking signed oscillation, and identifying or estimating
a geometric trace are separate tasks.
