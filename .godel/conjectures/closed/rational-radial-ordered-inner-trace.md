---
evidence_revision: 022676f32fb32118354a025cb57b7c48d5dac9cf
outcome: parked
---

# The ordered radial theta trace counts interior zeros

Over $\mathbb Q$ in the trivial compact isotype, fix integer $r\ge1$ and use $L^2(e^{2\alpha|x|}(1+x^2)^r dx)$. For almost every $0<\alpha<1/2$ and every $f\in C_c^\infty(\mathbb R\setminus\{0\})$, the proposed identity is
$$
\lim_{\rho\uparrow1}\lim_{B\to\infty}\operatorname{Tr}(M_\rho P A_f Q_B)
=-\sum_{|\Re z-1/2|<\alpha} m_z\int f(x)e^{(z-1/2)x}\,dx.
$$
Here $z$ runs over distinct nontrivial zeta zeros with orders $m_z$, $P$ is the actual theta-closure projection, $Q_B$ the theta band projections, $A_f$ convolution, and $M_\rho$ the position cutoff.

**Parked:** The proposed inner-contour computation is not a checked identification of the ordered trace. Even if correct, moving the contour outward adds the omitted zeros, not an independently vanishing remainder.

The construction (`e8913f9bf7e2319247a1eb0c4354ee4bc56945a0`) used a smoothed zeta multiplier, inverted it on each strip edge, and spliced the inverses on opposite half-lines. The challenge (`6181c705710057f8aafc0a7da657fb04b0d8695f`) separated inner winding from exterior normalization: A strip-invertible factor can preserve the range while changing outer winding. This is not a counterexample for zeta. The [spectral strip estimates](../../obligations/trace-spectral-strip-q.md) and Lean band exhaustion are inputs, not a Lean proof of the display. Reopen with an independently verifiable trace-class comparison in this operator order that also advances the [global-to-local comparison](../../obligations/trace-to-zeros.md).
