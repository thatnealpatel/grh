---
evidence_revision: a684299f2b54e602be826969b35b7c1f30742700
outcome: refuted
---

# The Boolean shell on the standard lift does not have the orbital circle trace

In the rational zero-line model, let $L=\log p$ and use the lift $b\otimes\mathbf1_{\widehat{\mathbb Z}}$. The proposed identification is that applying the signed first source mask to this lift, then smooth compact log convolution $A_f$ and compact smooth output cutoff $M_\rho$, yields the circle trace $L\sum_{j\in\mathbb Z}f(jL)$ for every $f\in C_c^\infty((0,\infty))$. One may even fix $\int\rho=L$.

**Refuted for this model:** A nonnegative bump about $2L$ missing all other lattice points, with $f(2L)>0$, gives zero for the signed shell and a positive circle trace. The discrepancy does not depend on the sign assigned to the shell.

The [unit-mask calculation](../../../Proofs/Theorems/RationalThetaPrimeMask.lean) is Lean-checked. Its complement selects the $p$-divisible integers, hence the manuscript sign gives $-S_L$ on the profile, where $S_Lu(x)=u(x+L)$. The remaining comparison is on paper: The kernel of $-M_\rho A_f S_L$ against $dy$ is $-\rho(x)f(x+L-y)$. It is smooth and compactly supported, and conjugation by the square root of the polynomial weight leaves its diagonal unchanged. Its trace is $-f(L)\int\rho$. In the dense zero-line ring-transition model, putting $Q_Y$ on the right does not change this limit as $Y\to\infty$: The unbanded operator is trace class and the orthogonal projections converge strongly to the identity.

This tests a mask on the **testing argument**, not the source variable of the actual indented quotient kernel in (11.3.2.3). A principal translate can also change a masked representative, but need not lie in this standard presentation. Neither argument identifies the indented kernel. The [orbital circle comparison](../../obligations/trace-orbital-q.md) and the [valuation-layer model](rational-valuation-layer-cut-trace.md) are alternatives, not proofs of that identification.
