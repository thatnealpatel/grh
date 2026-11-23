---
evidence_revision: fd9b420ec415046d03028c1929d0b349ac0f7426
---

# An effective capped-tail bound for the singleton Gaussian spectral trace

Let \(\mathcal T\subset\mathbb R\) be the distinct real zeros of \(Z(t)=L(1/2+it,\bar\eta)\), let \(d_t\) be the multiplicity of \(t\), and put \(w(t)=\min(d_t,2)\) and
\[
M(R)=\sum_{t\in\mathcal T,\,|t|\le R}w(t).
\]
Assume that an explicit constant \(C\ge0\) satisfies \(M(R)\le C(1+R^2)\) for every \(R\ge0\). Let \(\mu=\mu_1(G^1)\), let \(b_0\in C_c^\infty(\mathbb R)\) be the prescribed positive-log bump, and define
\[
m(t)=\mu\int_{\mathbb R}b_0(x)e^{itx}\,dx.
\]
For every integer \(k\ge3\) and every \(T>0\), define the boundary-inclusive head
\[
S_T=\sum_{t\in\mathcal T,\,|t|\le T}w(t)m(t).
\]
Then, provided the stated all-height counting bound holds and the Fourier decay is bounded by integration by parts,
\[
\left|\sum_{t\in\mathcal T}w(t)m(t)-S_T\right|
\le |\mu|\,\|b_0^{(k)}\|_1
\left(
\frac{C(1+T^2)-M(T)}{T^k}
+\frac{2C}{k-2}T^{2-k}
\right).
\]
The zero at \(t=0\) is included in the head, and zeros with \(|t|=T\) are included in \(S_T\), not the tail.

The correction is material: The draft's alternative coefficient \(kC/(k-2)\) is not algebraically equivalent to \(2C/(k-2)\). The displayed bound above follows by applying Stieltjes summation to \(f(r)=r^{-k}\) on \((T,\infty)\), using \(M(r)\le C(1+r^2)\), and integrating the majorant by parts. The boundary term vanishes because \(k>2\). The estimate \(|m(t)|\le |\mu|\|b_0^{(k)}\|_1|t|^{-k}\) holds for \(t\ne0\).

This supplies a precise conditional analytic bridge from a quadratic capped zero-count bound and a certified derivative norm of the fixed bump to a truncation error. If a complete, rigorously enclosed zero list through height \(T\) gives a finite-head enclosure \(|S_T-\widetilde S_T|\le\varepsilon\), then \(|\widetilde S_T|>\varepsilon+E_T\), with \(E_T\) equal to the displayed tail bound, proves that the actual singleton trace is nonzero.

For the prescribed bump and $T=8192$, the [checked quartic Gaussian tail](../../../Proofs/Lemmas/QuarticGaussianTail.lean) now provides an alternative to the all-height Stieltjes route above. `Masullo.quarticGaussianTail_bound` proves summability and an absolute tail at most $425984/10^{12}$ for the concrete Gaussian Mellin transform, with both signs retained and endpoints excluded. It uses the Fourier integral **without** $\mu$. The [Gaussian singleton evaluation](../../obligations/trace-spectral-sum-qi.md) identifies the spectral normalization in ordinary mathematics, not in this Lean theorem. In the card’s units the error budget is therefore $E_{8192}=|\mu|\,425984/10^{12}$.

**Remaining test:** Enclose the inclusive, signed head with $|S_{8192}-c|\le\varepsilon$ and $|c|>\varepsilon+E_{8192}$. Account for capped orders and for any ordinates not individually enclosed. The tail estimate alone does not separate the full sum from zero; this card remains open.
