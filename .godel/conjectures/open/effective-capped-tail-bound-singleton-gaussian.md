---
evidence_revision: a36dcd32e6e687da76b7ea30fc9eb0e2aa48b392
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

The accepted Gaussian spectral evidence identifies the actual convolution-first trace with the capped jet sum and establishes qualitative trace-classness, absolute convergence, and a qualitative Jensen-type zero count. It does not yet supply an explicit all-height constant \(C\), a certified complete zero list through a chosen height, rigorous Fourier-transform enclosures for the prescribed bump, or a lower bound for the finite head. The cited family-density and general Hecke zero estimates do not provide these missing individual inputs for this fixed quartic character.

The concrete test is to certify \(\|b_0^{(k)}\|_1\) for one or more \(k\ge3\), derive an explicit all-height bound \(M(R)\le C(1+R^2)\) including the small-height range, compute and enclose every relevant zero through an explicit \(T\), and evaluate the finite Fourier sum with rigorous error control. The claim remains open unless these data yield \(|\widetilde S_T|>\varepsilon+E_T\). A finite numerical scan without a complete zero certificate and a universal tail estimate is insufficient.
