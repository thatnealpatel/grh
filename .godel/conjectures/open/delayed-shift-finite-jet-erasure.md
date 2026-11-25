---
evidence_revision: 737e540e22a06a7fc38fcc573f4d9cba0c8a7146
---

# Can delayed shifts erase any finite Mellin jet section while preserving the prime window?

**Conjecture (paper argument, not Lean-checked):** In the notation of the
[signed Möbius-tail conjecture](rational-signed-mobius-tail-residual.md),
put $q=(Xt)*\check\phi$, where $(Xt)(x)=xt(x)$, and $k_N=R_Nq$.
Fix a compact sampling window $W=[-L-\eta,-L+\eta]$ and finitely many
interior shifted zeros $w_j$ with positive jet counts $c_j$, closed
under conjugation with equal counts on conjugate pairs. There exists a
real finite sum of log-integer shifts $\widetilde R$ that retains every
coefficient of $R_N$ through $N$, with the following properties:

- $\widetilde Rt$ is still in the genuine theta closure.
- $\widetilde Rq=k_N$ throughout $W$.
- $M_{\widetilde Rq}^{(b)}(w_j)=0$ for $0\le b<c_j$, where
  $M_h(z)=\int h(x)e^{zx}\,dx$. Hence the orthogonal projection of
  $\widetilde Rq$ onto the span of those jet representers is zero in
  the original strip weight.

**Proposed construction:** Take $a=K\log 2>\max(\log N,L+\eta+2d)$
with $K$ integral. In the convention $\tau_s h(x)=h(x-s)$, set
$$
\widetilde R=\prod_j(1-e^{aw_j}\tau_{-a})^{c_j}R_N.
$$
Conjugate factors pair to give real coefficients. The constant term
in the product is the identity; every other term delays by at least
$a$. Since $\operatorname{supp}k_N\subset(-\infty,2d]$, none of those
terms reaches $W$. Their indices $2^{K\ell}n$ for $\ell\ge1$ exceed
$N$. The theta assertion uses only translation invariance. On the
Mellin side the product contributes $(1-e^{-a(z-w_j)})^{c_j}$ for
each $j$, giving the requested order of vanishing without dividing by
any jet value or assuming the zeros are simple.

**Discriminating test and scope:** At $L=\log 5$, $d=1/32$, and $N=8$,
the unchanged center sample is $-C(0)\log(5)/\sqrt5\ne0$. Compare
with the zero operator, which has the same selected jets but zero
sample. Thus no function of those jets alone can recover the sample
on a shift family containing both operators. The delayed coefficients
are not the prescribed Möbius coefficients beyond $N$ and need not
have controlled norms. This does not settle a comparison restricted
to the original Möbius operators, erase the full complementary
projection, or give a residual bound.
