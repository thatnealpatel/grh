---
evidence_revision: 8e0f45864088cc246d66567c2b83ccb84f553fd0
---

# Extract rightmost zero ordinates from signed samples

**Proposition to test:** Fix integers $q\ge2$, $m\ge8$,
and $B\ge1$. Write $M=10^{15}$, $a=\log 2$,
$h_m=\mathbf1_{[0,a]}^{*m}$, $k_m=4h_m^{(4)}-5h_m''+h_m$,
and $t_p=\log(p/X)$. Use the same signed deficit
$$H(X)=MX-\sum_{p\nmid q}(\log p)
  [Mh_m(t_p)+\mathbf1_{p\equiv1\bmod q}k_m(t_p)].$$
Let $\theta=\Theta_q$ be the supremum of the real parts
of the nontrivial zeros of the primitive inducers of
characters modulo $q$, including zeta. For each real $t$
put $z=\theta+it$, $d=\varphi(q)$, and
$S(z)=\sum_{\chi\bmod q}\operatorname{mult}_{\chi^*}(z)$,
with multiplicity zero at nonzeros, including the zeta
pole at one. Write $\Phi(s)=\int_0^a e^{sv}dv$ and
$Q(s)=(4s^2-1)(s^2-1)$. The claimed ordinary limit is
$$\lim_{N\to\infty}\frac1{\log N}
  \sum_{n\le N}H(n^B)n^{-Bz}/n
 =\Phi(z)^m[M\operatorname{mult}_\zeta(z)+Q(z)S(z)/d]
  +\mathbf1_{\theta=1/2,\ t=0}(M/2)\Phi(1/2)^m.$$
At every nonreal edge point the coefficient should
separately determine the zeta multiplicity and $S$.
The same visibility is sought at real edge zeros when
$\theta>1/2$. The center at $\theta=1/2$ is blind to
central nonprincipal multiplicities. No attainment or
zero-spacing hypothesis is imposed.

**Source and payoff:** The evidence landing recovers
$\theta$ from positive sampled excess. The window and
deficit residues are from the fixed-baseline criterion
at `f5fbeb09e9b972565848e25ac295f3341a537afd`.
This is a new use of signed samples, not an inference
of ordinates from the positive excess alone. It seeks
aggregate, not individual, nonprincipal multiplicities.
It does not seek deeper zeros or a finite algorithm.

**Discriminating test:** At the worst order $m=8$,
reconstruct the full primitive zero expansion by a
shift to $\Re s=-1/2$. Check residue signs, horizontal
and vertical bounds, and absolute coefficient mass.
Restore the imprimitive exclusions and remove squares
using fixed-class PNT on exactly $b^2=1$ for the
identity term, checking both square constants. Test
whether dominated convergence removes all left zeros,
even with no gap, and whether harmonic sums of the
logarithmic phases isolate exactly $t$ for every fixed
$B$. Check extraction on the entire nonreal locus
$\Im Q=0$ by unconditional zeta nonvanishing there.
