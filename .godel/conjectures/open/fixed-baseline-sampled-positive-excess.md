---
evidence_revision: 50cd94ded63eeaaaaecd31993cb28f211002139f
---

# Recover the zero supremum from sampled positive excess

**Proposition to test:** Fix an integer $q\ge2$, any
integer $m\ge8$, and any fixed integer $B\ge1$. Let
$M=10^{15}$, $a=\log 2$, $h_m=\mathbf1_{[0,a]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and $t_p=\log(p/X)$. Put
$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
  [Mh_m(t_p)+\mathbf1_{p\equiv1\bmod q}k_m(t_p)].$$
Let $\Theta_q$ be the supremum of real parts of all
nontrivial zeros of the primitive inducers modulo $q$,
including zeta. For integer $N\ge2$ set
$$S(N)=\sum_{N\le n<2N}\max(0,W_{q,m}(n^B)-Mn^B).$$
Then, with natural logs,
$$\Theta_q=\max\left\{\tfrac12,\frac1B\left(
  \limsup_{N\to\infty}\frac{\log(1+S(N))}{\log N}-1
  \right)\right\}.$$
Moreover, if $\Theta_q>1/2$, for every $\epsilon>0$
there are arbitrarily large $N$ with at least
$N^{1-\epsilon}$ consecutive integers $n\in[N,2N)$
each satisfying $W_{q,m}(n^B)-Mn^B\ge(n^B)^{\Theta_q-\epsilon}$.
There is no zero-line, attainment, separation, or
independence premise.

**Source and payoff:** The sampled-sign landing at the
evidence pin gives the one-sided Mellin barrier and
the zero-bound derivative estimate. The exact windows
and residues are at
`f5fbeb09e9b972565848e25ac295f3341a537afd`.
The proposed exponent measures the extent of zero
protrusion, not merely its presence. It does not ask
for an uncapped equality at $\Theta_q=1/2$, positive
density, or eventually good blocks.

**Discriminating test:** With $H=MX-W_{q,m}$, audit the
Mellin residue signs and visibility and the contour
estimate at $m=8$ without the forward choice of order.
For $\Theta_q>1/2$, seek arbitrarily late peaks of
$-H$ above $Y^{\Theta_q-\eta}$ by contraposition. Test
whether the derivative bound, or Chebyshev at
$\Theta_q=1$, preserves half the peak across a right
interval of length $cY^{1-2\eta}$. Count consecutive
powers there using $N=\lceil Y^{1/B}\rceil$, including
rounding, the $2N$ endpoint, and $\eta<1/(2B)$. Check
that the losses can be absorbed for the run bound and
that the upper limsup follows even on the line.
