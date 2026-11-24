---
evidence_revision: 50cd94ded63eeaaaaecd31993cb28f211002139f
outcome: established
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

## Adjudication

**The capped identity and the consecutive-run bound both hold.** Write
$H(X)=MX-W_{q,m}(X)$ and $\theta=\Theta_q$. All constants below may
depend on the fixed parameters, including the exponent slack.

### Which pinned estimates apply

The polynomial-sample-sign card at the evidence revision uses its
prescribed order for the forward sign (lines 49–55). Its two reverse
estimates (lines 59–106 and 108–153) apply at *each* fixed $m\ge8$:

* A tail bound $H(X)\ge-KX^b$, $K\ge0$, $b<1$, forces
  $\theta\le\max(b,1/2)$. Indeed, for $\Phi=(2^s-1)/s$ and
  $Q=(4s^2-1)(s^2-1)$ the deficit transform in the variable-order
  card (lines 144–183 at the window pin above) is regular at one:
  $\Phi(1)=1$ and $Q(1)=0$ cancel the main pole. Prime-power
  corrections are regular to the right of $1/2$. A family zero there
  contributes residue $\Phi(\rho)^m(Mm_\zeta+Q(\rho)T/\varphi(q))$,
  where $T>0$ sums character multiplicities. The prefactor never
  vanishes. At a real zero the eta series excludes a zeta zero, and
  $Q<0$, so the residue is negative. Nonreal cancellation requires a
  zeta zero $s=x+it$ with $t^2=x^2-5/8$ from $\Im Q=0$. There
  $|s-1|^2\le3/8$ and $|s|/x<\sqrt2$; Euler summation gives
  $|(s-1)\zeta(s)-1|\le |s-1|(1+|s|/x)/2<1$. Thus every such pole
  is visible. Adding $KX^b$ creates no pole right of $\max(b,1/2)$.
  The resulting nonnegative tail transform cannot have its real
  convergence abscissa there: A negative residue contradicts
  nonnegativity from the right, and at a regular point the Taylor
  series of nonnegative log moments gives convergence to the left
  by monotone convergence. Holomorphy there proves the bound.
* If $\theta<u<1$ with $u>1/2$, then $H'=O(X^{u-1})$. The windows
  are compactly supported and $k_m\in C^{m-6}$, so differentiation
  holds even at knots. For $XW'$ the multiplier is $sK_f(s)$, of
  worst decay $O_m((1+|t|)^{5-m})$, already cubic at order eight.
  In the pinned Hadamard comparison the real parts at $2+it$ minus
  those at $-1+it$ bound $\sum_\rho (1+(t-\Im\rho)^2)^{-1}$ by
  $O_q(\log(2+|t|))$. The fixed horizontal gap $u-\theta>0$ thus
  controls the reciprocal differences from $2+it$ throughout the
  shift. No zero spacing is needed. The shifted vertical contributes
  $O(X^u)$; the only residue after averaging is $MX$. Deleting higher
  prime powers costs $O_m(\sqrt X\log^2(2X))=O(X^u)$. Subtract and
  divide by $X$. Without a gap, the bounded windows and their first
  derivatives with Chebyshev give $H=O(X)$ and $H'=O(1)$.

### From an excursion to consecutive indices

Suppose $\theta>1/2$. Take $\eta>0$ with $\theta-\eta>1/2$,
$2B\eta<1$, and, if $\theta<1$, $\theta+\eta<1$. There are arbitrarily
large real $Y$ with $-H(Y)>Y^{\theta-\eta}$: Otherwise the first
estimate with $K=1$ gives $\theta\le\theta-\eta$. This tests the
supremum without needing a pole at the supremum.

On $[Y,2Y]$ the second estimate with $u=\theta+\eta$, or the
unconditional bound if $\theta=1$, gives
$|H'|\le L Y^{\theta+\eta-1}$ with $L$ independent of $Y$. Put
$\Delta=cY^{1-2\eta}$ with $c=1/(2+2L)$. Integration costs at most
$LcY^{\theta-\eta}$, so the excess is at least $Y^{\theta-\eta}/2$
throughout $[Y,Y+\Delta]$.

Put $x=Y^{1/B}$, $z=(Y+\Delta)^{1/B}$, and $N=\lceil x\rceil$.
Then $z<2x\le2N$, and $\Delta=z^B-x^B\le Bz^{B-1}(z-x)$ gives
$z-x\gg x^{1-2B\eta}$. Consequently the integers $N$ through
$\lfloor z\rfloor$ form a single run in $[N,2N)$ of length at least
$z-x-1\gg N^{1-2B\eta}$ for large $Y$. Their powers are between
$Y$ and $2Y$, so each excess is $\gg(n^B)^{\theta-\eta}$. For a
given $\epsilon>0$ choose also $2B\eta<\epsilon$ and $\eta<\epsilon$.
Both constants are absorbed by the strict exponent gaps as $N$ grows.
This proves the stated run bound, not a density assertion.

### Recovering the exponent

Along those blocks the unweighted sum is
$S(N)\gg N^{1-2B\eta+B(\theta-\eta)}$. Taking its logarithmic
limsup with the stated $1+$ convention, then letting $\eta\downarrow0$,
gives the lower exponent $1+B\theta$ for $\theta>1/2$. Conversely,
for $\theta<1$, integrating the derivative bound gives
$|H(X)|\ll X^{\theta+\eta}$ for arbitrarily small $\eta>0$; for
$\theta=1$ use $|H(X)|\ll X$. Summing over $N$ indices with
$n^B<(2N)^B$ gives upper exponent $1+B\theta$ in all cases.
Finally $1/2\le\theta\le1$ by the critical strip, zeta zero existence,
and reflection. At $\theta=1/2$ the upper bound alone proves the
capped identity. At the prescribed forward order the pinned strict
sign on joint GRH even makes $S(N)$ eventually zero, so an uncapped
identity there is not justified. No positive derivative margin at
arbitrary order or bound on the first good block has been used.
