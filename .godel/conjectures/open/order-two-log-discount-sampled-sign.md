---
evidence_revision: 6596fa6e00f481978d7f2792eec2b3dde99a8a29
---

# Test the order-two sign with an identity-class discount

**Proposition to test:** With natural logarithms, put
$h=\mathbf1_{[0,\log 2]}*\mathbf1_{[0,\log 2]}$ and
$K(s)=((2^s-1)/s)^2$, with the removable value at zero. For
$q\ge2$ let $d=\varphi(q)$, $L_q=\lceil\log(2q)\rceil$, and
$\delta_q=1/(\sqrt2 A L_q)$. Define
$$H(X)=(1-\delta_q/d)X-\sum_{p\nmid q}(\log p)
 (1-\delta_q\mathbf1_{p\equiv1\bmod q})h(\log(p/X)).$$
Do there exist an absolute positive integer $A$ and absolute
$X_0\ge2$, $c>0$ such that, for all integers $q\ge2$, $B\ge1$,
joint GRH for the primitive inducers modulo $q$, including
zeta, is equivalent to $H(n^B)\ge0$ for every positive
integer $n$ with $n^B\ge X_0$? Under that fixed-$q$ hypothesis,
require $H(X)\ge c\sqrt X$ on all real $X\ge X_0$. Conversely,
require only an arbitrary eventual tail of sampled signs.

**Source and payoff:** The pinned [triangular divisor card](../closed/triangular-weighted-character-zero-divisors.md)
gives the order-two expansion and a split-cell strip argument
for exact-value recovery. The [prior sign card](../closed/fixed-baseline-polynomial-sample-sign.md)
at `50cd94ded63eeaaaaecd31993cb28f211002139f` gives a
Landau obstruction for a different window, growing order,
and modulus-dependent onset. This is a proposed use of the
triangular expansion for one-sidedness, not a claim of either
landing. No monotonicity or named zero recovery is required.

**Discriminating test:** Split off the ordinary zeta deficit
and nonnegative bad-prime correction. Check the ordinary
prime-square constant, derive the inverse-square zero total
from the completed zeta product, and certify the margin
against the full zero-mass bound. Bound the smoothed identity
class discrepancy by $C\sqrt X\log(2q)$ with absolute $C$:
Check the primitive completed log-derivative difference,
left contour, trivial residue, imprimitive factors, and
prime powers under joint GRH for this $q$ only. Choose $A$
after this bound and check the uniform onset.

For the reverse direction, compute all grouped zero residues
and check their visibility and sign at real zeros without
GRH. Use the split-cell sub-first moment bound to continue
the same positive-tail sample Dirichlet series one strip at
a time. Check whether Landau excludes its real abscissa in
each strip and hence excludes every visible pole there,
including intermediate cut issues and abscissa $-\infty$.
