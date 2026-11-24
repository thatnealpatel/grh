---
evidence_revision: d6e80ee6c70053b0089a7f7b1301bb767d3ab266
outcome: established
---

# Prime-only doubling of the order-three density

Let $h_3=\mathbf{1}_{[0,\log 2]}^{*3}$ in the log variable,
and set $P_3(X)=\sum_p(\log p)h_3(\log(p/X))$ for real
$X>0$, summing over rational primes only.

**Proposition to test:** Ordinary RH is equivalent to the
existence of a real $A\ge1$ such that for every real $X\ge A$,

$$P_3(2X)/(2X)\ge P_3(X)/X.$$

This is a single doubling step at each translate, without
centering, prime squares, or an additive allowance.

**Source and payoff:** This operator proposition changes the
multiplier in the [order-three comparison](../closed/zeta-order-three-prime-comparison.md)
from $\sqrt2$ to $2$. It uses the ordinary-zeta specialization
of the [prime formula](../closed/dedekind-prime-root-critical-dilation.md)
at `e29848af48be97061090219fcb2ea99e27079367`.
The [order-two budget](../open/zeta-order-two-prime-comparison.md)
at `9328b646effbe6e2cc0559c62e40521bab600b48` supplies an
alternative weighted moment. None of these asserts the new
comparison. It would characterize ordinary RH by an eventual
monotone chain along doubling from every large starting point.

**Discriminating test:** Restore the signs in $2P_3(X)-P_3(2X)$,
including the pole, removed squares, and higher powers. Write
$r=\sqrt2$, $\Phi(s)=(2^s-1)/s$, and $k=\Phi(1/2)$.
On RH, bound the all-zero oscillation for $2-2^\rho$ in units
of $\sqrt X k^3$ against $(2-r)/2$. In particular, verify a
rigorous low-ordinate exclusion (not just a located zero),
then test the exact inverse-square-total bound using
$C=2+\gamma_E-\log(4\pi)$, or use the weighted moment if
needed. Check the PNT remainder on the square scale. For the
converse, iterate the inequality at each real starting point,
use the unconditional density limit, and test the resulting
nonnegative centered Mellin tail: Its endpoint correction,
pole at one, prime-power remainder, real-axis regularity, and
visibility of nonreal zero poles to the right of $1/2$.

## Adjudication

**Yes.** On RH the square terms removed from the Euler sum give a
larger margin than the entire zero oscillation for this multiplier.
Conversely, the doubling chain from *each* large starting point
bounds the unnormalized prime sum by its main term at that point.

### The forward sign

Before any comparison, lines 72–86 of the prime formula cited above,
specialized to the rational field and $m=3$, give on RH the full
prime-power sum as $X-\sum_\rho X^\rho\Phi(\rho)^3+O(X^{1/4})$.
Here $\Phi(1)=1$, and the zero sum includes both signs and all
multiplicities. The cubic transform is integrable on the shifted
vertical at $1/4$ and kills the zero-avoiding horizontal edges.
To recover $P_3$ one must subtract the powers with $j\ge2$, each
weighted by $\log p$, not $j\log p$. For squares, integrate the PNT
$\vartheta(y)=y+o(y)$ at $y=\sqrt X v$ against $h_3(2\log v)$.
Its bounded variation on $[1,\sqrt8]$ and the uniform $o(\sqrt X)$
on this fixed rescaled interval give $\sqrt X\,k^3/2+o(\sqrt X)$:
The integral in $dv$ is $\tfrac12\int h_3(t)e^{t/2}dt=k^3/2$.
For higher powers, $p\le(8X)^{1/3}$, $j\ll\log(2X)$, and the
bounded spline costs in total $O(X^{1/3}\log^2(2X))$.
Thus the pole cancels, but the squares do **not** cancel:

$$\frac{2P_3(X)-P_3(2X)}{\sqrt X\,k^3}
=-\frac{2-r}{2}-\sum_\rho(2-2^\rho)(\Phi(\rho)/k)^3
 X^{i\Im\rho}+o(1).$$

By the genus-one product calculation at the evidence revision,
lines 49–61 of the order-three card, $C=2+\gamma_E-\log(4\pi)$
is $\sum_\rho 1/(\rho(1-\rho))$, hence $\sum_\rho|\rho|^{-2}$
on RH. The count below gives $|\rho|>14$. Since $|2^\rho|=r$,
the absolute sum is bounded uniformly in $X$ by

$$U=(2+r)((1+r)/k)^3 C/14.$$

At 128 bits, FLINT real balls with $r=\sqrt2$,
$(1+r)/k=(3+2r)/2$, and its constants for $\gamma_E$ and $\pi$
gave $0.27879698<U<0.27879699$ and $(2-r)/2-U>0.01409623$.
The real-variable $o(1)$ tends to zero within this gap. This proves
eventual strict doubling on RH, not merely a sign on a subsequence.

### Certifying the low-ordinate exclusion

Count zeros in the rectangle $[-1,2]+i[0,14]$ by the argument of
$\xi(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)/2$. It is positive
on the bottom: Use the Euler product, positivity of the paired eta
series on $(0,1)$ with $1-2^{1-s}<0$, continuity at the canceled
poles (where $\xi(0)=\xi(1)=1/2$), and reflection. On the right
edge $\Re\zeta>0$ since $\sum_{n\ge2}n^{-2}<1$. We independently
checked $\Re\zeta>0$ all along the top from $2+14i$ to $1/2+14i$
as follows, without a first-zero table.

Take $N=256$, $s=\sigma+14i$, and use Euler–Maclaurin through $B_2$:

$$T(s)=\sum_{n=1}^{N-1} n^{-s}
  + N^{-s}\left(\frac{N}{s-1}+\frac12+\frac{s}{12N}\right).$$

The periodic second Bernoulli polynomial has modulus at most $1/6$,
so $|\zeta(s)-T(s)|\le |s(s+1)|N^{-1-\sigma}/(12(1+\sigma))$
throughout $1/2\le\sigma\le2$. This is less than $1/200$, since
both factors in $|s(s+1)|$ are less than $15$. To reproduce the
strict lower bound for $\Re T$, use FLINT 3.3.1 balls at 128 bits:

1. For $0\le j<12288$, take $\sigma$ with exact dyadic center
   $(8193+2j)/16384$ and radius $1/16384$. These intervals cover
   the closed segment with no gaps.
2. Initialize the real sum with the terms
   $\exp(-\sigma\log n)\cos(14\log n)$, $1\le n<256$.
   Add the real part of the displayed correction, evaluating
   $N^{-s}=\exp(-s\log N)$ in complex balls. Every resulting
   interval was strictly above $1/200$. This tests enclosures
   over the segments, not just their centers.
3. With the branch of $\log\Gamma$ real on the positive axis,
   evaluate $(\Im\log\Gamma(1/4+7i)-7\log\pi)/\pi$ by `acb_lgamma`
   and real-ball operations. The result lies in $(-0.568,-0.567)$;
   denote the numerator by $\theta$.

Follow the right edge upwards, then the top leftwards to the midpoint.
The continuous terminal argument of $\zeta$ is in $(-\pi/2,\pi/2)$
by the two positivity checks. The arguments of $s$ and $s-1$ started
at zero and now sum to $\pi$; the gamma and pi factors contribute
$\theta$. By $\xi(1-\bar s)=\overline{\xi(s)}$, the remaining
half of the contour above the real axis contributes the same change
of argument. Hence the zero count is the nonnegative integer
$1+\theta/\pi+\arg\zeta(1/2+14i)/\pi<1$. There are no zeros on
the boundary or inside. Conjugation covers negative ordinates.

### The converse uses a different nonnegative tail

Unconditionally, partial summation at scale $p=Xv$ gives
$P_3(X)/X\to\int h_3(t)e^t dt=1$ by PNT. For each fixed real
$X\ge A$, iteration of the assumed inequality makes the densities
at $2^nX$ nondecreasing toward $1$. In particular $H(X)=X-P_3(X)$
is nonnegative on the entire tail, not just on one dyadic sequence.

Let $Q(s)=\sum_p(\log p)p^{-s}$ and $R(s)=\sum_{j\ge2}Q(js)$.
The latter converges normally on $\Re s>1/2$ by comparison, for
$\Re s\ge\sigma>1/2$, with $\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$.
For $\Re s>1$, the Euler product and the full Mellin transform of
a prime spline, $p^{-s}\Phi(s)^3$, give

$$\int_A^\infty H(X)X^{-s-1}dX
=\frac{A^{1-s}}{s-1}+\Phi(s)^3\left(\frac{\zeta'}{\zeta}(s)+R(s)\right)
 +\int_0^A P_3(X)X^{-s-1}dX.$$

The endpoint integral is entire: On this bounded interval $P_3$
has only finitely many contributing primes and vanishes near zero.
The residues at one cancel since $\Phi(1)^3=1$. The continuation
is regular at every real $s>1/2$ by eta and the Euler product. Each
zero strictly to the right of the critical line would give a pole
since $|2^s|>1$ there, so $\Phi(s)\ne0$.

If the nonnegative tail had convergence abscissa $b>1/2$, its
continuation would be regular in a disk about $b$. Choose $u=b+\epsilon$
so close that the Taylor expansion at $u$ reaches $b-\epsilon$.
Its coefficients in $u-s$ are integrals against
$X^{-u-1}(\log X)^j/j!$, all nonnegative since $A\ge1$.
Monotone convergence would give a finite defining integral at
$b-\epsilon$, contradicting the abscissa. Thus the integral is
holomorphic on $\Re s>1/2$ and excludes every such zero pole.
Reflection gives RH.

The criterion is for rational primes, order three, and every large
real starting point. It neither establishes the inequality without RH
nor asserts monotonicity between successive doubling steps. The earlier
centered comparison and the separate order-two obstruction are unchanged.
