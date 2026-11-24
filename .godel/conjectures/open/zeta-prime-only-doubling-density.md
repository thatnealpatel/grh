---
evidence_revision: d6e80ee6c70053b0089a7f7b1301bb767d3ab266
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
The [order-two budget](zeta-order-two-prime-comparison.md)
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
