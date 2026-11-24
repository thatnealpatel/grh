---
evidence_revision: 76d66112fa30b3a9cc28d24759ac6f8fe78f9e94
---

# One positive quartic prime density and fixed-modulus GRH

Fix an integer $q\ge2$. Set $h_4=\mathbf 1_{[0,\log 2]}^{*4}$
with ordinary real convolution, and for real $X>0$ let
$$P(X)=\sum_{p\nmid q}(\log p)h_4(\log(p/X)),\qquad
P_1(X)=\sum_{p\equiv1\bmod q}(\log p)h_4(\log(p/X)).$$

**Proposition to test:** All nontrivial zeros of every
primitive Dirichlet $L$-function inducing a character
modulo $q$, including $\zeta$, lie on $\Re s=1/2$ if and
only if there exist an integer $M\ge1$ and a real $A\ge1$
such that the single real density $W(X)/X$ is nondecreasing
for all real $X\ge A$, where
$$W=(M+\sqrt 2)P-P_1.$$
The two assigned prime weights are $M+\sqrt 2-1$ in the
identity class and $M+\sqrt 2$ elsewhere, both positive.
The same formula applies when $q=2$ and only the identity
class occurs. No zero simplicity or disjointness is assumed.

**Source and payoff:** This operator proposal uses the
order-four class derivative bound of the [simultaneous criterion](../closed/fixed-modulus-one-extra-vote-prime-density.md)
at the evidence revision and the RH derivative margin of the
[quartic zeta criterion](../closed/zeta-prime-only-continuous-density.md)
at `a08d9dfe9adc87383319f9e970b60bd443cfcca2`.
Neither source asserts this criterion. The payoff is one
monitored density instead of all class comparisons, not
unconditional increase or a baseline uniform in $q$.

**Discriminating test:** Check that the strict total derivative
margin dominates the two-sided identity-class derivative
bound for some $M$. In the converse, use the fixed-modulus
PNT limit to center the nonnegative deficit on a real tail.
Without simultaneous conservation, derive its tail Mellin
transform, check the endpoint, power terms, pole at one, and
imprimitive factors, and test whether the uniform character
coefficients of the identity class and the irrational total
weight prevent pole cancellation at arbitrary coincident
zeros. Test the sign at a real zero using zeta nonvanishing,
then apply the nonnegative-tail convergence-abscissa argument
with these real poles allowed. Check holomorphy in the full
open right half of the critical strip and reflection in the
inducing primitive family.
