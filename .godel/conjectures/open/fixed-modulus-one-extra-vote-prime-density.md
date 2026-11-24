---
evidence_revision: a08d9dfe9adc87383319f9e970b60bd443cfcca2
---

# One extra vote per reduced class and fixed-modulus GRH

Fix any integer $q\ge2$ and let $G=(\mathbb Z/q\mathbb Z)^*$.
For a fixed integer $m\ge4$ put
$h_m=\mathbf 1_{[0,\log 2]}^{*m}$, using ordinary real
convolution. For real $X>0$ write

$$P_a(X)=\sum_{p\equiv a\bmod q}\log(p)h_m(\log(p/X)),
\qquad P(X)=\sum_{a\in G}P_a(X).$$

**Proposition to test:** All nontrivial zeros of every
primitive Dirichlet $L$-function inducing a character
modulo $q$, including $\zeta$, lie on $\Re s=1/2$ if and
only if there exist integers $m\ge4$, $M\ge1$, and a
real $A\ge1$ such that $(MP+P_a)/X$ is nondecreasing on
$[A,\infty)$ for every $a\in G$. The same $m,M,A$ are
used for all classes and may depend on $q$, not on $X$.
Test also whether one can always take $m=4$ in the forward
implication.

**Source and payoff:** This operator proposal uses the
[quartic prime-only criterion](../closed/zeta-prime-only-continuous-density.md)
at the evidence revision. For comparison, the
[critical dilation criterion](../closed/critical-dilation-prime-square-allowance.md)
at `a954fef4e3a0db9c2124fbeb457b881886b18b47` uses a
signed single-character count and a prime-square allowance.
Neither landing asserts the simultaneous comparison. The
payoff would be a joint criterion using only genuine
rational primes with coefficients $M$ and $M+1$, without
a square allowance, chosen phase, or real-axis premise.

**Discriminating test:** Center each density using its
fixed-class PNT limit. Sum the nonnegative deficits and
check whether this forces ordinary RH for the *witness*
order $m$, not just order four. With zeta RH alone,
derive a square-root bound for the total deficit and
check whether conservation gives a two-sided bound in
every class. Invert with each full character and audit
the Mellin endpoints, prime powers, inducing Euler
factors, and visibility of a real zero above the line.
For the other direction, insert $g=-h_4'-h_4$ directly
in the smoothed explicit formula. Test whether the
class terms, including central zeros and squares, have
a finite uniform-in-$X$ derivative bound in the scale
of the pinned positive margin, so that one integer
baseline works at all real arguments on a common tail.
