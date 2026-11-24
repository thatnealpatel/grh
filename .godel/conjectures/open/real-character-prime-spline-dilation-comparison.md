---
evidence_revision: d3675071daa1e1afbff4107024f1a9943855a43b
---

# Two-scale prime spline comparisons for fixed real characters

Fix any primitive nonprincipal real Dirichlet character
$\chi$, without a real-axis nonvanishing hypothesis. Let
$h_m=\mathbf{1}_{[0,\log 2]}^{*m}$ under ordinary real
convolution, and for $X>0$ set

$$W_m(X)=\sum_p\chi(p)\log p\,h_m(\log(p/X)).$$

For each integer $j\ge1$ put $a_j=1/2+1/(j+2)$,
$c_j=2^{a_j}$, and $V_{j,m}(X)=c_jW_m(X)-W_m(2X)$.

**Proposition to test:** The following are equivalent:

1. Every nontrivial zero of $L(s,\chi)$ has real part
   $1/2$.
2. For every $j\ge1$ there are an integer $m\ge2$ and
   $X_0\ge1$ such that $V_{j,m}(X)\le0$ for all real
   $X\ge X_0$.

The order and threshold may depend on $\chi,j$, and the
threshold on the order. There is no sign requirement on
$W_m$ itself and no uniformity in $j$ or the conductor.

**Source and payoff:** This operator-proposed comparison
replaces the one-scale sign in the pinned
[fixed-character criterion](../closed/real-character-prime-spline-eventual-sign.md),
whose converse assumes real-axis nonvanishing. Bob's
[endpoint estimate (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789` is a
magnitude bound under a different premise, not this
comparison. The question is whether comparing two true
local prime sums can encode zero location without the
extra real-axis premise. Neither landing asserts this
repair.

**Discriminating test:** On the critical-line hypothesis,
compute the square and central-zero bias after dilation,
and test whether the noncentral terms can be made smaller
than the surviving margin for each fixed $j$ by a fixed
order. In the reverse direction, compute the tail Mellin
transform of $-V_{j,m}$ with its finite endpoint terms.
Test whether the multiplier $(c_j-2^s)K(s)^m$, where
$K(s)=(2^s-1)/s$, can permit a real zero above $a_j$ to
be the first singularity of a nonnegative tail. Separate
the domain of integral convergence from meromorphic
continuation, locate possible complex cancellations on the
boundary, and test the passage from each $a_j$ to $1/2$
without any uniformity in the orders.
