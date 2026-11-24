---
evidence_revision: 69d5d30993da9b1de65d9d7930f06a86664cfa0b
---

# Test explicit constants for the discounted triangular sign

Let $h=\mathbf1_{[0,\log 2]}*\mathbf1_{[0,\log 2]}$ and
$K(s)=((2^s-1)/s)^2$ with the removable value at zero.
For integers $q\ge2$ let $d=\varphi(q)$,
$L_q=\lceil\log(2q)\rceil$, and
$\delta_q=1/(\sqrt2\,10^6 L_q)$. Use natural logarithms and
$$H(X)=(1-\delta_q/d)X-\sum_{p\nmid q}(\log p)
(1-\delta_q\mathbf1_{p\equiv1\bmod q})h(\log(p/X)).$$

**Proposition to test:** For every $q\ge2$, joint GRH for the
primitive inducers modulo $q$, including zeta, implies
$H(X)\ge\sqrt X/25$ for every real $X\ge2^{512}$. For each
fixed integer $B\ge1$, joint GRH for this family is equivalent
to $H(n^B)\ge0$ for every positive integer $n$ with
$n^B\ge2^{512}$.

**Source and payoff:** The [discounted sign criterion](../closed/order-two-log-discount-sampled-sign.md)
at the evidence revision proves an existential forward onset
and a qualitative all-$B$ converse. The [triangular divisor card](../closed/triangular-weighted-character-zero-divisors.md)
at `6596fa6e00f481978d7f2792eec2b3dde99a8a29` supplies
the compact triangular shift. The requested strengthening
fixes the discount, threshold, and margin, with no unspecified
forward size constants and no finite-test interpretation.

**Discriminating test:** Derive exact full Mangoldt identities
with kernels $K$ and $K(s/2)/2$ by sending left lines to
minus infinity after their horizontal edges vanish. Check the
trivial residues, all real knots, the prime-square lower and
upper bounds at $\sqrt X$, and the higher-power losses by
monotone estimates at the fixed threshold. Use the completed
log-derivative difference at $2,-1$ and average primitive
zero bounds, then charge omitted Euler factors and prime
powers. Compare the resulting rational budget against the
zeta margin and $1/25$ with the exact discount. Check that
irrationality and the sampled eventual-sign premises still
apply to the pinned Landau converse.
