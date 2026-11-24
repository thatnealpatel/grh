---
evidence_revision: dca062832345d6f827769b6a1af9b923d21e3b0e
---

# Fourth-power samples of the mod-four prime ramp

Let $\chi_4$ be the primitive real character modulo $4$, and
for real $X\ge1$ let

$$P(X)=\sum_{p<X}\chi_4(p)\log p\,\log(X/p).$$

**Proposition to test:** There exists an integer $N\ge1$ such
that $P(n^4)\le0$ for every integer $n\ge N$ if and only if
every nontrivial zero of $L(s,\chi_4)$ has real part $1/2$.
The ramp is unnormalized, unmodulated, and over primes only,
with natural logarithms. No sign between samples is assumed.

**Source and payoff:** This is a proposed weakening of the
sampling premise of the [all-cutoff sign criterion](../closed/mod-four-prime-ramp-eventual-sign.md).
The ramp comes from Bob's [equation (1) and signed-pair use](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789`, taking
$(d_i,d_j)=(1,-4)$ at an odd base conductor and $v=0$. Neither
source asserts the sampled proposition. A transfer at this
mesh would separate the cost of chaining local intervals from
the arithmetic needed to establish the sampled signs.

**Discriminating test:** In $t=\log X$, subtract the chord of
the actual signed hinge sum on each adjacent sample cell.
Check which hinges remain, including equality at the cell
ends, and bound the one-sided deficit by counting integers,
without prime cancellation. Test whether the resulting
upper envelope is $O(\sqrt X\log^A(2X))$ for a fixed $A$.
If so, add a dominating envelope to $-P$ and test Landau on
that nonnegative tail, not on $-P$ itself. Check on
$\Re s>1/2$ the envelope transform, the prime-power
correction, real-axis regularity, zero-pole noncancellation,
and reflection. For the reverse direction check whether the
all-cutoff result applies with identical weights and cutoffs.