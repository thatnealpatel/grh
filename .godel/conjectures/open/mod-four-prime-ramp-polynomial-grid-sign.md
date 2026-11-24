---
evidence_revision: 61af82a6f5935dbfe5d699c03bcbd3e804b71c1d
---

# Polynomial-grid signs of the mod-four prime ramp

Let $\chi_4$ be the primitive real character modulo $4$ and
let $P(X)=\sum_{p<X}\chi_4(p)\log p\,\log(X/p)$ for real
$X\ge1$, over genuine primes with natural logarithms.

**Proposition to test:** For every fixed integer $k\ge5$,
$\exists N\in\mathbb N\;\forall n\in\mathbb N,\ n\ge N:
P(n^k)\le0$ if and only if every nontrivial zero of
$L(s,\chi_4)$ has real part $1/2$. Each individual $k$ has
its own premise; no simultaneous signs, rate, or between-
sample signs are assumed.

**Source and payoff:** This operator conjecture extends the
[fourth-power criterion](../closed/mod-four-prime-ramp-fourth-power-sign.md)
at the evidence revision, using the identical ramp from
Bob's [equation (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789` with
$(d_i,d_j)=(1,-4)$ and $v=0$. The [all-cutoff criterion](../closed/mod-four-prime-ramp-eventual-sign.md)
landed at `dca062832345d6f827769b6a1af9b923d21e3b0e`.
Neither source claims this extension. It would test whether
a sharper slope bound and iteration can replace the one-shot
cell bound without any new assumptions on the samples.

**Discriminating test:** Start from the trivial bound or
nonvanishing in $\Re s>a$, allowing boundary zeros. Prove or
obstruct an unsmoothed prime-log bound with an arbitrarily
small exponent loss using a finite Perron contour or a
truncated explicit formula. Check sharp endpoints, prime
powers, and constant dependence. Anchor at the left sample
and integrate the slope against the actual log gap. Test
whether the nonnegative envelope-minus-ramp tail gives a
strictly better zero-free half-plane by Landau, verifying
real-axis regularity and noncancellation. Track losses and
constants over finitely many steps, including the final
threshold $1/2$. For the converse, verify that the all-cutoff
result applies without a normalization or cutoff change.
