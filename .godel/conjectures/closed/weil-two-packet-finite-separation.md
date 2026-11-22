---
evidence_revision: 022676f32fb32118354a025cb57b7c48d5dac9cf
outcome: established
---

# A compact-window bound controls two packets through separation 1.5

Let $Q$ be the rational Weil Hermitian form in additive log coordinates, $b$ a smooth packet supported on an interval of length at most $0.1$, $T_t$ translation, and $K(t)=Q(b,T_t b)$. **Given** $Q(u,u)\ge0$ for every smooth complex $u$ supported in $[-0.8,0.8]$, one has $|K(t)|\le K(0)$ for $|t|\le1.5$.

**Established as an implication:** Every linear combination of the two packets fits, after a common translation, into the certified window because its span is at most $0.1+|t|$. Translation leaves the Weil form unchanged. Positivity of the resulting two-by-two Gram matrix gives the inequality by its determinant.

The [compact-window preprint](https://arxiv.org/abs/2608.24827), corollary “Positivity for arbitrary test functions,” reports the stronger lower bound $8.9\times10^{-18}\|u\|_2^2$. We inspected its statement and zero-side normalization, not the numerical certificate. The argument above is on paper, not in Lean. Unlike the [short-support input](https://arxiv.org/abs/2006.13771), this window covers $t=\log 2,\log 3,\log 4$ with the prime and archimedean terms together. It does not establish [unbounded separation](weil-two-packet-all-separations.md).
