---
evidence_revision: aa29b65e34d74fd33b15862966aab882d06b9722
---

# Modulo-eight endpoint tails in the terminal Vaughan triangle

Let $x$ tend to infinity through integers, $q=\lfloor x^{1/4}\rfloor$, and $\chi=\chi_4$. For $x/(2q)<m\le x/(q+1)$ put $t=\lfloor x/m\rfloor$ and $a(t)=\max(q,8\lfloor t/8\rfloor)$. In the terminal Vaughan triangle the inner coefficient on $q<n\le t<2q$ is exactly $\mu(n)$, since no proper divisor of $n$ exceeds $q$.

Conjecture: The signed contribution from the final incomplete block satisfies

$$
E_8(x)=\sum_{x/(2q)<m\le x/(q+1)}\Lambda(m)\chi(m)
\sum_{a(t)<n\le t}\mu(n)\chi(n)=o(x^{3/4}).
$$

The absolute row bound is $O(x^{3/4})$ by Chebyshev and the seven-term cutoff. This is a test of the endpoint mechanism, not a claim that the complete blocks are negligible or that $D(x)$ has square-root cancellation.

**Next discriminating test:** Group by the exact quotient $t$, retaining its residue modulo eight, and identify the arithmetic estimate required on each resulting interval of $m$. Test whether an unconditional theorem gives a saving, whether the same proof works for arbitrary bounded inner weights or other fixed block lengths, and what remains in the full triangle. In particular, do not infer cancellation from the sign table or from averaging over cutoffs.
