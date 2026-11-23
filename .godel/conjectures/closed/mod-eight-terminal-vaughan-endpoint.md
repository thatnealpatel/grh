---
evidence_revision: aa29b65e34d74fd33b15862966aab882d06b9722
outcome: established
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

## Resolution

The intervals for the exact quotient $t=q+1,\ldots,2q-1$ partition the outer range with no clipped intervals. Each is $(X-H,X]$ with $X=x/t$ and $H=x/[t(t+1)]$. Uniformly, $X\asymp x^{3/4}$ and $H\asymp X^{2/3}$. The inner tail is a single number $w_t$ throughout this interval, with $|w_t|\le 7$.

Use the short-interval progression estimate in Thorner and Zaman, [*Refinements to the prime number theorem for arithmetic progressions*](https://arxiv.org/abs/2108.10878), subsection “Connections with classical results,” display following the Hoheisel discussion. Take modulus $4$, $A=1$, and $\epsilon=1/24$. For large $x$, $H\ge X^{7/12+\epsilon}\log X$. For each of the classes $1,3$ the weighted prime sum is $H/2+O_B(H/(\log X)^B)$ for every fixed $B>0$, uniformly in these intervals. The stated stretched exponential beats every fixed inverse log power. Subtracting cancels the main terms. Adding higher prime powers costs at most $O(\sqrt X\log^2 X)$ per interval (count each exponent up to $\log_2 X$ separately), absorbed by the same error since $H\asymp X^{2/3}$. Thus

$$
\left|\sum_{X-H<m\le X}\Lambda(m)\chi(m)\right|
\ll_B H/(\log x)^B.
$$

Multiply by $w_t$ and sum: The interval lengths telescope to $x/(q+1)-x/(2q)$. This proves $E_8(x)\ll_B x^{3/4}/(\log x)^B$ at each cutoff. No GRH or averaging over $x$ enters. The mechanism works for **any** bounded quotient multiplier, with the bound multiplied by its supremum. In particular, neither the Möbius signs nor modulus eight of the endpoint contributed the saving. For the **whole terminal triangle**, the full inner prefix has modulus at most $q$, so the same argument gives $O_B(x/(\log x)^B)$. This beats the trivial $O(x)$ there, but neither gives a fixed power saving nor bounds the remaining Vaughan ranges at square-root scale.
