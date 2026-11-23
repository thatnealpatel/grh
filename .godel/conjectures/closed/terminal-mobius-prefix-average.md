---
evidence_revision: dcc11ec5bbd653cbb1068ea454799744de33fb73
outcome: established
---

# Does averaging the terminal Möbius prefixes weaken the power-bound target?

Write $S(u)=\sum_{n\le u}\mu(n)\chi_4(n)$ and $A(q)=q^{-1}\sum_{q<t<2q}|S(t)-S(q)|$, with integer cutoffs. Test the conjecture that, for fixed $0<\alpha<1$, a uniform $A(q)\ll q^\alpha$ is equivalent to $S(q)\ll q^\alpha$. The terminal triangle in the [endpoint certificate](../closed/mod-eight-terminal-vaughan-endpoint.md) uses this average only after taking absolute values of the outer prime sums. Every integer $q$ occurs at $x=q^4$.

**Discriminating test:** Compare two nearby starting points against common endpoints in their overlapping doubling intervals. Track the cost of reconstructing an individual prefix and distinguish uniform control from a bound for typical starting points. If the equivalence holds, determine its zero-free implication without assuming GRH.

## Resolution

Set $r=\lfloor3q/4\rfloor$. For $q\ge16$, the overlap $q<t<2r$ has $2r-q-1\ge q/4$ integer points. For each such point, compare $S(q)$ and $S(r)$ via $S(t)$, then sum. This gives

$$
(2r-q-1)|S(q)-S(r)|\le qA(q)+rA(r).
$$

A uniform $A(q)\ll q^\alpha$ bounds this difference by $O(q^\alpha)$. Iterate $q\mapsto\lfloor3q/4\rfloor$ until below 16. The resulting error is bounded by $O(q^\alpha\sum_{j\ge0}(3/4)^{j\alpha})$. Conversely, $S(q)\ll q^\alpha$ bounds every difference in $A(q)$ by $O(q^\alpha)$. This deterministic equivalence holds for any sequence of partial sums; it does not follow from an estimate for a typical anchor $q$.

For the actual arithmetic sequence, $S(u)\ll u^\alpha$ makes $s\int_1^\infty S(u)u^{-s-1}\,du$ holomorphic on $\Re s>\alpha$. It equals $1/L(s,\chi_4)$ on $\Re s>1$ by the unconditional Euler product. Multiplying by the entire $L(s,\chi_4)$ and continuing the identity shows that $L$ has no zero on $\Re s>\alpha$. This is a consequence of a hypothetical power saving, not a proof of one.

An unconditional benchmark is $A(q)\ll_B q/(\log q)^B$ for every fixed $B>0$: Take the imaginary part of Davenport's linear exponential-sum estimate at frequency $1/4$, using $\chi_4(n)=\sin(\pi n/2)$, and bound $S(t)$ and $S(q)$ separately. See Green and Tao, [*Quadratic uniformity of the Möbius function*](https://arxiv.org/abs/math/0606087), (1.3). Combining this with the certificate buys logarithms but stays in its existing arbitrary-log-saving class. A genuinely different target keeps the sign of the outer interval sum paired with the prefix, rather than bounding the prefix against all bounded weights uniformly.
