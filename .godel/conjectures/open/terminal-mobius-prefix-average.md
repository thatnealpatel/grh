---
evidence_revision: dcc11ec5bbd653cbb1068ea454799744de33fb73
---

# Does averaging the terminal Möbius prefixes weaken the power-bound target?

Write $S(u)=\sum_{n\le u}\mu(n)\chi_4(n)$ and $A(q)=q^{-1}\sum_{q<t<2q}|S(t)-S(q)|$, with integer cutoffs. Test the conjecture that, for fixed $0<\alpha<1$, a uniform $A(q)\ll q^\alpha$ is equivalent to $S(q)\ll q^\alpha$. The terminal triangle in the [endpoint certificate](../closed/mod-eight-terminal-vaughan-endpoint.md) uses this average only after taking absolute values of the outer prime sums. Every integer $q$ occurs at $x=q^4$.

**Discriminating test:** Compare two nearby starting points against common endpoints in their overlapping doubling intervals. Track the cost of reconstructing an individual prefix and distinguish uniform control from a bound for typical starting points. If the equivalence holds, determine its zero-free implication without assuming GRH.
