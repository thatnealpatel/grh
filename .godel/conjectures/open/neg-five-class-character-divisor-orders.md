---
evidence_revision: a684299f2b54e602be826969b35b7c1f30742700
---

# Zero orders of the two stage multipliers for the nontrivial class character

Let $\Lambda(s,\chi)$ be Masullo’s entire completed Hecke factor for the nontrivial ideal-class character of $F=\mathbb Q(\sqrt{-5})$. At $S''=S_\infty\cup\{\mathfrak p_2,\mathfrak p_5\}$, put $D_f(s)=L(s,\chi_{-4})L(s,\chi_5)$ and $D_{S''}(s)=(1+2^{-s})(1-5^{-s})D_f(s)$. The claim is equality of the full zero orders (order zero at a nonzero value):

$$
\operatorname{ord}_s\Lambda(\cdot,\chi)=
\begin{cases}
\operatorname{ord}_s D_{S''} & \text{on }\Re s>0,\\
\operatorname{ord}_s [D_{S''}(1-\cdot)] & \text{on }\Re s<1.
\end{cases}
$$

Both equalities must hold on the overlap. The two extra Euler factors have no zeros on the forward open half-plane, but they belong in the stage multiplier, not in the completed global factor.

The [completed-product audit](../../obligations/isotypic-inverse-range-q-sqrt-minus-five.md#verified-completed-product-and-divisibility) identifies the complex gamma factor by continuation. Lean checks the [finite Hecke product comparison](../../obligations/isotypic-euler-factorization-q-sqrt-minus-five.md#checked-all-prime-grouped-identity) on $\Re s>1$. The [glued closed-range calculation](../../obligations/isotypic-glued-closed-range-q-sqrt-minus-five.md) identifies both stage multipliers in reviewed mathematics. These are inputs, not a Lean proof of the two order equalities.

**Next discriminating test:** Write the quotient of $\Lambda$ by the forward multiplier, then by the reflected multiplier using the functional equation for this self-dual character. Track the gamma, conductor, and finite factors in the same normalization. Check for a holomorphic, nowhere-zero extension on each stated half-plane, explicitly at $s=1$ on the forward side and $s=0$ on the reflected side. A residual zero or pole in either domain would give an order mismatch. Success identifies the scalar vanishing conditions in the proposed range of (6.3.2.3), p. 304; it does not prove that the divided pair satisfies the local gluing relation.
