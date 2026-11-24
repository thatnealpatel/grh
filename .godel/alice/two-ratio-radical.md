# Count actual triples using both recoverable ratios

Fix one actual two-label list with $g=R=j=1$. Take the ordered triples left by the [reciprocal pair deletions](global-double-ratio.md); keep the successive-row conditions from the construction. With their notation put $z=Y/Y_0=n/w$, $S=kZ/(hZ_0)=x/y$, and $L=S/z$, using reduced coordinates for $z,S$. Fix one pool $P$ of at most $(\log q)^{1.10}$ eligible primes for the list. For a positive rational $u$, let $r(u)$ be the log to base $q$ of the product of the distinct primes outside $P$ with nonzero valuation in $u$.

**Triple price before pruning columns.** The retained triples with $r(L)\le 3.320$ cost at most $q^{1.13445+o(1)}$ on the entire list, with no ordinary/exceptional split. At the previous cutoff $2.760$ the price is $q^{1.00845+o(1)}$. This is a count of actual triples across moving prefixes, not a count of labels discounted by a multiplicity exponent.

Here is the support comparison. For prime sets outside $P$ write $w(E)=\sum_{p\in E}\log_q p$. Let $I_0$ be the intersection of the supports of $z$ and $S$, and $D_0$ the subset where both valuations are equal. Then

$$r(z)+r(S)=r(L)+w(I_0)+w(D_0).$$

Indeed the support of $L$ is the union minus $D_0$. Opposite signs and unequal nonzero valuations contribute to $I_0$ but not to $D_0$. The reduced supports are contained in the raw supports, so it suffices for $I_0$ to intersect each of $Y,Y_0$ with each of $hZ,kZ_0$. On the same column, the full part of the *second* row product supported on the first row is $<q^{.115}$ by [successive-row freshness](shared-row-labels.md). On opposite columns the full part of $dY$ on the support of the other column and both its rows is $<q^{.118+o(1)}$, and reciprocally for $eY_0$. The latter mask includes the cofactor, not just the output. Thus $w(I_0)\le 2(.115+.118)+o(1)=.466+o(1)$.

Every prime of $D_0$ divides $J_0=(n,x)(w,y)$, by the sign of its common valuation. The converse need not hold. In a dyadic bin $J\le J_0<2J$, put $t=\log_q J$. Then $w(D_0)\le t+o(1)$ and $t\le .466+o(1)$ by the [hidden-factor bound](global-double-ratio.md).

Bin both outside radical products dyadically. For either ratio of product-height exponent $b$, its cost in a bin of radical exponent $r$ is $q^{.05b+.45r+o(1)}$: Enumerate the outside radical at half power, its signed valuations at subpower cost once the support is known, and the inside part at exponent $.05$ on height $b-r+o(1)$. The [exact-ratio recoveries and prices](joint-valuation-escape.md) apply separately to $z$ and to $S$ **on the same bin**. Both have subpower fibers across the entire list. Since $b_z=2.890$ and $b_S=4.220$ are upper bounds, our triple exponent on $r(L)\le s$ is at most

$$\min\{.1445+.45r(z),\ .211+.45r(S)\}+o(1)
\ \le\ \frac{.3555+.45(s+.466+t)}2+o(1).$$

Here the radical exponents can be taken at bin endpoints with $o(1)$ loss. Taking $t\le .466+o(1)$ and summing the polylogarithmically many bins gives the claimed prices. Neither an independent second congruence nor an additional $L$-multiplicity charge is needed. This does not supersede the [separate distinct-label estimate](ordinary-outside-radical.md) in every bin.

**If the objective counts columns, delete them first.** Keep the same prescribed $P$. Remove every column for which any of the five keys $cd,h_i y_j$ has $r\le 1.980$. Their height is at most $q^{2.110+o(1)}$, and any single key specifies that column at subpower cost, including the cross-row keys. Thus the deletion costs $q^{.05(2.110)+.45(1.980)+o(1)}=q^{.9965+o(1)}$ incidences. Also remove all columns at any input with $r(v/F_1)\le 1.590$. Here the key $ca=v/F_1$ has height exponent $1.720$ and specifies just the input. Multiply the key count by the [pointwise degree](ordinary-outside-radical.md), $1+q^{.195+o(1)}$. This costs $q^{.05(1.720)+.45(1.590)+.195+o(1)}=q^{.9965+o(1)}$ incidences. Charging the partners too would give exponent $1.1915$ for either cut, outside the pair budget. Do not infer a small number of pairs in the original graph from these deletions.

On this subgraph every $h_i y_j$ has $r>1.980$, and $h_i\le q^{.665+o(1)}$. In particular all four raw outputs have $r>1.315-o(1)$. On retained pairs, primes common to $Y,Y_0$ divide their gcd, of size at most $q^{.118+o(1)}$ by the reciprocal mask. Passing to $z$ loses at most twice their log radical from $r(Y)+r(Y_0)$, so **$r(z)>2.394-o(1)$**. Now if $r(L)\le 3.510$, the support comparison gives $r(S)\le 3.510+.466+.466-2.394+o(1)=2.048+o(1)$. Pricing $S$ alone costs at most $q^{.211+.45(2.048)+o(1)}=q^{1.1326+o(1)}$ triples on the pruned graph. This higher cutoff is not a price on all original triples.

**Remaining incidence test.** Write $C_*$ for the ordinary retained pairs with their shared inputs on this subgraph satisfying $r(L)>3.510$. The pointwise reciprocal deletions still apply there: Sum their original per-reference bounds over the surviving references. Cauchy on at most $q^{.860+o(1)}$ inputs, restoring the two incidence charges, gives for the original column count

$$I\le q^{.9965+o(1)}+q^{.430+o(1)}\sqrt{q^{1.1355+o(1)}+q^{1.1326+o(1)}+C_*},$$

using the [exceptional price](cheap-filter-occupancy.md). There is no sum over pools and no permission for an endpoint cut to depend on its future partner. The next common-input lift count need only bound $C_*\le q^{1.136-\eta}$ for fixed $\eta>0$; no such bound is proved here. If counting triples on the *unpruned* list instead, use $3.320$, not $3.510$, as the new radical threshold.
