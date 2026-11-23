# Count rows sharing a smooth complement

**Test at one prime.** Keep the [joint residual](joint-radical-gap.md) at $t=1.11$, with $N=X^k=q^{2.5+o(1)}$, $B=\log\log q$, and $H=2N/q^{2.11}$. Two ordered product pairs with the same gcd $g$ can share the same pair of smooth divisors after cancelling $g$. For the choice of divisors below, let $D_g$ count ordered collisions of **distinct** rows on such a shared pair. A sufficient estimate for the whole residual is

$$\sum_g \sqrt g\, D_g \le q^{1.725-\epsilon} \qquad (\epsilon>0\text{ fixed}).$$

The direct one-divisor count gives $q^{1.835+o(1)}$ instead. This is a shortfall of that bound, not evidence for many actual collisions. Test the shared-divisor condition before running a second unrestricted smooth-pair count. The second moment is sufficient, not necessary; a first-moment alternative is given below.

**One edge per ordered pair.** Write $n=gu,m=gv$, $(u,v)=1$, and set $Z=\tfrac12\sqrt{N/H}\, B^{-2k}=q^{1.055+o(1)}$. We have $g\le H$, $|u-v|\le qH/g$, and $u,v\ge NB^{-4k}/g>Z$. In each of $u,v$ take the longest prefix of the prime factors in nondecreasing order with product at most $Z$. The products $c\mid u,d\mid v$ lie in $(Z/X,Z]$. At fixed $g$, join row $(a,b)=(u/c,v/d)$ to column $(c,d)$. Count only residual pairs. The choice is deterministic, and an edge recovers its pair. A row meets at most one column: For any two completions, $q\mid cd'-c'd$ by $ac\equiv bd\pmod q$ and $q\nmid a$. Also

$$|cd'-c'd|\le 2q(H/g)Z/a\le 2qHZ^2 B^{4k}/N=q/2.$$

The determinant vanishes, and both columns are primitive since $(u,v)=1$.

**Price of Cauchy-Schwarz.** Write $E_g$ for the number of edges and $s$ for a column degree, so $D_g=\sum s(s-1)$. The smooth count $\Psi(y,X)\le P\sqrt y$, where $P=\prod_{p\le X}(1-p^{-1/2})^{-1}=q^{o(1)}$, gives at most $M=P^2Z$ columns per $g$, and at most $P\sqrt H$ possible gcds. Also $\sum_g 1/\sqrt g\le P$ over distinct admissible gcds. From $E_g^2\le M(E_g+D_g)$ we obtain $E_g\le M+\sqrt{MD_g}$. Sum, using Cauchy-Schwarz on $g^{-1/4}(g^{1/4}\sqrt{D_g})$, to get

$$\sum_g E_g\le q^{1.25+o(1)} + q^{0.5275+o(1)}\left(\sum_g\sqrt g\,D_g\right)^{1/2}.$$

This gives the stated pass exponent $2(1.39)-1.055=1.725$ with a strict power saving required. It does not infer the all-$g$ conclusion from a squarefree $g=1$ experiment. Alternatively, for fixed small $\eta>0$ all columns of degree $s\le q^{0.335-\eta}/\sqrt g$ together contribute at most $MP q^{0.335-\eta}$ edges. It suffices to bound the **edges**, not the squared degrees, above this cutoff by $O(q^{1.39-\xi})$ for some fixed $\xi>0$. This alternative allows rare columns of very large degree.

**Where the ordinary count stops.** For a collision write $a_ic-b_id=q\delta_i$, $|\delta_i|\le H/g$. Then $z=a_1 b_2$, $z'=a_2 b_1$ are distinct since both rows are primitive, and

$$c(z-z')=q(b_2\delta_1-b_1\delta_2).$$

Thus $q\mid z-z'$. Put $U_g=(NX/(gZ))^2$, $J_g=2HNX^2/(g^2Z^2)$. We have $z,z'\le U_g$, $0<|z-z'|/q\le J_g$, and $z'\ge (NB^{-4k}/(gZ))^2>J_g$ uniformly for large $q$. For fixed $g,z,z'$ there are at most $2^{4k}$ ordered row decompositions by the divisor bound, and then at most one common column. The cross-products need not be coprime or squarefree, even on the squarefree initial test.

Dropping the common-column requirement, count $z$ by $P\sqrt{U_g}$. If $J_g<1$ there is no collision. Otherwise take a smooth divisor of $z'$ in $(J_g/X,J_g]$ as before. There are at most $P\sqrt{J_g}$ choices; the sign and divisor constrain $|z-z'|/q$ to one residue class modulo the divisor, with $O(X)$ possibilities. Consequently

$$D_g\le q^{o(1)}\sqrt{U_g J_g}\le q^{1.835+o(1)}/g^2,$$

since $g^2 U_g=q^{2.89+o(1)}$ and $g^2 J_g=q^{0.78+o(1)}$. Summing against $\sqrt g$ gives $1.835$ again, and $(1.055+1.835)/2=1.445$, the original row exponent. At $g=1$ even the second application of the progression bound needs more than $0.110$ in the collision exponent. An improvement could exploit the requirement that both signed gaps come from admissible rows on the **same** column. No such saving, fixed-$A$ floor, or estimate at $t=1.2$ is proved here.

**A test allowing large second moments.** Let $C_g$ count just the columns above the degree cutoff $q^{0.335-\eta}/\sqrt g$, with $0<\eta<0.1$. Since $g\le H$, those degrees exceed two for large $q$. Their total edge mass is at most

$$\sum_g\sqrt{2C_gD_g}\le q^{0.9175+o(1)}\left(\sum_g C_g/g\right)^{1/2}.$$

Here $s^2\le2s(s-1)$ on these columns; insert the unconditional per-$g$ bound above and use $\sum_g 1/g\le P$ in Cauchy-Schwarz. Thus a bound $\sum_g C_g/g\le q^{0.945-\epsilon}$ for fixed $\epsilon>0$ suffices, even if a few shared complements carry many rows. Start with the rich columns at $g=1$. The support bound over all gcds is an alternative unproved premise, not a consequence of row uniqueness.
