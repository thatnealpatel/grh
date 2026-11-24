# Charge the occupied planes with small reduced normal denominator

Fix one actual constructed two-label list in the $g=R=j=1$ stratum. Use the residual ordered triples and the **ordered** visible split $(P,Q_0)$ of [the global ratio count](global-double-ratio.md). Write $Q=Q_0$, $F=F_1$, and use $g$ below only for the image index of a plane normal, not the stratum parameter. Among rank-two splits with $a\ell\ne0$ and $R_0>q^{.446}$, all triples for which

$$u=|a|/\gcd(|a|,|\ell|)\le q^{.160}$$

together cost at most $q^{1.135+o(1)}$. This is a total over varying splits on the list, not the price of fixing a split or global label. It includes the case $|a|\le q^{.160}$. We do not assume $a$ or $\ell$ is smooth.

**Inputs.** The congruence lattice is $Fm\equiv q\alpha\pmod P$, $Fm\equiv q\alpha_0\pmod Q$ in the box of radii $(V,H,H)$. The coprime eligible-smooth moduli $P,Q$ are units modulo $Fq$ and both exceed $2H$. We use $F=q^{.780+o(1)}$, $V=q^{1.720+o(1)}$, and $H=q^{.390+o(1)}$. Orient the primitive normal $(a,b,c_0)$ of the span of the lattice points in the box by $a>0$. Let $g$ generate the image of the lattice under the normal, $\lambda=PQ/g$, $D_0=\|(aV,bH,c_0H)\|_2$, and $R_0=VH^2/(\lambda D_0)$. The ambient lattice has index $PQ$; taking images under the primitive normal shows $g\mid PQ$ and gives index $\lambda$ in the integral plane. Thus both $g$ and $\lambda$ are eligible-smooth. The vector $(q,F,F)$ gives the integer $\ell=(qa+F(b+c_0))/g$. In particular, with $K=qH^2+2FVH$,

$$g\ell\equiv qa\pmod F,\qquad |g\ell|\le K/(\lambda R_0),\qquad \lambda R_0 a\le H^2.$$

**Recover the moduli from normal fractions.** We have $(a,g)=1$. If $p\mid(a,g)$, it divides exactly one of $P,Q$. For $p\mid P$, evaluation on $(0,0,Q)$ gives $p\mid c_0$; evaluation on $(q,F,F)$ gives $p\mid b$ as well. For $p\mid Q$, start with $(0,P,0)$. Both violate primitiveness.

Fix dyadic bins $R\le R_0<2R$, $J\le\lambda<2J$, $U\le u<2U$. Put $t=(a,|\ell|)$, $n=g\ell/t$, and $d=a/t=u$. The fraction $n/d$ is reduced, with $d>0$ and $g\mid |n|\ne0$. **Do not cancel $t$ modulo $F$.** Instead group by $s=(F,t)$ at divisor cost. For each fraction in that group $n\equiv qd\pmod{F/s}$, and $|n|\le K/(JRs)$. For any two of them, the signed determinant $\Delta=n_1d_2-n_2d_1$ therefore satisfies

$$F/s\mid\Delta,\qquad |\Delta|/(F/s)\le T:=4KU/(FJR).$$

The loss in the modulus cancels the improvement in the numerator height. With the full modulus alone the deduction would be invalid.

If $g\le T$, enumerate $g$. Otherwise choose a divisor $f\mid g$ strictly crossing $T$ by multiplying its prime factors until the first crossing (use $f=1$ when $T<1$). Then $f\le\max(1,TX)$ for the eligible-prime ceiling $X=q^{o(1)}$. Two fractions sharing $f$ have $f\mid\Delta$, and $(f,F)=1$, hence $f\mid\Delta/(F/s)$. This forces equality of the fractions. In this branch the chosen $f$ fixes at most one reduced fraction within the group and bins; enumerate $g$ among the divisors of its nonzero numerator. Uniqueness suffices for an upper bound, without an algorithm to find the fraction.

The [smooth half-power estimate](shared-complement-count.md) charges the small-$g$ and crossing choices at most $q^{o(1)}(1+\sqrt T)$ in total. Enumerate the smooth $\lambda<2J$ at $q^{o(1)}\sqrt J$ cost. Each known $g\lambda$ has divisor-many ordered splits $(P,Q)$. All divisor bounds here are subpower since the integers have polynomial height. Thus the number of splits in the bins is at most

$$q^{o(1)}(1+\sqrt T)\sqrt J\ll q^{o(1)}\left(\sqrt J+\sqrt{KU/(FR)}\right).$$

**Return to triples.** As in the global ratio count, each occupied split costs $q^{o(1)}(1+\sqrt{R_0})$ triples, without fixing $L$. Indeed if $j$ generates the image of the plane lattice on the $m$-axis, restrict $m/j$ by a smooth divisor strictly crossing $3R_0$, or enumerate $m/j$ itself below the cut. In the former branch the index on the plane is exactly the selected divisor, so independent box vectors are impossible by scaled area. On a line there is at most one primitive point with $m>0$. In the latter branch fixed $m$ gives at most one gap in each residue class. Actual points determine their ordered triples by the two sorted prefixes. It is enough to upper-bound, not assume, occupancy.

For the specified class the multiplier is $O(q^{o(1)}\sqrt R)$. Since $RJ\le H^2/a$ and $K/F=q^{2.110+o(1)}$, the weighted price per bin is at most

$$q^{o(1)}\left(H+\sqrt{KU/F}\right)\le q^{1.135+o(1)}.$$

There are only polylogarithmically many bins. This is below $1.136$ by a fixed margin in the exponent. For an exceptional split still outside the charge, $u>q^{.160}$ and $\lambda\le q^{.174+o(1)}$ by $\lambda R_0a\le H^2$. A next test is whether these small complementary indices, together with the separate divisibilities $(g,P)\mid c_0$ and $(g,Q)\mid b$, improve on counting $g\lambda$ via its single normal residue. The latter two divisibilities follow by evaluating on $(0,0,Q)$ and $(0,P,0)$, respectively. Without a new constraint the term $\sqrt{KU/F}$ reaches $q^{1.136+o(1)}$ already at $U=q^{.162}$. Neither the other exceptional splits nor the number of labels outside this plane argument have been bounded at the required price.
