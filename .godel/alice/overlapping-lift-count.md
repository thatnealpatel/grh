# Two arithmetic cuts on the large-gap-determinant rectangles

Keep the actual $g=1$ incidences, ordered labels, column ordering, and $S=|\det(v_1,v_2)|r_2/r_1$ of the [gap-direction count](gap-direction-rectangles.md). Put $t_\ell=(x_{1\ell}y_{2\ell}-x_{2\ell}y_{1\ell})/q$ and $T_\ell=|t_\ell|/r_\ell$. Even without any prime overlap, the rectangle exponent is at most **2.665** when $T_1 T_2\le q^{1.110}$. This is a product of two within-column quantities; $S$ may be arbitrarily large within its original range. A different cut uses smooth overlap. Write $G_\ell=\gcd(y_{1\ell},y_{2\ell})$ and $J_\ell=\gcd(d_\ell,G_\ell)$. The rectangle exponent is at most **2.665** on the union of

* $q^{.330}<S\le q^{.410}$ with $G_1\ge q^{.080}$ **or** $J_2\ge q^{.080}$;
* $S>q^{.330}$ with $J_2\ge q^{.080}$ and $r_2\ge q^{.290}$.

These upper bounds do not need reciprocal freshness. In particular they bound the corresponding subcounts with the original freshness requirement. They do not bound all rectangles with two unrelated squarefree $y$ coordinates on each column. Below we also give a smaller sufficient saving for the **edge** objective, without claiming that it suffices for the original unweighted $R_2$ objective.

## A strip normal to the known row coordinates

In fact for $P\ge1$ the rectangle count on $T_1T_2\le P$ is

$$\ll q^{2.110+o(1)}(H+\sqrt P).$$

Forget the cut on $S$ when upper bounding this subcount, so we may count first the column with **smaller $T$**, without changing either row's position or label. The factor for restoring the column order is at most two. Box $T_\ell\in[V_\ell,2V_\ell)$ dyadically, $V_1\le V_2$, $V_1V_2\le P$. These lower endpoints start at one since $r_\ell\mid t_\ell\ne0$. For the first incidence choose its column and starting row in $q^{1.445+o(1)}$ ways. The normalized neighbour lemma with empty mask and parameter $2V_1$ costs $q^{o(1)}\sqrt{V_1}$ for the other row. Labels cost only a divisor loss.

Fix the second $h$ pair at cost $q^{.665+o(1)}$. On this column box $R\le r<2R$, and drop its subscript. The identity $x_2v^{(1)}-x_1v^{(2)}=dt/r$ places $v$ in the centred intersection

$$\|v\|_\infty\le H/R,\qquad |x_2v^{(1)}-x_1v^{(2)}|\le 2ZV_2.$$

Its area is at most $8HZ V_2/(R x_1)\le 2V_2/R$ since $HZ/A_-=1/4$ exactly. This strip does not refer to the first gap direction. Put $B_*=\max(1,V_2/R)\le\max(1,W)$. Sieve by a smooth divisor of $d$ at scale $B_*$, then recover $d$ from the nonzero linear form and sieve $c$ at scale $R$, as in the gap-direction proof. The first step costs $q^{o(1)}\sqrt{B_*}$ by primitivity in the centred body, the last $q^{o(1)}\sqrt R$. The divisors exist since $Z/X>\max(W,2H)$. Both remaining row coordinates are forced. The net count in the box is at most

$$q^{2.110+o(1)}\sqrt{V_1\max(R,V_2)}.$$

If $V_2\ge R$, the radical is at most $\sqrt P$. Otherwise $V_1\le V_2<R\le H$, so it is at most $H$. Summing the boxes proves the assertion. The $H$ term avoids claiming a fractional direction count on very thin bodies. At $P=q^{1.110}$ the cost beyond $2.110$ is $.555$; at the trivial $P=W^2$ it is $.780$ and there is no saving. This exploits actual short row determinants even when the gap directions need not be close. It is not a bound for the frequency of small $T_1T_2$.

## A divisor available on both sides of reconstruction

On the second column suppress the column subscript. With $x_i=F_i h_i$, $cx_i-dy_i=qr v^{(i)}$, put $N_v=x_2v^{(1)}-x_1v^{(2)}$ and $t=(x_1y_2-x_2y_1)/q$. Distinct positive primitive rows on a common column give $t\ne0$ integral, $dt=rN_v$. All of $cdx_1x_2y_1y_2$ is coprime to $r$: A prime of $r$ dividing an endpoint on either row must divide the opposite endpoint. Hence $E=N_v/d=t/r$ is a nonzero integer. Since $G\mid qrE$ and $(G,qr)=1$, one has **$dG\mid N_v$**, not merely $\operatorname{lcm}(d,G)\mid N_v$.

Box $r_\ell\in[R_\ell,2R_\ell)$ dyadically. For $S>0$ use a direction body consisting of the intersection of the boxes $\|v\|_\infty\le\min(\|v_1\|_\infty,H/R_2)$ and, if $S\le K$ is imposed, the strip $|\det(v_1,v)|\le 2KR_1/R_2$. It is centred of area $O(B_0)$ with $B_0=(H/R_2)^2$, or the minimum of this and $2KR_1/R_2$ for the strip. Empty boxes can be omitted, so $B_0\ge1$.

Fix the first incidence and the second $h$ pair. If $J\ge Q\ge1$, let $U=\min(Q,\sqrt{B_0})$. Multiply eligible prime factors to choose $u\mid J$ in $[U/X,U]$, then $e\mid d/u$ in $[B_0/u^2,XB_0/u^2]$. The latter crossing is possible since $du\ge d>Z/X>2H^2$. Now $u^2 e\mid dG\mid N_v$. Even if $u$ and $e$ share primes, $x_1$ is a unit modulo $u^2 e$, since every prime here divides $d$. The direction lattice has index $u^2 e\ge B_0$. Each choice leaves $O(1)$ primitive directions: Pick's theorem if the points span the plane, and at most two on a line through zero otherwise. The smooth divisor pairs cost only $q^{o(1)}\sqrt{B_0/U}$: Their product $ue\le X^2 B_0/U$ is smooth and has subpowerly many splits. This counts divisors before knowing the exact direction.

After fixing $v$, enumerate $d\mid |N_v|$, then $G\mid |E|$, at subpower cost. Choose $b x_1\equiv q v^{(1)}\pmod d$. The actual lift has $c=br+dj$, $y_i=b_i r+x_i j$ where $b_i=(b x_i-q v^{(i)})/d$ is integral by $d\mid N_v$. The pair $(r,j)$ is primitive since $(r,c)=1$. If $G\ge\Gamma\ge1$, impose $G\mid b_1 r+x_1 j$ at no further enumeration cost. A divisor $f\mid c$ in $[\max(1,R_2/G),X\max(1,R_2/G)]$ exists since $c>Z/X>2H$. Impose also $f\mid br+dj$. The joint index is $Gf$: The individual forms are surjective since $(x_1,G)=(d,f)=1$, and $(G,f)=1$ by endpoint primitivity. These are necessary conditions, not sufficient smoothness tests. The area of $|r|\le2R_2, |br+dj|\le Z$ divided by the index is $O(R_2 Z/(dGf))=O(X)$. The same primitive-point argument leaves subpowerly many lifts per $f$, at total cost $q^{o(1)}\sqrt{\max(1,R_2/\Gamma)}$. Both $y_i$ are then forced. One must not count a common divisor of $y_1,y_2$ as two independent lift congruences.

For the first incidence conditional on $G_1\ge L_0\ge1$, start on its fixed column at the first selected row. Mask the primes of its $y$ coordinate in the [normalized neighbour lemma](rich-column-rows.md). On the next row the full masked product is at least $G_1$. Since $|t|\le W$, the lemma costs $q^{o(1)}\sqrt{W/(R_1L_0)}$ neighbours for $R_1L_0\le W$. This inequality holds in each nonempty box: $r_1G_1\mid t\ne0$. There are at most $q^{1.055+o(1)}$ columns and $q^{.390+o(1)}$ starting rows per column. Together with the $q^{.665+o(1)}$ second $h$ pairs, we obtain the box count

$$
q^{2.500+o(1)}\sqrt{\frac{B_0\max(1,R_2/\Gamma)}{R_1L_0\min(Q,\sqrt{B_0})}}.
$$

For the first strip with $G_1\ge q^{.080}$ use $L_0=q^{.080}$ and $Q=\Gamma=1$, giving $q^{2.500+o(1)}\sqrt{2K/L_0}$. For the strip with $J_2\ge q^{.080}$ use $Q=\Gamma=q^{.080}$ and $L_0=1$. If $B_0\ge Q^2$ the factor beyond $q^{2.500+o(1)}$ is at most $\sqrt{2K/Q}$. Otherwise it is at most $(2K)^{1/4}$ when $R_2\le Q$, and $(2KH)^{1/4}/\sqrt Q$ when $R_2>Q$. At $K=q^{.410}$ these exponents are $.165,.1025,.160$, respectively. For the second range use the full box and $Q=\Gamma=q^{.080}$; the second-column count per first incidence is at most

$$q^{.665+o(1)} H/\sqrt{\min(R_2Q^2,HQ)}\le q^{.830+o(1)}$$

since $R_2\ge q^{.290}/2$. Sum the dyadic boxes and allow either original column order. In contrast, $r_1=r_2=G_1=G_2=1$ and full-size directions still give $2.890$. At $r_2=1$ the reconstruction bound once $v,d$ are fixed is already subpower: A saving there needs to exclude candidates altogether, not reduce a positive per-candidate multiplicity.

## Localize the edge objective before the arithmetic test

Take a dyadic bin of original degrees $D\le s<2D$, $D=q^\sigma$, $.334-o(1)\le\sigma\le.390+o(1)$. Count the [constructed lists](shared-row-labels.md) in this bin only. In fact one may first discard pairs with $T_\ell/G_\ell\le D^2q^{-\eta}$ on their column, for any fixed small $\eta>0$: The masked neighbour lemma with parameter $D^2q^{-\eta}$ leaves at most $q^{o(1)}Dq^{-\eta/2}$ such neighbours per starting row (the full masked part is at least $G_\ell$). Thus the retained lists still number $(1-o(1))s^2$ per column. This thinning is optional and only for the edge objective. Since $r_\ell T_\ell\le W$, it gives $r_\ell G_\ell<Wq^\eta/D^2$. At the top degree scale one may already require both $r_\ell G_\ell<q^{\eta+o(1)}$ and $T_\ell>q^{.780-\eta+o(1)}$ in each column. This explains why neither overlap nor the small-$T_1T_2$ count alone is likely to settle the edge objective.

Weight each retained incidence by $1/s$. There are at most $q^{.780+o(1)}$ lists. Those with popularity $m\le q^{.608}D$ cost $q^{1.388+o(1)}$ in the bin. Bin the others by $M\le m<2M$, $M=q^\mu$, and put $I=\sum m$ in this bucket. Count ordered pairs of distinct retained columns on each list, requiring each recovery product in either column to have full outside part at least $q^{2\mu-.004}$ relative to the other column's support. The fixed-mask bound for a list costs $q^{\mu-.002+o(1)}$ failures per first incidence in one order; double this for both orders. The bound is uniform in the bucket since Rankin costs the same Euler product at every threshold. Hence $R_{D,M}\ge(1-o(1))MI$ and the represented edge weight is at most $(1+o(1))R_{D,M}/(DM)$.

Use $K=q^{2(\sigma+\mu-1.1115)}$. In the retained buckets $\mu\ge .608+\sigma-o(1)$, so $K\ge q^{.329-o(1)}$. The existing unconditioned strip estimate divided by $DM$ costs at most $q^{1.3885+o(1)}$. A bound $R_{D,M}(S>K)\le q^{1.390+\sigma+\mu-\epsilon}$ uniformly for fixed $\epsilon>0$ would now suffice, summing subpowerly many buckets. The unrestricted bound is $2MI\ll q^{1.055+2\sigma+\mu+o(1)}$, since each column contributes $O(D^2)$ lists. Its excess exponent over the boundary is $\sigma-.335\le.055+o(1)$. At the top scales $(\sigma,\mu)=(.390,1.055)+o(1)$ the determinant cutoff is $q^{.667+o(1)}$ and the outside cut is $q^{2.106+o(1)}$. Test the frequency of *nonempty* jointly smooth reconstructions at small $rG$ in these high-degree buckets. Neither this weighted reformulation nor the overlap subcounts prove the global $R_2$ bound, an all-gcd saving, or a fixed-window floor.
