# Two arithmetic cuts outside the translated gap boxes

Work at $g=1$ on the actual [two-position lists](shared-row-labels.md). Keep $x_i=F_i h_i$, $cx_i-dy_i=q\delta_i$, $0<|\delta_i|\le H$, and $t=(x_1y_2-x_2y_1)/q$, with $0<|t|\le W$. All smooth coordinates have primes at most $X=(\log q)^{2+o(1)}$. Neither cut below restricts the location of the gaps. They can therefore be applied after deleting any of the [priced translated rectangles](short-label-ratios.md). We never replace the signed products by arbitrary weights.

## Small prime sets in the forced outputs

Fix a first list incidence and both cofactors of a second realization. Choose one set $P$ of at most $(\log q)^{1.85}$ eligible primes using only these data. Among reconstructions with $G=(y_1,y_2)\le\sqrt W$, at most

$$W^{.425}q^{o(1)}$$

have full $P$-part of $y_1y_2$ at least $W$. This counts actual columns, not full gap boxes that contain one such column.

Indeed write $y_i=GY_i$. Then $(Y_1,Y_2)=1$, $q\nmid G$, and $x_1Y_2-x_2Y_1\equiv0\pmod q$. In the centred box $|Y_i|\le A_+/G$ also impose $|x_1Y_2-x_2Y_1|\le qW/G$. The area is at most $4q(W/G^2)(A_+/x_1)$ by integrating in $Y_1$. The $P$-part of $Y_1Y_2$ is at least $V=W/G^2\ge1$. Accumulate its primes, with multiplicities, up to the first product $V\le f\le XV$ (take $1$ at $V=1$). Split $f=f_1f_2$ with $f_i\mid Y_i$. The [restricted Rankin estimate](rich-column-rows.md) gives $q^{o(1)}V^{.425}$ choices including splits. The lattice defined by these two divisibilities and the slope congruence has index $qf$: After substitution of multiples of $f_i$, the coefficient $x_1 f_2$ is a unit mod $q$. The area divided by index is $q^{o(1)}$ since $A_+/A_-=q^{o(1)}$. If the lattice points span the plane, Pick's theorem on their convex hull bounds their number by twice this ratio plus two. Otherwise the line goes through zero and carries at most two ambient primitive points. This argument uses the normalized $Y$, not primitivity of $(y_1,y_2)$.

For each point the first recovered row $(x_1,GY_1)$ determines at most one column by row uniqueness. Sum over **all** smooth $G$ in range: $\sum G^{-.850}\le\prod_{p\le X}(1-p^{-.850})^{-1}=q^{o(1)}$. No support condition on $G$ is needed.

**Unweighted price for a smaller mask.** Count the column with larger $G$ first (tie-break before choosing the mask). After fixing it and the second cofactors, allow one mask of at most $(\log q)^{1.4}$ eligible primes. If the second $y_1y_2$ has $P$-part at least $W$, the restricted unweighted pair count is at most $q^{2.656+o(1)}$. This has no cut on either gap vector, or on $G,r,S$, or $T_1T_2$. It applies in particular at $r_1G_1=r_2G_2=1$. For a common predetermined mask one can use it for pairs concentrated on both sides, but not automatically for concentration on just the larger-$G$ side.

To see this, take a dyadic box $J\le G_1<2J$. There are at most $q^{1.835+o(1)}/\sqrt J$ first incidences: On a fixed column at the first row, mask its $y$ primes in the normalized neighbour lemma with parameter $W/J\ge1$ (in nonempty boxes $G_1\mid t_1$). The full masked part of the next row is at least $G_1$. There are at most $q^{o(1)}\sqrt J$ smooth choices $G_2\le2J$. For each, repeat the normalized strip proof with crossing scale $V=\max(1,W/G_2^2)$ and restricted Rankin exponent $.200+(\log\log q)^{-1/2}$: The log Euler product is at most $O((\log q)^{1.4}(X/(\log\log q)^4)^{-.200-(\log\log q)^{-1/2}})=o(\log q)$ with the same eligible-prime lower bound as in the $.425$ estimate. At $V=1$ take $f=1$ and use the area bound without any crossing. Thus for fixed $G_2,h_1,h_2$ the count is at most $W^{.200}q^{o(1)}$. The two factors of $\sqrt J$ cancel, giving exponent $1.835+.665+.780(.200)=2.656$. If the first column must instead be prescribed in the original order, the identical bound holds in the $G_2=1$ subcase without any comparison of $G_1,G_2$. This is a restriction on the forced outputs, not evidence that a small mask captures most of them.

**Weighted price.** Use the optional [degree thinning](overlapping-lift-count.md) before forming lists. In a bin $D=q^\sigma$ it leaves $rG<Wq^\eta/D^2$, in particular $G<\sqrt W$ throughout the rich bins for small fixed $\eta$. Summing over the two smooth cofactors costs $q^{.665+o(1)}$ per first incidence, so the number of restricted partners per first incidence is at most $q^{.9965+o(1)}$. At the top degree $\sigma=.390+o(1)$, there are at most $q^{.780+o(1)}M$ first incidences in a popularity bucket $M\le m<2M$. Dividing the restricted pair count by $DM$ costs $q^{1.3865+o(1)}$, for any such retained popularity bucket. Equivalently the cut loses $o(m)$ partners there since $m\ge q^{.608}D$. For smaller degrees the same calculation costs $q^{1.7765-\sigma+o(1)}$, not a uniform saving. One may take a union over a predetermined subpower family of masks, e.g., all consecutive blocks of at most $(\log q)^{1.85}$ eligible primes in increasing order (at most $X^2$ blocks). This does not permit arbitrary masks chosen to fit the two outputs.

This is different from counting neighbours on one known column. Here the column moves, the mask can vary with the second cofactor pair, and neither single $y_i$ need have $P$-part $W$. Do not use a mask contained in the first support to motivate the cut at top popularity: Reciprocal freshness of $h_i y_i$ already precludes the requisite overlap. For the fixed mask consisting of the largest $(\log q)^{1.85}$ eligible primes (round down), there is also a simpler prefix case. If $d$ contains a prime there, *every* prime of each $y$ is there by sorted prefix order. Then $P$-part$(xy)\ge y>W$ on that column; the old single-column bound gives $s\le1+q^{.3315+o(1)}$ and hence no rich column of this type. It does not give the moving-mask estimate above.

## Shared divisors of actual signed-product differences

On each column let

$$n=|F_2 h_2\delta_1-F_1 h_1\delta_2|=d|t|>0.$$

The unweighted ordered rectangle count restricted by $(n_1,n_2)\ge Q$, $Q\ge1$, is

$$R_2\big((n_1,n_2)\ge Q\big)\ll q^{2.500+o(1)}(1+H/\sqrt Q).$$

In particular $Q=q^{.450}$ pays $2.665$, without assuming the two $d$'s have a common factor. Write $\boldsymbol\delta=r v$ with $v$ primitive, $R\le r<2R$ dyadically. Fix the first incidence and a divisor $e\mid n_1$, $e\ge Q$, and require $e\mid n$ on the second. The divisor choices cost $q^{o(1)}$. Set $k_0=(x_1,x_2)$ and $L=(x_2/k_0)v_1-(x_1/k_0)v_2\ne0$. Then $n=rk_0|L|$, and $d\mid L$ since $(d,rk_0)=1$ by endpoint primitivity. Group the second candidates by

$$e_k=(e,k_0),\qquad e_r=(e/e_k,r),\qquad e'=e/(e_ke_r).$$

There are subpowerly many such splittings. We have $e'\mid L$ by valuations, not by assuming that the factors are relatively prime. Also $e_k\mid h_1 h_2$: At each prime at least one label is a unit. The two smooth $h_i$ therefore cost $q^{.665+o(1)}/\sqrt{e_k}$ choices by counting $h_1h_2/e_k\le q^{1.330+o(1)}/e_k$ and splitting.

With these $h_i$ fixed let $B=(H/R)^2<d$. If $e'<B$, take a smooth divisor $f$ of $d/(d,e')$ crossing $B/e'$ within a factor $X$; otherwise take $f=1$. This crossing exists since $d>B$. Now $e'f\mid L$ by the least common multiple identity. The direction lattice has index $e'f$ because the two reduced coefficients are coprime. In the centred box of radius $H/R$ there are $O(1)$ primitive points per $f$ by the same area argument. The divisor choices cost $q^{o(1)}\sqrt{\max(1,B/e')}$. After fixing $v$, recover $d\mid L$ at subpower cost.

Take $bx_1\equiv qv_1\pmod d$ and write $r=e_r j$, $c=be_rj+di$. Then $(j,i)=1$ since $(r,c)=1$. If there are any lifts then $e_r\le 2R$. Choose a divisor of the smooth $c$ crossing $2R/e_r$ within a factor $X$, possible since $c>Z/X>2H$. This has $q^{o(1)}\sqrt{2R/e_r}$ choices. Writing $f_c$ for this divisor, the congruence $be_rj+di\equiv0\pmod{f_c}$ has index $f_c$ since $(d,c)=1$. The centred body $|j|\le2R/e_r$, $|be_rj+di|\le Z$ has area divided by index $O(Z/d)=O(X)$; again there are $q^{o(1)}$ primitive points. The $y_i$ are forced. Thus the cost per first incidence in this box is at most

$$q^{.665+o(1)}\left(\frac H{\sqrt{Re}}+\sqrt{\frac R{e_ke_r}}\right).$$

For the symmetric gcd condition count the column with larger $r$ first, at cost at most twice the resulting bound. This need not be the order defining the angular statistic $S$: No restriction on $S$ is used. The [first-incidence estimate](gap-direction-rectangles.md) is $q^{1.835+o(1)}/\sqrt{R_1}$ for $R_1\le r_1<2R_1$. Now $R\ll R_1$ absorbs the second term, and $e\ge Q$ gives the displayed unweighted result after summing boxes.

**Asymmetric weighted version.** One can instead prescribe any family of $q^{o(1)}$ integers $Q\le e\le q^{O(1)}$ per first incidence, *before* inspecting the second cofactors, and count partners with $e\mid n_2$ for at least one of them. Use the per-incidence bound without swapping, $R\le H$, and at most $q^{1.055+2\sigma+o(1)}$ first incidences. The price after dividing by $DM$ is

$$q^{1.720+\sigma-\mu+o(1)}(H/\sqrt Q+\sqrt H),\qquad M=q^\mu.$$

For example $Q=q^{.113}$ costs $q^{1.3885+o(1)}$ at the top degree and popularity. Throughout $\mu\ge.608+\sigma-o(1)$, $Q=q^{.227}$ suffices for this same bound. The smaller threshold is **not** uniform. The dictionary can include the divisors of $n_1$, or all $e\le ZW$ supported on primes at most $\log q$. The latter family has size $q^{o(1)}$: At any fixed Rankin exponent $0<\alpha<1$, its size is at most $(ZW)^\alpha\exp(O_\alpha((\log q)^{1-\alpha}))$, and then let $\alpha\downarrow0$. Consequently the remaining $n_2=d_2|t_2|$ can be required to have full part on these small primes below $Q$, including multiplicities. This is not the assertion that $t_2$ has a polynomially large prime divisor.

**Next test.** Neither cut prices a typical separated partner whose $n_2$ misses the prescribed divisors and whose forced $y_1y_2$ spreads its prime factors. For the top degree, the cofactor budget leaves a target below $q^{.333}$ partners per fixed cofactor pair on average at the $q^{.998}$ per-list target. Try to count the dispersed forced-output pairs there using the additional requirement that their recovered row actually completes with a smooth $c,d$; the output slope modulo $q$ already entered the strip index and cannot be charged again. The masks and the divisibility cuts pay only for their own pairs in the pair-to-edge comparison. No unrestricted large-$S$ estimate, all-gcd saving, or fixed-window conclusion follows.

**After Work:** The [one-product progression cut](spaced-product-cut.md) prices the mixed term for all $d$, not just partners with both products on the structured support. The bounded-common-step cap benchmark and its limits are in [the common-weight note](common-product-weight.md). At $e=q^{.1375+o(1)}$, one prescribed product residue even on the full interval costs at most $q^{.98625+o(1)}$ actual partners per first incidence, irrespective of $(d,e)$. Do not sum this saving over all classes. The dispersed smooth-completion test above is still open.
