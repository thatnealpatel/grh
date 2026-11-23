# Simultaneous modular output tests on a two-position list

Fix the first incidence and its constructed ordered list at $g=1$. Use the [row identification and recovery](shared-row-labels.md): $x_i=F_i h_i$, the labels are coprime, $(F_2,x_1)=1$, $W<F_i\le WX$, $h_i\le U=q^{.665+o(1)}$, and $x_i,y_i=q^{1.445+o(1)}$. The smooth column has $Z/X<c,d\le Z$, $Z=q^{1.055+o(1)}$. Write $r=c/d$ **in the field**. Both $y_i\equiv x_i r\pmod q$, and $t=(x_1y_2-x_2y_1)/q$ is an integer of absolute value at most $W=q^{.780+o(1)}$. Smooth counts up to polynomial height $D\ge1$ cost $q^{o(1)}\sqrt D$, and prime factors are at most $X\asymp(\log q)^2$. No real interval for the slope is used below.

## A cut that applies outside any prescribed dictionary

Put $P=q^{.880}$. Charge **every** partner on a cofactor pair $(h_1,h_2)$ if

* for some $z\in\mathbb F_q^\times$, $\|x_1z\|_q\,\|x_2z\|_q\le P$, or
* two distinct actual partners on this pair have the same $r$.

Here $\|\cdot\|_q$ is absolute least residue. Together these cost $q^{.995+o(1)}$. In the first test $z$ ranges over the whole punctured field, not a dictionary with one charge per $z$. In particular one can take $z=r-r_0$ for any other modular slope, even from a different cofactor pair. The discrepancies tested are $y_i-h_i F_i r_0$, not $y_i/h_i-F_i r_0$.

**Nonzero difference.** Dyadically box the nonzero least residues $v_i$ in $|v_i|\le B_i$, with $B_1B_2\le4P$. The vector $(h_1 v_2,h_2 v_1)$ belongs to the index-$q$ lattice $F_1 n_1\equiv F_2 n_2\pmod q$. Its box has relative area up to a constant $E=U^2 B_1B_2/q$. Write the vector as $jw$, with $w$ primitive in this lattice and $j>0$. Put $k_i=(j,h_i)$, $l=\operatorname{lcm}(k_1,k_2)$. Then $l\mid j$, $l\le U\min B_i$, and $h_i/k_i\mid w_i$. Count $w$ in the original box divided by $l$. Before enumerating it choose a smooth divisor $f$ of $(h_1/k_1)(h_2/k_2)$ crossing $\max(1,E/l^2)$ with overshoot $X$, using the whole product if too small. Split it as $f_1 f_2$ with $f_i\mid h_i/k_i$. The conditions $f_i\mid w_i$ multiply the covolume by $f$, since $q\nmid f$ and the congruence still has index $q$ after substitution. Relative area is $O(1)$ in the crossing case and $O(E/(h_1h_2))=q^{o(1)}O(B_1B_2/q)$ in the whole-product case, by $k_1k_2\le l^2$ and $h_i=q^{.665+o(1)}$. A centered planar box with this relative area contains subpowerly many base-primitive candidates: Use Pick's bound on their lattice hull in rank two, and at most two primitive vectors in rank one. Both coordinates are nonzero, so divisors recover the $h_i/k_i$. This argument includes exact parallelism; it never divides by a determinant quotient.

For given smooth $l$ there are divisor-cost choices of $k_i\mid l$, and $q^{o(1)}(1+\sqrt E/l)$ choices of $f$ and its split. Summing gives a cofactor price

$$q^{o(1)}\big(\sqrt{U\min B_i}+U\sqrt{B_1B_2/q}\big)\le q^{.605+o(1)}.$$

The first exponent is at most $.5525$. Multiply by the [full gap-square price](short-label-ratios.md) $q^{.390+o(1)}$ per qualifying pair, not by a count of short vectors. This works for all aspect ratios, including one residue larger than $W$.

**Equal slope.** Here $a_i=(y_i-y'_i)/q$ are integers of size $q^{.445+o(1)}$. The vector is nonzero by primitive row recovery. Its determinant $T=x_1a_2-x_2a_1=t-t'$ has size $\le2W$. It is nonzero: The primitive kernel has first coordinate $x_1/(x_1,x_2)\ge x_1/h_2=q^{.780+o(1)}$. Neither coordinate vanishes since $2W<\min x_i$. Use the preceding content sieve on $(h_1a_2,h_2a_1)$, now in $\mathbb Z^2$, in coordinates $(h_2a_1,T)$ of covolume $F_1$ (the coordinate map has determinant of absolute value $F_1$). The relative area parameter becomes $E=U q^{.445+o(1)}(2W)/F_1=q^{1.110+o(1)}$. Divisibility on the two **original** coordinates again multiplies covolume by $f$. Here $j\mid T$ gives $l\le 2W$, and $E/(h_1h_2)\ll1$. The same sum gives $q^{o(1)}(\sqrt W+\sqrt E)$ qualifying pairs, costing $.945$ after restoring the full fibers.

**Residual property.** The slope map is injective on the remaining actual partners of each cofactor pair. Moreover their two output residues are separated in product: Any two distinct columns on it have $\|y_1-y'_1\|_q\,\|y_2-y'_2\|_q>P$. Every translated cyclic output rectangle with product of diameters at most $P$ therefore holds at most one of them. The threshold from the nonzero-difference term is exponent $.886$ for $P$ at partner price $.998$. This is a packing conclusion, not an upper bound on the number of occupied rectangles by $q^{.333}$. For example, tiling the two output circles with rectangles of area $P$ costs order $q^2/P$ even before exploiting that the outputs lie on a modular line.

## Larger bands for the normalized outputs

In contrast, test $y_i/h_i$ in two cyclic intervals of radius $K=q^k$, one pair of centers per $d$. For $.880\le k\le.905$, the partner price is

$$q^{o(1)}Z(K/q)^{3/5}=q^{.455+.6k+o(1)}.$$

In particular $.900$ is allowed at price $.995$; the [single-band estimate](modular-complement-bands.md) at this radius costs $1.005$. This bound pays for the partners **in** the two bands, not all partners on the same denominators.

Choose a smooth divisor $f\mid c$ crossing $V=ZK^2/q^2$ with $V\le f\le C=XV$; it exists since $V<Z/X$. Write $g=c/f\le G=q^2/K^2$. After lifting each cyclic interval, $(g,u_1,u_2)$ lies in a translated box of half-widths $(G,K,K)$, and $d u_i\equiv fF_i g\pmod q$. These congruences have index $q^2$. Scale by $S=\operatorname{diag}(1/G,1/K,1/K)$ to get a determinant-one lattice. Write $\lambda_j$ for its successive cube minima, and $\tau$ for the shortest sup norm in its dual. Minkowski's second theorem gives $\lambda_1\lambda_2\lambda_3\asymp1$; fixed-dimensional transference gives $\lambda_3\tau\asymp1$ (cube and polar norms are equivalent here).

At fixed $d,f$, occupancy is $\le q^{o(1)}(1+1/\tau)$ uniformly in the translations. Indeed, if $\lambda_2\le2$, the usual lattice box bound $\ll\prod_j(1+1/\lambda_j)$ is $O(1+\lambda_3)$ by the product estimate. If $\lambda_2>2$, differences span at most a line. In a nonsingleton box the primitive line step has nonzero $g$ coordinate: A vertical difference must change some $u_i$ by at least $q>2K$. There are at most $2/\lambda_1$ parameter steps. Smooth $g$ along this nonconstant integer progression costs only $q^{o(1)}\lambda_1^{-1/2}$: On an interval of parameter length $D\ge1$, divide out the common gcd of step and initial value. Reduced smooth values up to $D$ cost $q^{o(1)}\sqrt D$; larger ones have a divisor in $(D/X,D]$ coprime to the reduced step and each divisor selects $O(X)$ parameters. Finally $\lambda_1^{-1/2}\ll\sqrt{\lambda_2\lambda_3}\le\lambda_3$.

For $\tau\le\eta\ll1$ (allowing any fixed constant upper cutoff), the dual supplies a nonzero integer tuple $(b,a_1,a_2)$ with

$$db+fA\equiv0\pmod q,\qquad A=F_1a_1+F_2a_2,\qquad |b|\le\eta q/G,\quad |a_i|\le\eta q/K.$$

Indeed the dual consists precisely of $S^{-1}(b,a_1,a_2)/q$ with this congruence. The $a_i$ cannot both vanish since $|b|<q$. Also $|A|<q$ by the label sizes, and $A=0$ would require a nonzero multiple of $(F_2,-F_1)$, too long. Thus $q\nmid A$, $b\ne0$, and $\eta\ge K/q$.

Here is a direct centered sieve for the dual count. **Fix $a_1,a_2$**. Smooth pairs $(d,f)$ admitting such a $b$ give $(db,f)$ in the index-$q$ lattice $n_1+A n_2\equiv0\pmod q$, in a centered box with relative area parameter $E=Z C\eta/G$. Write $(db,f)=jw$ with $w$ base-primitive. Now $j\mid f$ is smooth. For each $j\le C$ and $k_0=(j,d)\mid j$, sieve $w$ with a divisor of $(d/k_0)(f/j)$ crossing $\max(1,E/j^2)$ as above. The two split factors divide the respective coordinates of $w$. Even if the whole product is used, the relative area is $O(E k_0/(jdf))\ll X^2\eta/G=o(1)$. Both coordinates are nonzero. Recover $d/k_0$ from divisors of $w_1$, and $f=jw_2$. The bound per $j$ is $q^{o(1)}(1+\sqrt E/j)$, hence $q^{o(1)}(\sqrt C+\sqrt E)\ll q^{o(1)}\sqrt E$ in total since $Z\eta/G\gg1$ at $\eta=K/q$. No smoothness assumption on $b$, no primitivity of $(d,f)$, and no averaging over centers is needed.

Summing over $O((\eta q/K)^2)$ choices of $a$ gives at most $q^{o(1)} Z\eta^{5/2}$ exceptional $(d,f)$. The trivial count is $q^{o(1)}\sqrt{ZC}=q^{o(1)} ZK/q$. Dyadically sum the smaller count with weight $1/\eta$ for $\eta/2<\tau\le\eta$, balancing at $\eta=(K/q)^{2/5}$. This proves the asserted price including the ordinary term. Row identification means there is no cofactor multiplicity to put back.

**Scope of adaptation.** For fixed labels the envelope $q^{o(1)}\sum_f(1+1/\tau_{d,f})$ at each $d$ is independent of both centers. Thus a uniform budget of $q^{.003-\epsilon}$ simultaneous slots per $d$ at $.900$ costs $q^{.998-\epsilon+o(1)}$, even with whole-fiber choices. This is not a free budget per cofactor. If the multipliers vary with $d$, the centered dual sieve no longer has one fixed lattice for each $a$. Pointwise at $.900$ the full-width single-band bound is still $q^{.4775+o(1)}$ per $d$ for any one pair of unit multipliers: Ignore the second band and use $\sqrt{ZK/q}$. That only sums to $1.005$. The exceptional dual term, not the choice of translations, is where the fixed-label hypothesis enters.

## A narrower same-denominator pair target

Remove the full cofactor fibers in the first cut. On the remaining actual partners put $C_d=\{c\}$, $n_d=|C_d|$, $D=\#\{d:n_d>0\}$, and $N=\sum n_d$. On each ordered pair $c',c\in C_d$ write $z=(c-c')/d$ in the field. Let $P_*$ count only pairs satisfying **all** the following:

1. $\min_i\|x_i(c')z\|_q>q^{.880}$ (both old anchor discrepancies are large).
2. $\max_i\|F_i z\|_q>q^{.900}$ (at least one normalized discrepancy is larger still).

No cofactor is fixed across the two columns. The first test can be failed by at most $2B$, $B=q^{.4675+o(1)}$, numerators per anchor, by the pointwise single-band lemma at $.880$. The second can be failed by at most $E_d$ numerators per anchor, where $E_d$ is the center-independent dual envelope just proved at $.900$, with $\sum_d E_d\le q^{.995+o(1)}$. Here the centers $F_i c'/d$ vary with the anchor, **but the multipliers are the list labels**. Do not multiply an averaged one-slot saving by an uncontrolled anchor multiplicity. Instead subtract the local allowances before Cauchy-Schwarz:

$$ P_*\ge\sum_d(n_d-2B-E_d)_+^2,\qquad N\le 2BD+\sum_d E_d+\sqrt{D P_*}. $$

Thus the old $1.4685-\delta$ pair exponent would suffice on this smaller region, since $D\le q^{.5275+o(1)}$. This reduction charges the excluded full fibers only once at partner scale and does not claim that their pair multiplicities are small. It works also after omitting any partners paid for by a prescribed dictionary. Nothing here bounds $P_*$ from above.

**Next test.** For such same-$d$ pairs use the fact that the ordinary differences $c-c'$ and $y_i(c)h_i(c')-y_i(c')h_i(c)$ satisfy

$$d\,[y_i(c)h_i(c')-y_i(c')h_i(c)]=F_i h_i(c)h_i(c')(c-c')-q[\delta_i(c)h_i(c')-\delta_i(c')h_i(c)] .$$

In both equations the rightmost bracket has size $O(HU)$, not the product-output scale. Try to count admissible lifts of these two brackets for fixed $c-c'$ with the same $d$ and smooth cofactors, retaining both large-discrepancy tests. A count after summing over $c-c'$ and all anchors must be below $q^{1.4685}$ by a fixed power; charging a free anchor per lift will not suffice. The unrestricted average, the all-gcd estimate, and the fixed-window conclusion remain open.
