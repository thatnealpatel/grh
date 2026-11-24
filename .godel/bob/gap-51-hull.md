# A balanced mask rejects the old mixtures, not the pair

In the [half-gap comparison](half-gap-mixture.md) at $c=39/20$, fix shifts $s=1/20$ and $s+d=14/25$, with $d=51/100$. The equal-weight mask cannot have zero answer for **any constant mixture of the six profiles below** in the capped first-representer construction with failure mean at least $8/9$. Nevertheless, a change to the angular law on a single negative interval permits **both zero answers simultaneously**, for every pair with $1/2\le d\le 13/25$ and every real $s$. The second law at $3t$ may depend on the pair. The previous results now restrict a two-term scalar separator to like signs and $13/25<d<4$. None of this supplies signed measurements at actual failures.

## An upper bound on the whole old family

Use the notation $G_A,G_B,C_1,C_{10},m,\mu$ of the [single-shift construction](single-shift-10-2.md). The simplicial weights $x_i$ mix the underlying laws with the same weights on every slab. In order, the vertices are single-shift $(10,2)$, regional $(10,2)$, hard-pair $(10,2)$, radial $(9,9)$, step $(11,1)$, and the atom at zero. This includes the raw-cutoff mixture. Put $u_i=\operatorname{mean}_i-8/9$, $g_i=G_{A_i}(0)/C_1$, $a=C_{10}/C_1$. Retain only $u\cdot x\ge0$ and $g\cdot x\le a$ from the construction's constraints: The second is one side of its frequency-zero cap. We do **not** need each vertex to meet either constraint, or to know that this cap is necessary for unrelated shallow constructions.

Write $H=e^{is\xi}(1+e^{id\xi})/2$, $m_x=-\sum_i x_iG_{B_i}/C_1$. The signed upper bound on capacity minus absolute center is

$$J(x)=\int\big[|H|-|H||m_x|^2-\Re(Hm_x^2)\big]\,d\mu.$$

The two subtracted terms together equal $2|H|\Re(e^{i\arg(H)/2}m_x)^2$ (zero at $H=0$). Thus $J$ is a concave quadratic on the simplex even where $m_x$ is not a circle mean. Negativity implies failure; positivity alone is not a simultaneous-matching certificate. For the original half-gap mixture the center is positive, and the actual normalized slack is $-.000210681678$ to within $2\cdot10^{-12}$.

Take $v=(52129715,0,46988009,880383,0,1893)/10^8$ and let $L$ be the affine tangent to $J$ there. Quadratic interpolation gives $L(e_i)=4J((e_i+v)/2)-2J(v)-J(e_i)$. For every feasible $x$,

$$J(x)\le L(x)\le L(x)+157.33448(a-g\cdot x)+458.21570\,u\cdot x.$$

The last expression is affine, so testing six vertices bounds the entire simplex. The [128-bit Sage checker](check-gap-51-hull.py) prices $J=C(d)-(S(s)+S(s+d))/2$ by the accepted jump kernels and the absolutely convergent cosine series. The geometric tail estimate in the half-gap proof with $N=256$ gives error below $10^{-12}$ per price; we add $7\cdot10^{-12}$ at each tangent evaluation. Rounded **up** in vertex order, the corrected upper bounds are $(-.00001740,-.0024084,-.00001772,-.00001315,-.10652,-.00001767)$. All are below $-1.2\cdot10^{-5}$. The checker uses the tabulated angular means, not the approximate surpluses or KKT conditions from the numerical fit. No claim about slab-dependent weights follows from this tangent.

## Escaping the bound without changing the failure surplus

Start with the half-gap mixture. On $-3/2\le z<-11/8$ replace $X$ by the endpoint law with $\Pr(X=1\mid z)=(1+A(z))/2$, the remaining mass at $-1$. Leave all other slabs alone. This is a common law for both harmonics, not a free change of the second representer: $\mathbb EX=A$ everywhere, and $B=A$ on the block because $4X^3-3X=X$ at both endpoints. Since $z_+e^{-z}=0$ there, the failure mean surplus is still $9.48562\ldots\cdot10^{-8}$. Thus neither the order-ten cap nor the failure mean needs to be bought back. The $B$ cap and the two-shift test **do** need fresh checks.

The [strip checker](check-half-gap-mixture.py) verifies $\|G_B\|_\infty<1.19<C_1$ by the all-frequency Taylor bound (87 finite boxes and a jump tail). It replays the original strip and applies the same signed chord estimates on $[-8-13/25,8]\times[1/2,13/25]$ to the modified law. All real coefficient directions pass, with normalized slack $>5\cdot10^{-6}$ on 169 rectangles, Fourier tail $<4.34\cdot10^{-60}$, and separate analytic bounds on the two outer shift ranges. Compact convex separation gives the simultaneous answers. The block was selected by numerical pricing; its validity needs neither the search nor a floating point optimizer. From the repository root run both `sage .godel/bob/check-gap-51-hull.py` and `sage .godel/bob/check-half-gap-mixture.py` with assertions enabled.

**Next test:** At $s=.07,d=.55$ the same checker gives balanced slack $<-.00044$ for the block law. Refining its coefficient mesh cannot work. Try negative-slab endpoint replacements on more than one interval, with $A$ and positive slabs fixed, pricing this balanced direction before fitting the others. Retest the changed $B$ cap and the full coefficient space before claiming another joint strip. For separation rather than matching, the six-weight tangent is insufficient: A bound must apply to slabwise laws or otherwise control their added freedom.
