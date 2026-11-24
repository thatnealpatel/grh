# Common prime laws for two-term masks and nearby pairs at depth $1.95$

**Decision.** At $c=39/20$, the rational **regional law** is compatible with the zero second-order answer at $3t$ for each scalar mask in the following union. Write the mask as $H(x)=ae^{isx}+be^{i(s+d)x}$, where $a,b,s\in\mathbb R$ and $d\ge0$ (order the shifts first).

| Mask parameters | Certified scope |
|---|---|
| Same sign and $|a-b|\le (|a|+|b|)/20$ | $|s|\le1/20$, $7/8\le d\le 11/5$ |
| Same sign and $|a-b|\le (|a|+|b|)/20$ | Every $s$, $d\ge11/5$ |
| Either sign, arbitrary ratio | Every $s$, $d\ge28$ |
| One effective term, including a coincident pair | Every real shift |

A **different, hard-pair law** is compatible with the zero answer for every $H=e^{isx}(1+qe^{idx})/(1+q)$ with

$$-1/20\le s\le 7/20,\qquad 7/8\le d\le43/40,\qquad 27/50\le q\le61/100.$$

It also admits **one completion per pair** making both second answers zero whenever $(s,d)$ is within $1/2500$ coordinatewise of either $(0,1)$ or $(4/25,1)$. It covers the last three rows of the regional table as scalar masks as well; the first row is not claimed for it.

Each law keeps the strict failure mean, all first translates at both heights, and the zero higher answers at orders two through ten at $t$. The same prime law works for all masks in its stated scope. At $3t$ the shallow conditional law can depend on the requested mask or pair; there is no one completion asserted for the union of pairs or for the whole scalar region. This is a result for the fixed-spline common-law comparison, not arithmetic realizability, actual zeros, or RH/GRH.

## Primal data and unchanged constraints

Use the [existing comparison](single-shift-10-2.md#matching-with-one-shift-at-a-time) and its sign convention. In each table, a row is an integer knot followed by pairs $(10^8X,10^8p)$ for $X=\cos\theta$ with probability $p$. The [regional table](two-term-10-2.txt) has 228 right-continuous slabs, knots encoded as $64z_j$, and $X=0$ before $-8$. The [hard-pair table](hard-pair-10-2.txt) has 416 slabs, knots encoded as $128z_j$, and $X=0$ before $-12$. The last slab starts at $16$ and extends to infinity in both. Form $A=\mathbb E X$, $B=\mathbb E(4X^3-3X)$, and $U=\mathbb E\sqrt{(1+X)/2}$ slabwise. For $Y=A,B$, set

$$ w=\tfrac12+ix,\qquad G_Y(x)=\frac{\sum_j e^{-z_j/2}\Delta Y_j e^{iz_jx}}{w},\qquad d\mu=\frac{dx}{2\pi |w|^2}. $$

The [checker](check-two-term-10-2.py) verifies the atom ranges and exact probability sums, then rigorously checks:

| Quantity | Regional law | Hard-pair law |
|---|---:|---:|
| $\int z_+e^{-z}U(z)\,dz-8/9$ | $>1.50498\cdot10^{-6}$ | $>3.11082\cdot10^{-8}$ |
| $\|G_A\|_\infty<C_1/(2\cos(\pi/12))$ | $<.618660$ | $<.6186603$ |
| $\|G_B\|_\infty<C_1$, where $C_1=\cosh(c)/3$ | $<1.195160$ | $<1.195160$ |

The cap proof is Taylor bisection on $[0,64]$, reflection by conjugation and a jump-sum tail as in the one-shift certificate. The first cap permits its twelve-angle law at $t$, so the first moment there is $-G_A/C_1$ and moments two through ten vanish. At $3t$ use first moment $m=-G_B/C_1$. Plancherel identifies these first moments with the prime answers for every first translate, and the estimates for the limiting higher prime answers are unchanged. Both shallow laws put equal depth mass at $\pm c$.

## Exact scalar criterion

Fix $x$ and $H(x)\ne0$, and rotate the circle by $e^{i\arg H(x)/2}$ so the first moment becomes $n=e^{i\arg H(x)/2}m(x)$. The vertical and horizontal chords through $n$ minimize and maximize $\Re\mathbb E V^2$ among unit circle random variables $V$ with mean $n$: nonnegative variance of the real coordinate proves the lower bound $2(\Re n)^2-1$, and nonnegative variance of the imaginary coordinate proves the upper bound $1-2(\Im n)^2$. Choose the two endpoint probabilities to preserve $n$. Multiplying by $|H|$ and rotating back, the unrotated conditional interval for $\Re(H\mathbb E V^2)$ is centered at $\Re(Hm^2)$ with radius $|H|(1-|m|^2)$. These laws can be chosen measurably, using any first-moment-preserving chord at $H=0$. Integrate the two extreme laws over $\mu$; a constant mixture attains zero exactly when

$$F(H)=\int|H|(1-|m|^2)\,d\mu-\left|\Re\int Hm^2\,d\mu\right|\ge 0.$$

All nonzero fixed-spline shift factors and the common order-two sign or scaling are absorbed into $a,b$; equivalently the coefficient of $(z+s)_+$ contributes $e^{s/2}$ times that coefficient at frequency $s$. The checker works after normalizing $|a|+|b|=1$; zero masks impose no constraint.

## Enclosing the criterion

Let $S(t)=\Re\int e^{itx}m^2\,d\mu$ and $E(t)=\int\cos(tx)|m|^2\,d\mu$. With $\beta_j=e^{-z_j/2}\Delta B_j/C_1$ and the [one-shift kernels](single-shift-10-2.md#matching-with-one-shift-at-a-time),

$$\begin{aligned}
S(t)&=\sum_{j,k}\beta_j\beta_k(1+u_++u_+^2/2)e^{-|u|/2},& u&=z_j+z_k+t,\\
E(t)&=\sum_{j,k}\beta_j\beta_k(2+|v|)e^{-|v|/2},&v&=z_j-z_k+t.
\end{aligned}$$

The kernels are evaluated by prefix sums at exact rational arguments. Write $V_0=1-E(0)$, the total capacity, and $T=\int x^2|m|^2d\mu=-E''(0)$. The explicit kernel gives $T$ by replacing $(2+|v|)$ with $(1/2-|v|/4)$ at $t=0$. Differentiation under the integral gives the uniform second derivative bound $T$ for both $S$ and $E$. Replay gives $(E(0),T)$ approximately $(.5410026131,1.6751460952)$ for the regional law and $(.5321900838,1.6536241446)$ for the hard-pair law.

Same-sign normalized masks have $a=(1+\eta)/2$, $b=(1-\eta)/2$ after common sign removal. Since

$$|a+be^{idx}|^2=\cos^2(dx/2)+\eta^2\sin^2(dx/2),$$

the capacity is at least $C(d)=\int|\cos(dx/2)|(1-|m|^2)\,d\mu$ and the largest price over $|\eta|\le1/20$ is $(|S(s)+S(s+d)|+|S(s)-S(s+d)|/20)/2$. This sufficient lower bound need not be sharp for a given unbalanced mask. Compute $C$ with

$$C(d)=\frac2\pi\left[V_0+2\sum_{k\ge1}\frac{(-1)^{k-1}}{4k^2-1}(e^{-kd/2}-E(kd))\right].$$

For all $d\ge7/8$, cutting at $k=140$ incurs absolute error $<9.487\cdot10^{-22}$ for the regional law and $<5.253\cdot10^{-21}$ for the hard-pair law. In fact $|z_j-z_k|\le D$, where $D=24$ or $28$ respectively, so for $u>D$ one bounds $|E(u)|$ by $(\sum_j|\beta_j|)^2(2+u+D)e^{-(u-D)/2}$, and sums a geometric envelope on the omitted terms. The finite series has second derivative bounded by $(4/\pi)\sum_{k=1}^{140}\frac{k^2}{4k^2-1}(e^{-7k/16}/4+T)$.

Each smooth signed-price and endpoint-$\eta$ branch on an $(s,d)$ rectangle is certified by its four corner gaps: subtract the Fourier tail and the sum of the two chord errors $M h^2/8$, where $M$ bounds the second derivative in the relevant coordinate and $h$ is that side length. Taking the corner worst price simultaneously handles all four branches; there is no interpolation through an absolute-value cusp. Dyadic subdivisions check 291 boxes for $[-1/20,1/20]\times[7/8,11/5]$ and 5254 for $[-15,5]\times[11/5,10]$. The same checker covers the hard-pair law on the second rectangle in 4692 boxes. Each normalized gap is $>10^{-5}$.

### Unbounded shifts and gaps

On a compact interval, the checker bounds the suprema of $|S|$ and $|E|$ by endpoint maxima on a grid plus the chord error $Th^2/8$. On the tails, $S$ is a pure exponential to the left of $-32$ and an exponential times a quadratic to the right of $-2z_0$; $E$ is even and an exponential times a linear polynomial to the right of $D$. The right polynomials are recovered at offsets $0,1,2$ (or $0,1$) and bounded using $v^j e^{-v/2}\le(2j)^j$ for $j>0$. For the regional law, valid upper bounds for the suprema of $|S|$ on all shifts, $|s|\ge5$, and $|s|\ge14$ are $.457331,.049352,.000494$, and for $|E|$ on $t\ge10$ and $t\ge D$ are $.002989, .000003171$. The hard-pair law gives $.450588,.049442,.000527$ and $.003363,.000000733$, respectively. Use the checker's enclosed bounds in the following tests.

* For one translate use $V_0-\sup|S|>.001$; a coincident pair collapses to one translate or zero.
* For $11/5\le d\le10$, if $s\notin[-15,5]$ both translates lie outside $(-5,5)$, so the price is at most $S_5=\sup_{|t|\ge5}|S(t)|$. Use $|\cos(dx/2)|\ge\cos^2(dx/2)$ to lower bound $C$ by $(V_0-\sup_{t\ge11/5}|E(t)|)/2$.
* For $d\ge10$, one translate lies outside $(-5,5)$, making the near-balanced price at most $[(1+1/20)S_{\rm all}+(1-1/20)S_5]/2$. Since $2\sum_{k\ge1}(4k^2-1)^{-1}=1$, the capacity lower bound is $(2/\pi)(V_0-e^{-5}-\sup_{t\ge10}|E(t)|)$.
* For $d\ge28$, either coefficient can be the larger in absolute value. Factor its exponential and sign, and denote the resulting coefficients by $a$ and $b$, where $a\ge1/2$ and $|b|=1-a$. The capacity is at least $aV_0-|b|\,|e^{-d/2}-E(d)|$ by taking the real part of the modulus and integrating. The price is at most $a S_{\rm all}+|b|S_{14}$ since one shift has size at least $14$ and $a\ge|b|$. The lower bound for the gap is therefore $(V_0-S_{\rm all}-e^{-14}-\sup_{t\ge D}|E(t)|-S_{14})/2$.

All tail inequalities give $F(H)>10^{-5}$ on their stated normalized domains, taking a coincident pair in its reduced one-term or zero form (a zero mask has $F=0$).

## Exact pricing around the hard pair

The signed-dual probe (`ad45bf6fcdec9c61d2a5a052c547d50667f10365`, `.godel/bob/two-shift-dual-search.md`) singled out the shifts $(.16,1.16)$ and same-sign magnitudes $(.001018011621,.0005809242445)$. Treating the decimals as exact, its normalized gap is **negative for the regional law** ($-.00281782331764680\ldots$), but **positive for the hard-pair law** ($+.00242547753881444\ldots$). Each value has binomial truncation error at most $1.289\cdot10^{-19}$ in addition to the outward-rounded arithmetic enclosure. The negative sign is an exact failure of one prime law, not a dual separator.

For a normalized positive mask with $0\le q<1$, let $u_j=\binom{1/2}{j}q^j$, $c_k=\sum_{j=0}^{n-k}u_j u_{j+k}$, and $R(y)=e^{-|y|/2}-E(y)$. Expanding $|1+qe^{idx}|=|(1+qe^{idx})^{1/2}|^2$ and truncating the square-root series gives the approximate capacity

$$C_n(d,q)=\frac{c_0 V_0+2\sum_{k=1}^n c_k R(kd)}{1+q}.$$

The square-root series error is at most $\delta=q^{n+1}/(1-q)$, since its binomial coefficients have modulus at most one. With $\delta<1$, squaring and dividing by $1+q$ costs at most $\delta(2/\sqrt{1+q}+\delta/(1+q))\le3\delta$ uniformly, hence also after integration against $v\,d\mu=(1-|m|^2)d\mu$, of mass at most one. Subtract the actual normalized price $|S(s)+qS(s+d)|/(1+q)$.

For the full hard-pair box, use $n=80$ at each ratio endpoint, mesh $1/80$ in $s,d$ and mesh $1/100$ in $q$. Treat the two signed-price branches separately. For each fixed ratio endpoint, the two coordinate curvature bounds for the truncated signed gaps are

$$ M_s=T,\qquad M_d=\frac{2(1/4+T)\sum_{k=1}^n k^2|c_k|+qT}{1+q}.$$

Interpolate in $a=1/(1+q)$ between adjacent ratio endpoints using the **true** capacity. The integrand is the norm of the affine vector $a+(1-a)e^{idx}$, of length at least $2a-1$ and with $a$-derivative of norm at most $2$. Its norm has second derivative at most $4/(2a-1)$, so the signed gap has curvature bound $4V_0/\min(2a-1)$ in $a$; its signed center is affine. The checker subtracts both spatial chord errors, the $a$ chord error, and the capacity tail at every corner. The 3584 boxes give $F(H)>.00128914$ throughout. The ratio and shift normalization here does not let the prime law vary within the box.

## Simultaneous zeros for two specified translates

Fix $d=1$ and $s=0$ or $s=4/25$. To cover all real coefficient vectors, factor the sign and translate of the coefficient larger in magnitude, and denote its absolute weight by $a\in[1/2,1]$; the smaller weight is $1-a$. Check both orientations of $u=S(s)$ and $v_1=S(s+d)$ in the price.

* **Same signs, $1/2\le a\le.52$.** Use $C(1)$ as a capacity lower bound. The maximum of $|a u+(1-a)v_1|$ occurs at an endpoint.
* **Same signs, $.52\le a\le1$.** Use $C_{160}(1,(1-a)/a)$ and the binomial tail at the $.01$ mesh nodes, subtracting for each edge the chord error with curvature bound $4V_0/(2a_{\rm left}-1)$ on the two true signed branches.
* **Opposite signs.** Taking the real part in the integral gives capacity at least $aV_0-(1-a)R(1)$. Subtract either signed branch of $a u-(1-a)v_1$, and check the two endpoints $a=1/2,1$ of these affine tests.

The resulting lower bounds for normalized gaps, rounded down, are:

| Pair | Same sign | Opposite sign |
|---|---:|---:|
| $(0,1)$ | $.00250812$ | $.03181987$ |
| $(.16,1.16)$ | $.00233569$ | $.02077885$ |

These bounds extend to the claimed pair neighborhoods uniformly in the coefficients. Put $h=1/2500$ and $L=2/h$. If $|\Delta s|,|\Delta d|\le h$, the price changes by at most $2h\sqrt{E(0)T}$, using $|S'|\le\int |x||m|^2d\mu\le\sqrt{E(0)T}$. The capacity changes by at most $\tfrac12\int\min(h|x|,2)d\mu$: factor the larger coefficient and use $v\le1$. Splitting at $L$ bounds this loss by $[h\log(1+4L^2)/2+2/L]/(2\pi)$. After both losses the checker gives normalized gap $>.0009352$ in either neighborhood.

Here the scalar tests imply **joint** matching for each fixed pair, by the same compact-convex argument as for separated second shifts (`1e497434606f0c43204e1a8c060d9035f8be8fa3`, `.godel/bob/separated-second-shifts.md`). Pointwise the attainable second moments form the disk $m^2+v\{g:|g|\le1\}$. To see attainability of its circumference, take the mean-preserving chord through $m$ in direction $e^{i\theta}$. If the real displacement is $Y$, then $\mathbb E Y=0$ and $\mathbb E Y^2=v$ from unit norm, giving second moment $m^2+ve^{2i\theta}$. Mixing opposite second-moment directions gives any point in the disk measurably. Conversely $|\mathbb E(V-m)^2|\le\mathbb E|V-m|^2=v$ for $|V|=1$. The two real answers are the image of the complex unit ball in $L^\infty(\mu)$ under the weak-star-continuous affine map

$$g\longmapsto \big(\Re\int e^{iyx}(m^2+vg)d\mu\big)_{y=s,s+d}.$$

The image is compact and convex. Every real linear functional has a range containing zero by the all-coefficient scalar tests, so a separating functional for the vector zero cannot exist. This yields a single shallow law for the two answers of this pair, not for the four answers of the two pairs together. If required, replace $g(x)$ by $(g(x)+\overline{g(-x)})/2$; the real answers do not change.

## Replay and limits

From the repository root, with assertions enabled (SageMath 10.9):

```sh
sage .godel/bob/check-two-term-10-2.py
TWO_TERM_LAW=hard-pair sage .godel/bob/check-two-term-10-2.py
```

Both commands passed in the dispatch workspace. They check the rational tables with exact rational inputs and 128-bit outward-enclosing balls. Table SHA-256 digests in regional, hard-pair order:

```
396c8a37cac805d51634522b2204dbd17d9239b632f570c2493835168a48e3d1
f8eb1b3ba222cc1884685c2a8ad2b32d7abe47fac5edae8ae6ec50c133c3d713
```

The tables were discovered by finite sampled conic margin searches in the slabwise convex hull of $(X,4X^3-3X,\sqrt{(1+X)/2})$. For a signed mask the integrand quadratic is positive semidefinite:

$$|H|\,|m|^2+\sigma\Re(Hm^2)=2\big(\Re[\sqrt{\sigma H}\,m]\big)^2.$$

The searches used midpoint spacing $1/64$, integrations over $[0,64]$ (regional) or $[0,128]$ (hard pair), and exchange of spectral-cap and convex-hull cuts. The regional fit included sampled directions from its intended domain, whereas the hard-pair fit imposed only the two signed constraints of the hard mask, not the resulting neighborhood or joint pair claims. The retained atom tables, not the optimizer or its quadrature, are the checker inputs. Optional discovery commands (numerical, not certificates) use [the discovery script](search-two-term-law.py), Python 3.14.7, NumPy 2.5.5, SciPy 1.18.1, and Clarabel 0.11.1:

```sh
export OPENBLAS_NUM_THREADS=1
s=.godel/bob/search-two-term-law.py
python "$s" --scope regional --refine --steps 12 --mean .0000015 --out /tmp/two-term-region
python "$s" --scope hard-pair --refine --left 12 --atoms 192 --steps 13 \
  --mean .000000025 --fpad .0000007 --seconds 25 --out /tmp/two-term-hard-pair
```

The regional run reached its 12-round limit (65 seconds per solve), with final reported residuals of order $10^{-8}$–$10^{-7}$. The hard-pair run used 416 slabs, a per-solve limit of 25 seconds, relative and absolute tolerance targets $10^{-8}$, and a two-thread `faer` solver. It reconstructed the table during repeated `NumericalError` rounds with primal/dual residuals $5.59\cdot10^{-7}$ and $3.46\cdot10^{-8}$, respectively, and sampled normalized-by-mask-mass margin about $.002739$. The rational reconstruction rounded atoms and probabilities to $10^{-8}$ and exactly renormalized each slab; the final spectral and mean slack were measured by the checker, not inferred from residuals. Earlier coarser hard-pair-only and joint fits did not find a positive margin, and do not furnish an impossibility bound.

Neither table settles arbitrary two-term masks. The companion gap-window certificate (`47530f8db6b3dd7da96234222fc69c22a61951ee`, `.godel/bob/two-gap-window.md`) already excludes opposite signs and gaps outside $(3/16,4)$ using the 152-slab law. The new information is in the interior of that window, including two neighborhoods of simultaneous zeros; the large-gap tests above give domains of the new tables, not better gap constants for pairs. A useful next test is to compare the three laws on the remaining potentially separating cells, retaining the full ratio rather than assuming the balanced capacity bound is sharp. If a cell still lacks a witness, optimize there with the exact signed constraints and retain a distinct common law only if its certified scope adds something.
