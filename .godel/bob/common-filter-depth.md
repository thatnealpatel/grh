# Depth 1.220 at the first height, and a ceiling at 1.226

How far can one move the [one-height packet](filtered-one-height-packet.md) by changing the prime weight but still paying the absolute joint modulus for shallow zeros? Depth $1.220$ works. Depth $1.226$ cannot be paid from the original angular mean by this method, even with an arbitrary real radial weight and no inflation for strip positivity. The lower and upper certificates use different witnesses. The upper one is not a model of zeta zeros.

## A filter that pays for a deeper signed census

Use the notation and the real high-endpoint failure hypothesis of the linked test: $R=(9/5)\log q$, $V=R^2$, $D=\log V$, $t=2q^{3/5}$, $b=\beta-1/2$, $d=bD$, $x=\gamma-t$, $w=\beta+ix$, $g(w)=\exp(1-\cos(\epsilon w))$, and $G=g(1)$. Let $H$ take the nine values $j/10$, $-5\le j\le3$, with probabilities $(1,4,8,12,15,16,17,17,10)/100$ in order. Put

$$ A(w)=\mathbb E e^{Hw},\quad N(z)=A(1/2+iz)A(1/2-iz),\quad s=.50001,$$
$$ Q(w)=V^{w-1}g(w)A(w)^2/w^2,\qquad E(z)=4s^2 N(z)/(s^2+z^2). $$

For each of the following two rows, fix $\epsilon>0$ sufficiently small and then take $q$ sufficiently large. At a failure the reflected statistic satisfies

$$ S(c)=\sum_{d>c,\ 1.5/D<|x|\le (2/\epsilon)\log D}
 \left[-(1+e^{-2d})\Re Q(w)-\frac{2G\cosh c}{R}\Re E(x+ib)\right]>m. $$

| Scaled depth $c$ | Net charge $m$ |
| --- | --- |
| $1.216$ | $.0021$ |
| $1.220$ | $.00025$ |

In particular the latter annulus contains a right zero with multiplicity counted in the sum. The two rows use the same residue and envelope, but different budget factors. Neither row gives an upper bound on the old statistic.

**Prime price.** Let $L=H_1+H_2$ for independent copies of $H$, and $f(z)=\mathbb E(z+L)_+$. These are seventeen cutoffs at a single height, not seventeen heights. For $u=|\cos((t/2)\log p)|$, $z=\log(V/p)$, and $d\mu=V^{-1}\sum_p(\log p)\delta_z$, apply Cauchy-Schwarz to the *original* $\int z_+u\,d\mu\ge 8/9-o(1)$. As in the three-cutoff proof, $f$ is positive on $[0,\infty)$, PNT applies to the fixed radial weights (not to the phases), and the prime price $\int f(2u^2-1)\,d\mu$ is at least $P-o(1)$, where

$$ \mathcal L=\int_0^\infty z^2 e^{-z}/f(z)\,dz,\qquad P=2(8/9)^2/\mathcal L-\mathbb E e^L>.5553717. $$

The checker partitions at the knots $-L\ge0$. On each resulting interval $f(z)=m_0(z+v)$, where $m_0$ and $m_0 v$ are the mass and first moment of the active shifts. The integrated tail primitive used at each endpoint $a$ is $e^{-a}(a+1-v)+v^2 e^v\Gamma(0,a+v)$ before division by $m_0$; only differences on the actual pieces are used. This calculation does not require that the Cauchy-Schwarz optimizer have $u\le1$.

**Strip price.** On the line $N(x)=|A(1/2+ix)|^2$, so $E(x)\ge |A(1/2+ix)^2/(1/2+ix)^2|$. Write $N(z)=\sum_{k=0}^8 r_k\cos(kz/10)$ by grouping the probability products with index difference $\pm k$. All $r_k$ are nonnegative. By harmonicity and uniform inverse-square decay on the closed strip it suffices to check $\Re E(x+i/2)\ge0$ for $x\ge0$ (symmetry handles the other boundaries, and the vertical end errors tend to zero). After removing positive factors this is

$$ \Re N(x+i/2)+\frac{x}{s^2+x^2-1/4}\Im N(x+i/2)\ge0. $$

For $0<x\le1$ use $\cos(kx/10)\ge1-(k/10)^2/2$, $|\sin(kx/10)|\le kx/10$, and the skew coefficient $\le1/x$; the checker verifies the resulting strict bound. At zero $N(i/2)>0$. For $x\ge1$, reduce $x/10$ modulo $2\pi$ to $\theta\in[0,2\pi]$. The coefficient is at most $1/\max(1,10\theta)$. Ball enclosures on subdivided intervals prove $\Re N(10\theta+i/2)>|\Im N(10\theta+i/2)|/\max(1,10\theta)$ throughout the period. In particular negative deep budgets do not invalidate the shallow bound.

The pole budget is

$$ I=\frac1{2\pi}\int_{\mathbb R} E(x)\,dx=2s\sum_k r_k e^{-sk/10}<.904476. $$

The [translated full-budget proof](filtered-one-height-packet.md#a-positive-budget-on-the-full-strip) applies: Each cosine gives translated exponential Fourier tails with exponent $s>1/2$, so the Weil prime contribution is $O(1)$, and the gamma term divided by $R$ gives $I/3+o(1)$. By combining the finitely many smoothed tent identities with weights $\Pr(L)$ and common denominator $V$, the zero residue is precisely $Q$ on $\beta\ge1/4$, up to the same total $O(\epsilon)+o_\epsilon(1)$ errors as in the linked proof. The shifts are fixed and bounded. The analytic multiplier $g(w)A(w)^2/w^2$ and its derivative on $1/4\le\Re w\le1$ are $O_\epsilon((1+x^2)^{-1})$. Thus the [reflection estimate](filtered-reflection-price.md) applies unchanged, even for a missing far-left mirror. On $|b|\le c/D$ the pair costs at most its two budgets up to summable $o_\epsilon(1)$ total error, by comparing with the line modulus before multiplication by $g$. The center has nonpositive residue charge since $A(\beta)>0$ and the phase is $Dx+O(1/D)$ there; the smoothed outer tail costs $o_\epsilon(1)$. This proves $S(c)\ge P-GI\cosh(c)/3-O(\epsilon)-o_\epsilon(1)$. Before smoothing the two margins exceed $.00212$ and $.00026$, respectively. There is no effective conductor threshold here.

## Why not optimize the cutoffs to reach 1.226?

Here is the precise limitation. For any real radial prime weight $f$ let $F(z)=e^{-z/2}f(z)$ and assume $F,\widehat F\in L^1(\mathbb R)$, where $\widehat F(x)=\int F(z)e^{-ixz}dz$. Price the critical-line joint modulus at $I_0(f)=\|\widehat F\|_1/(2\pi)$. This includes signed linear combinations of shifted ramps: The transform of $e^{-z/2}(z+L)_+$ is $e^{(1/2+ix)L}/(1/2+ix)^2$. In particular the price is for the sum, not for each term separately. For the preceding comparison take the unsmoothed limiting modulus, the price used before the fixed-small-$\epsilon$ errors. An envelope majorizing this modulus on the line only increases its integral.

There exists a single $a:\mathbb R\to[-1,1]$, independent of $f$, with

$$ \int_0^\infty ze^{-z}\sqrt{(1+a(z))/2}\,dz>8/9,\qquad
 \left|\int_{\mathbb R} f(z)a(z)e^{-z}dz\right|\le .6167\,I_0(f). $$

Indeed take $a=0$ before $-12/8$. Starting at $z_j=j/8$, $j=-12,\ldots,6$, use the successive constant levels

```
3248, -32580, 81424, -31044, -100000, 29735, 100000, 74329, -100000,
-100000, -100000, -100000, -71726, 7164, 45180, 59132, 63442, 64892, 60720
```

divided by $100000$, extending the last level to infinity. This is an admissible angular law: Choose a phase with $|\cos(\theta/2)|=\sqrt{(1+a)/2}$, so $\cos\theta=a$. Integrating $ze^{-z}$ over each nonnegative slab certifies the strict mean. Write $J=e^{-z/2}a(z)$. The jumps $\Delta a_j$ give

$$ \widehat J(x)=\frac{\sum_j\Delta a_j e^{-z_j/2}e^{-ixz_j}}{1/2+ix}. $$

The numerator has even modulus and period $16\pi$. Folding to $[0,8\pi]$ can only decrease the denominator modulus. The checker proves $|\widehat J|<.6167$ there by enclosing the squared trigonometric polynomial and the squared denominator on whole intervals, not merely at grid points. Fourier inversion of $F$ and $J\in L^1$ now bound $|\int FJ|$ by $I_0(f)\|\widehat J\|_\infty$. The paired integral is absolutely convergent since $J$ is bounded. This proves the assertion simultaneously for all these weights.

Since $\cosh(1.226)/3>.6167$, the angular mean alone cannot certify a positive prime-price margin at that depth against this absolute shallow price, even if the strip envelope is free of inflation. This does **not** preclude using signed shallow cancellation, a second height, or additional arithmetic information about the phase law. Unlike the [individually priced ceiling](dilated-harmonic-ceiling.md), the witness here applies to a joint first-height modulus; it does not treat further harmonics as first-height weights.

**Replay and decision.** Run [check-common-filter.py](check-common-filter.py) with SageMath's Python (without `-O`). The first-height filter now leaves a gap of less than $.006$ in scaled depth between a working price and the obstruction (the lower margin is strict at $1.220$). Further cutoff tuning alone cannot yield a substantial depth gain. At a candidate surviving the prime tests, the deeper census offers the alternative upper-bound target $S(1.216)\le .0021$ or $S(1.220)\le .00025$; apply the matching envelope and multiplier, not the old $.0018$ test to the smaller set. Nothing here supplies that arithmetic upper estimate or measures an exceptional conductor.
