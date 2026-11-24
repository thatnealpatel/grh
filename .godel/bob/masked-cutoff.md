# Improve the doubled-cutoff test without changing height

At a [real high-endpoint failure](long-cutoff-moments.md), even the **existing** smoothed $P_2$ has a stronger implication: $P_2\ge-.002$ forces a right zeta zero at scaled depth $d>1.574$. If using a new linear combination $Q_2$ of five translated copies of the same weight, $Q_2\ge-.0062$ forces $d>1.60$. Both conclusions are at $t=2q^{3/5}$ in the window $|x|=|\gamma-t|\le J=(2/\epsilon)\log D$, center included, with $R=(9/5)\log q$, $V=R^2$, $D=\log V$, and $d=D(\beta-1/2)$. Fix sufficiently small $\epsilon>0$ and then take $q$ sufficiently large. Neither price predicts the measured value.

The improvement comes from spending the original angular mean on a shifted first weight with a **real nonnegative** multiplier on the critical line. Unlike an absolute envelope on the strip, this does not discard the zero phase. There are two distinct prices: One for comparing a masked first measurement to an unmasked second, and one when the mask is common to both.

## Five shifts and their first price

Set $h=1/5$, $s_l=lh$, $r_l=(3-|l|)/9$, and $A_l=r_l e^{-s_l/2}$ for $-2\le l\le2$. Use exactly the $B_j$, $k_\epsilon$, and normalizations of [the long-cutoff identity](long-cutoff-moments.md#the-arithmetic-observable). Define $Q_j$ by replacing $B_j(y)$ by $\sum_l A_l B_j(y-s_l)$ in $P_j$. **Convolve the whole translated weight**, even for $j=2$. Multiplicativity of the bilateral transform inserts the factor

$$ L(w)=\sum_l r_l e^{s_l(w-1/2)},\qquad H(x)=L(1/2+ix)=|1+e^{ihx}+e^{2ihx}|^2/9. $$

Here $0\le H\le1$, and $L$ and its first derivative are bounded throughout the contour strip $-1/4\le\Re w\le2$. In particular the contour and outer-zero estimates are unchanged up to constants. Translating the compact spline shifts the maximum endpoint by at most $2h$; the exponential convolution tail changes only by a fixed factor depending on $\epsilon$. The same truncation to primes $p\le V^{j+1/2}$ costs $o_\epsilon(1)$ for fixed $1/\epsilon>j$.

For $z=D-\log p$ put $f(z)=\sum_l A_l(z+s_l)_+$. At failure the unaltered datum is $\int z_+u\,d\mu\ge 8/9-o(1)$ with $u=|\cos((t/2)\log p)|$ and $d\mu=V^{-1}\sum_p(\log p)\delta_{D-\log p}$. Since $f>0$ on $[0,\infty)$, Cauchy-Schwarz, followed by PNT for the phase-free weights, gives

$$ Q_1\ge P-O(\epsilon)-o_\epsilon(1),\qquad P=2(8/9)^2/\mathcal L-\sum_l A_l e^{s_l},\qquad \mathcal L=\int_0^\infty z^2 e^{-z}/f(z)\,dz. $$

Indeed the unsmoothed price is $\int f(2u^2-1)d\mu$; the remainder in replacing each positive-axis ramp by its translated even tent affects only $\log p\le2h$ and is negligible. Smoothing the tent costs $O(\epsilon)$ after normalization: Its Lipschitz bound gives $O(\epsilon)$ per value through $\log p\le D+2h+1$ and past that point the bound is $O(\epsilon e^{-(\log p-D-2h)/\epsilon})$ since it vanishes above the endpoint. Sum using Chebyshev. This argument does not justify omitting the smoothing at longer cutoffs. The PNT integrals for Cauchy-Schwarz and the total mass converge by the linear growth at large positive $z$ and the fixed lower cutoff; Chebyshev gives uniform exponential tails with a polynomial factor there.

## What the shallow hypothesis buys

Suppose there is no right zero with $d>c$ in the window. Reflection makes *all* local zeros shallow, $|d|\le c$. Write $k=(1/4+x^2)^{-1}$, $\phi=Dx-2\arg(1/2+ix)$, $M=R^{-1}\sum k\to1/3$, and $E$ for probability proportional to $k$ on these zeros with multiplicity. The [long-cutoff proof](long-cutoff-moments.md#one-common-phase-on-the-divisor) gives, with $b_j=\cosh(jd)\cos(j\phi)/\cosh(jc)$,

$$ Q_j=-M\cosh(jc)E[H b_j]+e_j,\qquad P_j=-M\cosh(jc)E[b_j]+e'_j. $$

Errors tend to zero in the fixed-small-$\epsilon$, then large-$q$ sense (iterated limsup as $\epsilon\downarrow0$). In the local residues $L(w)=H(x)+O_c(1/D)$ uniformly, an additive error summable against $k/R$ at each fixed order. The remaining factor at $1/2+ix$ has the same carrier $e^{ij\phi}$ as before; reflection averages $e^{jd}$ to $\cosh(jd)$. No sign of $L$ off the line is required.

We need *both* $E H\to I$ and $E H^2\to K$ at fixed $\epsilon$, where

$$ I=\sum_l r_l e^{-|s_l|/2},\qquad K=\sum_{l,m}r_l r_m e^{-|s_l+s_m|/2}. $$

Here the trace sees the fixed frequencies $lh$, not the growing $jD$. For details normalize local counting measure by $\log t$. For each fixed $a>1/2$ and $v\in\mathbb R$, the completed Hadamard trace at $1/2+a+i(t+v)$ is $(\log t)/2+O_{a,v}(1)$ by the exterior Euler series and Stirling. Discarding $|x|>J$ costs $o(\log t)$ by the unit zero counts. On all retained zeros, changing the Poisson width $1/2+a-\beta$ to $a$ costs $O_{a,v,c}(D^{-1}/(1+x^2))$ per zero. Thus the normalized measure against $a/(a^2+(x-v)^2)$ tends to $1/2$. As in [the localized trace](localized-principal-packet.md), unit counts give vague subsequential compactness and an $O(1/B)$ limsup tail against $(1+x^2)^{-1}$ outside $[-B,B]$. Every limit has the indicated convolution for every $a>1/2$; holomorphy in $\Re a>0$ extends the identity to all $a>0$, and the Poisson approximate identity identifies the limit as $dx/(2\pi)$. This uses no external strip assumption here, since the entire retained window is shallow. Test against $k$, $kH$, and $kH^2$, using $\int k(x)e^{isx}dx/(2\pi)=e^{-|s|/2}$ and $\log t/R\to1/3$. This gives the claimed limits without assuming independence of $H$ and the phases.

## Two ways to spend the price

At each local zero $b_2\ge 2b_1^2-1$: Harmonically extend the nonnegative boundary polynomial $(\cos\theta-y)^2$ to $|d|\le c$ and take $y=b_1$ at that point. The first price gives $-E[Hb_1]\ge 3P/\cosh c$ up to arbitrarily small errors. For the **raw** second order use $(E[Hb_1])^2\le (E H^2) E[b_1^2]$. For the **masked** second order use $(E[Hb_1])^2\le(E H)E[H b_1^2]$ and multiply the pointwise inequality by $H\ge0$. The resulting limiting upper prices are respectively

$$ U(c)=\frac{\cosh(2c)}3\left[1-\frac{2}{K}\left(\frac{3P}{\cosh c}\right)^2\right],\qquad W(c)=\frac{I\cosh(2c)}3\left[1-2\left(\frac{3P}{I\cosh c}\right)^2\right]. $$

Since $K>I^2$, the normalization by $I$ cannot be used for $P_2$. The following are strict necessary upper bounds, rounded *outward* with positive room for the errors:

| $c$ | $P_2$ | $Q_2$ |
|---|---:|---:|
| 1.54 | $<-.235$ | $<-.394$ |
| 1.574 | $<-.002$ | $<-.180$ |
| 1.60 | not needed | $<-.0062$ |

For comparison, at $c=1.574$ the old, unmasked first price $47/81$ gives an upper price **above** $.16$ on $P_2$. The improvement in the raw column needs no change at all to the prime sum being measured.

The two columns are not interchangeable even as prime-phase screens. Fix phases at primes through $3V$; their contribution to either second sum is $O(D^2/R)$, and prime powers are negligible. In the abstract independent prime-phase model choose separate constant real parts on narrow slabs about $2D-\log p=1$ and $-.3$, zero elsewhere above $3V$. At their midpoints the limiting unsmoothed raw leading weights are $h_2(1)=-1/2$ and zero. On the second slab the masked leading weight at the midpoint is $A_2h_2(.1)\ne0$ (only $s_2=.4$ contributes). Thus the two weight columns are independent. First choose small fixed slab widths, then sufficiently small $\epsilon$ so the smoothed columns remain independent by local uniform approximation; the other spline endpoints give vanishing errors as $D\to\infty$. PNT gives the normalized column integrals divided by $R$ tending to the slab integrals with density $e^{-z'}dz'$, $z'=2D-\log p$. The limiting matrix is invertible, so real parts of size $O(1/R)$ suffice for any fixed pair of targets. This comparison does not prescribe phases at an actual sample.

## Longer tests, only if the signed data warrant them

With the common nonnegative mask, integrate the strip extension of any nonnegative trigonometric polynomial against $H$. The [finite cutoff budget](finite-cutoff-budget.md) therefore applies with constant mass $I/3$ and prime first price $P$. For its normalized sine vector and $s_j=2\sum_k v_kv_{k+j}$, the signed price on $\sum_{j=2}^n s_j Q_j/\cosh(jc)$ is at most $I/3-2\cos(\pi/(n+2))P/\cosh c$ in the iterated limit. In particular the eventual bound is $<-.00092$ at $(c,n)=(1.90,7)$, and $<-.000044$ at $(1.95,15)$. For this single weighted moment relaxation the vanishing-higher-data ceiling is now $\operatorname{arcosh}(6P/I)\in(1.968,1.969)$: Below it some finite sine vector separates, and at or above it the circle density $(1-2(3P/(I\cosh c))\cos\theta)/(2\pi)$ meets the first constraint with all higher moments zero. This ceiling is not an upper bound for joint tests using other masks or actual primes.

**Replay and decision.** Run [check-masked-cutoff.py](check-masked-cutoff.py) with SageMath's Python without `-O`. It encloses $P,I,K$ and the prices by ball arithmetic, integrating $\mathcal L$ exactly up to enclosures on the three ramp pieces. At a surviving conductor use the raw column if $P_2$ is already available; if it does not decide, accumulate the masked column on the same primes and at the same height. Only an outside value with controlled numerical error selects a deeper census. Nothing here supplies an exceptional conductor, an unconditional $1.60$ depth, or the uniform $Z\le.0658$ exclusion.
