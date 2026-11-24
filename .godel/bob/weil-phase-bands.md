# Opposite phase bands for the original positive Weil charge

At a [real high-endpoint failure](short-buffered-packet.md), keep its own $R=(9/5)\log q$, $V=R^2$, $D=\log V$, and $t=2q^{3/5}$. Write $L=D/2$, $J=(2/\epsilon)\log D$, and fix $K=\cosh(0.28)$. For a right zeta zero $\rho=\beta+i\gamma$ put $x=\gamma-t$, $b=\beta-1/2>0$, $c=bD$, $s=\beta+ix$, and $z=x-ib$. All sums include multiplicity.

**Result.** In the annulus $1.5/D<|x|\le J$, retain the two bands

$$ \cos\theta<-K/\cosh c \qquad\text{or}\qquad \cos\theta>K/\cosh c, $$

where the exact phase $\theta$ is defined below. For every sufficiently small fixed $\epsilon>0$ and all sufficiently large failures, the first band's positive charge **minus the cost of the opposite band** exceeds $0.233$. The observable is the original $-\Re(g_\epsilon B^2)/(2R)$, summed over retained right zeros **and their same-ordinate mirrors**. No beta strip narrower than the classical critical strip is needed. There is no charge required from $c\le0.28$ in this lower bound: Neither band exists there. The cosine gap depends on depth and can become very small.

## An exact phase that separates the two halves

The centered positive test on $[-L,L]$ has endpoint profiles $e^{-v/2}$ at inward distance $0\le v\le L$ from either endpoint. Put $a(v)=(1-e^{-Lv})/v$, with $a(0)=L$. Integrating the two halves separately gives

$$ B(z)=e^{c/2+ixL}a(s)+e^{-c/2-ixL}a(1-s). $$

Use the analytic square root $r(z)=\exp((1-\cosh(\epsilon z))/2)$ of the **complex** multiplier. Define $X=e^{ixL}r(z)a(s)$, $Y=e^{-ixL}r(z)a(1-s)$, and $Z=r(z)B(z)$. Define the phase from

$$ P=\frac{e^{c/2}Z-e^{-c/2}\bar Z}{e^c-e^{-c}},\qquad \theta=2\arg P\pmod{2\pi}. $$

Exclude $P=0$ from both bands; its summand vanishes. This solves $Z=e^{c/2}P+e^{-c/2}\bar P$ exactly, so

$$ \Re(g_\epsilon B^2)=2|P|^2(1+\cosh c\cos\theta). \tag{1} $$

In particular the two bands contribute with opposite signs. Reflection $\rho\mapsto1-\bar\rho$ conjugates $Z$ by evenness and reality of the profile and multiplier on the real axis. Count a reflected pair once at its right member with charge $-\Re Z^2/R$. There is no reflection in $x$ about the test height.

## Bound the amplitude before pricing the complement

The formula for $P$ has an apparent loss near the line. In fact, uniformly in $x$ and $0<b<1/2$,

$$ P=e^{ixL}r(z)/s+O\big(1/[D(1+|x|)]\big). \tag{2} $$

To see this, set $\delta=Y-\bar X$. Subtracting $X$ from the formula for $P$ gives $(\delta-e^{-c}\bar\delta)/(e^c-e^{-c})$, of modulus at most $|\delta|/(e^c-1)$. For $b\le1/4$, compare $a(1-s)$ with $a(\bar s)$ along the horizontal segment of length $2b$. On this segment $\Re v\ge1/4$ and

$$ a'(v)=Le^{-Lv}/v-(1-e^{-Lv})/v^2\ll(1+|x|)^{-1}. $$

Also $|a(\bar s)|\ll(1+|x|)^{-1}$ and $|r(x-ib)-\overline{r(x-ib)}|\ll\epsilon b$: Differentiate $r$ on $|\Im z|\le1/2$, where exponential decay in $\cosh(\epsilon x)$ bounds the hyperbolic sine factor in $r'$. Thus $|\delta|\ll b/(1+|x|)$, and $b/(e^{bD}-1)\le1/D$. For $b>1/4$, the integral for $a(v)$ and its numerator bound give $|a(v)|\le\min(L,2/|x|)$ for both arguments, hence $|P-X|\ll De^{-D/4}/(1+|x|)$. Finally $|e^{-Ls}|\le e^{-D/4}$ in $X$. These estimates prove (2) for all small $\epsilon$ with bounded constants.

In particular, on bounded $|x|\le M$, the band phase is $xD+\arg g_\epsilon(x-ib)-2\arg s+O_M(1/D)$ modulo $2\pi$: Here $|r|$ is bounded below. This identifies the carrier of the alternating bands. **Use the exact phase for membership**, not this approximation: Even on a compact interval the error need not be smaller than the deep cosine gap.

From (2), $|P|^2\le (G+O(1/D))/|s|^2$, where $G=\exp(1-\cos(\epsilon/2))$ bounds $|g_\epsilon(z)|$. Gray entries (including band equality) have $-\Re Z^2\le2(K-1)|P|^2$ by (1). Only an upper bound on their signed charge is needed. At $\sigma=1+1/D$, let $k(d)=d/(d^2+x^2)$. The two numerators $d_1=1-\beta+1/D$, $d_2=\beta+1/D$ satisfy $0<d_1\le d_2$, so the pair pays

$$ k(d_1)+k(d_2)\ge\frac{1+2/D}{(\beta+1/D)^2+x^2}\ge\frac{1-O(1/D)}{|s|^2}. $$

This comparison is for a pair, including arbitrarily deep right zeros. Sum once per gray pair. The [completed Poisson sum](opposite-phase-bands.md#spend-one-poisson-budget-not-two) over all zeros is $W_\sigma=\sum_\rho k(\sigma-\beta)\le R/6+O(D^2+1)$. By positivity it dominates the sum of the gray pairs' kernels. Thus the normalized gray charge in the annulus costs at most $2(K-1)(G+O(1/D))W_\sigma/R\le G(K-1)/3+o(1)$. Line zeros contribute nonpositive charge since $B(x)$ is real and $g_\epsilon(x)>0$.

## Deduct the gray price once

The [original smoothed Weil estimate](short-buffered-packet.md#price-the-smoothing-on-the-original-prime-side) and the failure's first harmonic $\Re S_V(t)\ge47/81-o(1)$ give full charge at least $47/81-1/3-O(\epsilon)-o(1)$. In that same test the outer tail $|x|>J$ costs $o(1)$ and the center $|x|D\le1.5$ has nonpositive charge. Do **not** deduct the old near-line allowance: The gray estimate includes that set. The retained signed charge is consequently at least

$$ 47/81-1/3-G(K-1)/3-O(\epsilon)-o(1). $$

Before smoothing this is $47/81-K/3>0.23376$: For $u=0.28$, use $\cosh u\le 1+(u^2/2)/(1-u^2/12)$ by successive term ratios. Since $G=1+O(\epsilon^2)$, fix $\epsilon$ sufficiently small first, then take $R$ sufficiently large. This proves the strict $0.233$ claim, not an effective height threshold.

**Decision.** An upper bound of $0.233$ on this *retained signed charge* at the prescribed heights would suffice; it need not bound every off-line zero's absolute contribution. This is a different test from the [right-only Mellin imbalance](opposite-phase-bands.md), whose summands and normalization differ. Neither a bound excluding the packet nor an actual failing twist follows from the gray price.
