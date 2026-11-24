# An arithmetic mean bound for the original uncut screen

Let $Q\le q\le2Q$ range over integers, $R=(9/5)\log q$, $V=R^2$, $D=\log V$, $t=2q^{3/5}$, and $D_*=\log(((9/5)\log(2Q))^2)$. Keep fixed small smoothing $\epsilon>0$. For the [one-defect screen](uncut-defect-price.md) itself, at the actual zeta ordinates,

$$ \frac1Q\sum_{Q\le q\le2Q}|Z(q)|\ \le\ \exp\!\left[-(4/5-o_\epsilon(1))\frac{\log Q}{D_*}\right]. \tag{1} $$

Thus $Z\le0.0658$ except on a set of at most $Q$ times the right side, absorbing a constant in the exponent. This is **not uniform**. It applies even to nonconductors since the zeta test at $t$ uses no twist. Unlike the [annulus exception count](deep-retained-excess.md#where-the-genuine-upper-bound-holds), (1) includes distant zeros and estimates the size of the uncut functional, not just the probability of local support.

## A summable majorant after the exact smoothing

Use $a=1/D$, $A=1/2+a$, $x=\gamma-t$, and $b=\beta-1/2$. Combine the two exact expressions for $X$ in the [one-trace split](uncut-defect-price.md#the-signed-remainder). Since $Z=-\langle K,\Delta\rangle/(2\pi R)+(S-\alpha)d$, this gives

$$ Z=\frac1R\sum_{b>a}\big[-\Re F(x-ib)-q_b(x)+(S-\alpha)\delta_b(x)\big]. $$

The sum is over all right members at every ordinate, with multiplicity; the right-limit convention excludes $b=a$. In particular there is no additive $o(1)$ independent of the deep zeros. The uniform signed remainder bound gives $|q_b|\ll_\epsilon\delta_b$ for large $D$. The two widths in $\delta_b=k_{A-b}+k_{A+b-2a}$ are in $[a,2]$ for large $D$. For $b\le1/4$ they stay bounded away from zero, and for $b>1/4$ one has $D\ll V^b$. Thus $\delta_b(x)\ll V^b/(1+x^2)$ in both ranges. The centered test has $|F(x-ib)|\ll V^b/(1+x^2)$ by its bounded variation, bounded $L^1$ norm, support of length $D$ centered at zero, and bounded multiplier on the critical strip (see the [smoothed test bound](short-buffered-packet.md#price-the-complement-of-the-packet)). Consequently

$$ |Z(q)|\ll_\epsilon \sum_{\beta>1/2+1/D}\frac{V^{\beta-1}}{1+(\gamma-t)^2}. \tag{2} $$

This absolute estimate is for averaging. It would sacrifice the signs and the depth discount if imposed as a uniform target instead. No ordinate truncation was made in obtaining the screened functional.

## Average on the actual height mesh

Put $T=4(2Q)^{3/5}$, so $t\le T/2$ and $t\asymp T$. For $|\gamma|>T$, even using all zeros and $V^{\beta-1}\le1$, the unit zero count $O(\log(2+|\gamma|))$ bounds the sum by $O((\log T)/T)$ per sample. For $|\gamma|\le T$, discard the depth weight but require $\beta>\sigma=1/2+1/D_*$. For each fixed such zero,

$$ \sum_{Q\le q\le2Q}\frac{1}{1+(\gamma-2q^{3/5})^2}\ll Q^{2/5}. $$

Indeed the mesh spacing is $\gg Q^{-2/5}$ by differentiation; count samples in successive length-one bins and sum their inverse-square prices. By conjugation we may count positive ordinates and double. There is no real nontrivial zero of zeta, for instance by the alternating eta series. Thus the contribution to the average is $\ll_\epsilon Q^{-3/5}N(\sigma,T)$.

Use [Chourasiya and Simonič, first corollary](https://arxiv.org/abs/2507.15184), in the range $T\ge3\cdot10^{12}$ and $1/2+0.28/\log T<\sigma\le0.53125$, which holds eventually. Their specialized exponent is $3(1-\sigma)/(2-\sigma)$ with log power $(7-5\sigma)/(2-\sigma)\le3$ and additional $O(\log^2 T)$. The power of $T$ equals $1-(2/D_*)/(3/2-1/D_*)$. Now $Q^{-3/5}T=O(1)$ and $\log T=(3/5)\log Q+O(1)$, yielding (1) including the tails. No local count at a prescribed exception follows: A zero can be near $\asymp Q^{2/5}$ samples within a fixed ordinate interval, much smaller than the allowed exceptional population.

## A sign test for a packet, not a count of its zeros

There is also a deterministic restriction directly on the summands of $Z$ in the exact formula above. Denote the unnormalized bracket by $z_b(x)$. Fix $L<\infty$ positive. For sufficiently small fixed $\epsilon$ (depending on $L$) and all sufficiently large $D$, one has **$z_b(x)<0$ at every depth $a<b<1/2$** in the bands

$$ |x|\le L,\qquad \operatorname{dist}\big(Dx-\arctan(2x)-\arctan x,\,2\pi\mathbb Z\big)\le 1.20. \tag{3} $$

These are bands for the priced observable $Z$, not just for $-\Re F$. They need no knowledge of $b$ to locate. To see this, the phase of the growing square endpoint, including the multiplier, is

$$ \psi_b=Dx-2\arctan\big(x/(1/2+b)\big)+\sinh(\epsilon x)\sin(\epsilon b). $$

The difference between the middle angle in (3) and the angle without the multiplier in $\psi_b$ is at most $|\arctan(2x)-\arctan x|\le\arctan(1/(2\sqrt 2))$, by the tangent subtraction formula. Since $1.20+\arctan(1/(2\sqrt 2))<\pi/2$, fix $\epsilon$ small enough that $\cos\psi_b\ge\kappa_L>0$ throughout (3) and $2\inf_{|x|\le L}g_\epsilon(x)>S-\alpha$.

Check uniformity by taking any putative counterexample sequence. Pass to a subsequence with $c=bD$ bounded or tending to infinity. In the bounded case the exact two-half expansion from the one-trace price, at $x-ib$, gives

$$ z_b(x)/\delta_b(x)=S-\alpha-2g_\epsilon(x)-g_\epsilon(x)[2\cosh c+S e^{1-c}]\cos\big(Dx-2\arctan(2x)\big)+o(1). $$

Indeed the low cross term is $2g_\epsilon/(1/4+x^2)$, the real parts of the two carriers add with factor $2\cosh c$, $b=O(1/D)$ in the envelopes, and $\delta_b=(1+o(1))/(1/4+x^2)$. The cosine differs from $\cos\psi_b$ by $o(1)$. This excludes the sequence with bounded $c$, including approach to $1$ from above.

For $c\to\infty$, the growing half of $B(x-ib)$ has leading term $e^{iD(x-ib)/2}/(1/2+b+ix)$, of modulus $\asymp_L e^{c/2}$. Its omitted endpoint costs $O(e^{-D/4})$. The other half is $O(e^{-c/2})$ if $b\le1/4$ by its denominator, and $O(D e^{-c/2})$ otherwise: Factor out $e^{-c/2-iDx/2}$ and use the integral of $e^{-(1/2-b-ix)v}$ on $[0,D/2]$. In both cases the relative error tends to zero. Thus $\Re F(x-ib)$ is at least a fixed positive multiple (depending on $L,\epsilon$) of $e^c$ in (3), since $|g_\epsilon(x-ib)|$ is bounded below on the compact strip segment. Meanwhile $|q_b|+\delta_b\ll_\epsilon\delta_b=o(e^c)$: Use $\delta_b=O(1)$ for $b\le1/4$ and $O(D)$ otherwise. This excludes the second case. All signs refer to the already reduced, absolutely summed functional.

For example, an arbitrarily dense packet supported in (3) makes a nonpositive contribution even though (2) counts it positively. An exceedance requires more than $0.0658$ in the normalized **signed sum on the complement**, including $|x|>L$. This is a necessity only; dropping a large negative packet to estimate $Z$ from above could destroy the cancellation needed for the uniform bound. No fraction of actual zeros is asserted to lie in the bands.

**Decision.** The density estimate has the correct sign and strength for the mean of the actual $Z$, not the maximum. On a remaining candidate do not set the first prime harmonic to zero as on a typical sample. The [cutoff dilation test](dilated-first-ramp.md) gives a strictly stronger first-harmonic necessity at that same ordinate and a separate signed two-height test. These change the tests that could reject a candidate, not the value of its original $Z$.
