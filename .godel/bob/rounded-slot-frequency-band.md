# A frequency band for the actual rounded-slot excess

At the named center the signed shape count across separated supports can be tested by a finite band of additive characters of the *actual* reduced fraction $M/k$. Neither its constant mode nor its very low or very high modes can account for detection. The two ends of the band have different cutoffs: The zero integral of the sign kernel controls one, and its corners control the other. This is an absolute-error reduction, not a bound for the middle band.

Use the notation of the [signed comparison](separated-signed-tuples.md): $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $L=\log t/D$, $n=2h=(4+2\gamma)L+O(1)$, $0<\gamma<1/2$. Work at one integer $1\le d\le5D$, $A=\sum w_p>a_0>0$, with the original probabilities $\rho(p)=w_p/A$ on the prime pairs. All estimates are uniform at fixed $a_0,\gamma$. Use the separated completed-tuple gate of the [last-slot formula](last-slot-residues.md) with the power radius, or the $D^2$ radius intersected with the original low-private-slot exclusion as in the [same-amplitude detector](detection-radius.md). Denote this gate by $J$. Omit a fixed positive label. On $J$ the reduced base ratio is $M/N<1$, $k=(N-M)/d$, $x=M/k$, and $p$ is the nearest integer to $x$. Write $r=x-p$ and

$$v=v_p=\frac{p(p+d)}{td}=t^{-1+o(1)}.$$

Crucially, this width depends only on the candidate start, not on the hidden base once that label is fixed. For $s\in\mathbb R$ set $\operatorname{sinc}(s)=\sin(s)/s$ by continuity at zero, and put

$$c_m(v)=\pi v\left[\operatorname{sinc}^2(\pi(2\pi mv-1))+\operatorname{sinc}^2(\pi(2\pi mv+1))\right].$$

Choose any smooth even cutoff $0\le\chi\le1$ equal to 1 on $[-1,1]$, zero off $[-2,2]$, and nonincreasing on the positive axis. Write $\chi_H(m)=\chi(m/H)$. Fix $0<\epsilon<1/10$, $H_-=t^{8/11-\epsilon}$, $H_+=t^{8/5+\epsilon}$. Then the original signed shape integral $J_R$ equals

$$ A^n\sum_{m\in\mathbb Z}(\chi_{H_+}-\chi_{H_-})(m)
 \mathbb E_{\rm base}\left[J\rho(p)c_m(v_p)\cos(2\pi mM/k)\right]
 + O(t^{-1-\sigma+o(1)}), \tag{1}$$

where $\sigma=\min(\gamma/8,5\epsilon/4)$. Rejected bases contribute zero. In particular all the retained coefficients of the cosines are **nonnegative**, but the cosines are signed and must be averaged with their actual weights. The estimate does not assert a bound on the sum of termwise absolute correlations in either discarded tail.

## Freeze the width and keep the gate

On the rounded gate the exact argument of $G(z)=(1-|z|/(2\pi))_+\cos z$ is $r/v_x$ with $v_x=p(x+d)/(td)$. On the support of either $G(r/v_x)$ or $G(r/v)$, $|r|\ll X^2/(td)$ and $v_x/v=1+O(X/(td))$. Thus the Lipschitz replacement costs $t^{-1+o(1)}$ pointwise there, and there $|t\nu|\le 8$ eventually since $e^\nu=1+d r/[p(x+d)]$. Restoring the omitted independent slot by its factor $\rho(p)$, the original probability of this window is at most $t^{-1/4+o(1)}$ by the same-sign spacing bound of the last-slot note. As $A^n=t^{o(1)}$ the error is negligible at (1). Together with the preceding rounded-slot reduction this leaves $A^n\mathbb E_{\rm base}[J\rho(p)G(r/v_p)]$. In particular we have not extended the gate to nearby integers that are not prime pairs.

The periodization $F_v(r)=\sum_{j\in\mathbb Z}G((r-j)/v)$ agrees with this kernel for centered $r$ since $2\pi v<1/2$. Its Fourier coefficients are $c_m(v)$: Scale the integral and use the transform $2\pi\operatorname{sinc}^2(\pi s)$ of $(1-|z|/(2\pi))_+$ in angular frequency $s$, then translate by the cosine. They are absolutely summable for each $v$, and $c_0=0$ exactly. Since $p$ is an integer, $e^{2\pi i m r}=e^{2\pi i mM/k}$. This step expands the actual displacement, not a sample from a CRT class.

## A cell bound away from (as well as at) zero

Let $H=t^\theta$ with fixed $0<\theta<2$, and $\|\cdot\|$ denote distance to the nearest integer. For any offset $b=b(p)$ modulo one and fixed $B>1$,

$$\mathbb E_{\rm base}\big[J\rho(p)(1+H\|r-b(p)\|)^{-B}\big]\le H^{-1/4+o(1)}. \tag{2}$$

To see this, lift back to the full product law, imposing that the omitted positive label is exactly the rounded candidate. Condition on its value $p$. For a cell of $r$ of width at most $1/H$ in $[-1/2,1/2]$, the corresponding $\nu$ lies in a fixed interval of length at most $1/H$ eventually: Differentiate $\log(1+dr/[p(p+r+d)])$ on this range to get $O(d/X^2)$. Choose $j=\lfloor\log(H/4)/(2D)\rfloor$ other positive slots, possible since $j<h$. Given all other values their sum of log labels must lie in a translate of that interval. Different sums have spacing at least $X^{-2j}$ by comparing integer cross products of their ratios. Equal sums fix the multiset by the least differing start valuation, including for repeated starts. There are at most $j!$ completions. Under the unconditioned hidden-slot product law this costs at most $j!(8D^2/(a_0X))^j\le H^{-1/4+o(1)}$, since $\log j=D/2+O(\log D)$. No conditioning on successful rounding or separation was used for this price. Slice the circle into successive cells at distance $l/H$ from $b(p)$, splitting at the seam if needed; sum with weights $O((1+l)^{-B})$, then average over $p$. This proves (2), also with any extra restriction on the tuples.

## Price the two tails

Use the Fourier convention $e(mr)=\exp(2\pi i mr)$, and let $K_H(r)=\sum_m\chi_H(m)e(mr)$. By Poisson summation of a compact smooth cutoff (or repeated finite differences), $|K_H''(r)|\ll_B H^3(1+H\|r\|)^{-B}$. The low-pass kernel is

$$\sum_m\chi_H(m)c_m(v)e(mr)=v\int G(z)K_H(r-vz)\,dz.$$

Both $\int G$ and $\int zG(z)\,dz$ vanish. If $Hv=o(1)$, Taylor expansion through the linear term bounds the absolute value by $O_B((vH)^3(1+H\|r\|)^{-B})$. Use (2) at $H=H_-$. The weighted low-pass sum is $\ll t^{-3+(11/4)(8/11-\epsilon)+o(1)}=t^{-1-11\epsilon/4+o(1)}$.

For $Hv\gg1$ the high-pass kernel satisfies

$$\left|\sum_m(1-\chi_H(m))c_m(v)e(mr)\right|
 \ll_B (vH)^{-1}\sum_{b=0,\,\pm2\pi v}(1+H\|r-b\|)^{-B}. \tag{3}$$

Indeed, write $1-\chi_H$ as the telescoping sum of $\chi_{2T}-\chi_T$ at $T=2^jH$, $j\ge0$. On each shell the squared sine numerators in $c_m$ are $[1-\cos(4\pi^2mv)]/2$. Split them into the three exponentials, giving exactly the three offsets of (3). Each remaining smooth coefficient is a cutoff times a constant multiple of $v/(2\pi mv\pm1)^2$. After rescaling $m=T y$, the coefficient and every fixed number of its $y$-derivatives are $O_B(1/(vT^2))$ on the shell $1\le |y|\le4$. Poisson summation bounds its translated sum by $O_B((vT)^{-1}(1+T\|r-b\|)^{-B})$. Sum geometrically. This localization at **all three** corners avoids paying the worst Fourier tail at every tuple. By (2) at $H=H_+$, the weighted cost of (3) is $\ll t^{1-(5/4)(8/5+\epsilon)+o(1)}=t^{-1-5\epsilon/4+o(1)}$. The two tail prices, the width error, and the old rounding error prove (1).

## Why applying the ordinary additive large sieve to the band misses

The actual gated measure is not small before the kernel is applied. For $S=100X^2/d$, take the broad triangular multiplier $(1-S|\nu|)_+$. Its inverse height density $(2\pi S)^{-1}\operatorname{sinc}^2(u/(2S))$ is nonnegative, integrates to one, and is $\gg 1/S$ on $|u|\le cX/(nD)$. There $|Z_d(u)|^n\gg A^n$ by the derivative bound. The arbitrary-density comparison in the separated-tuples note, with power radius, gives weighted mass $\gg e^{-\eta}A^nX/(SnD)-t^{-1-\gamma/8+o(1)}\ge t^{-o(1)}$ in $|\nu|\le1/S$, where $\eta=o(n)$. For these tuples $M<N$ and $|x-p|=|p(p+d)(e^\nu-1)/(d-p(e^\nu-1))|<1/4$, so the actual last slot is recovered, even at this broad width. All slots are power-separated, so the tuples pass either gate. This uses no extrapolation of the low-private error to the broad window.

For some one of at most $X$ rounded labels $p$ the measure $A^n J\rho(p)\,d\Pr_{\rm base}$ therefore has mass $B_p\ge t^{-o(1)}$ at that label. Merge coincident phases $M/k\bmod1$ there into atoms of masses $b_i$. On the consecutive block $3/4\le2\pi m v_p\le5/4$ (length $N_0\asymp 1/v_p$), the band multiplier is 1, and $c_m(v_p)\asymp v_p$. A Cauchy bound for this block using the dual of the [Montgomery–Vaughan additive large sieve, Theorem 1 (1.4)](https://doi.org/10.1112/S0025579300004708), is

$$\|c\|_{2,\mathrm{block}}\left[(N_0+\Delta^{-1})\sum_i b_i^2\right]^{1/2},$$

where $\Delta$ is the minimum circular gap. Its hypotheses really do hold after merging, with the block anywhere on the integer line. But even using the **true** gap, its right side is $\gg\sqrt{v_p}\,B_p\ge t^{-1/2-o(1)}$: For $s$ distinct atoms, $\Delta^{-1}\ge s$ by packing, and $s\sum b_i^2\ge B_p^2$. For one atom the length term suffices. Even replacing the single gap by individual nearest-neighbor gaps in a bound of the same form does not fix this: Their sum is at most one, so $\sum b_i^2/\Delta_i\ge B_p^2$. Thus adding such absolute block bounds over $p$ and frequencies cannot reach $t^{-1+o(1)}$. This is a lower bound on the **certificate**, not on the true block sum or its second moment. It does not rule out subtracting a structured main term before estimating a remainder.

**Decision.** A detection-scale positive excess forces a positive contribution from this band. More precisely one can partition the band multiplier by a nonnegative smooth dyadic partition of unity: Some one of $O(\log t)$ shells then carries at least the excess less the error, divided by the number of shells. This is at a single shift with balanced signs and the genuine center; there need not be a common shell across shifts. Truncating instead at a small multiple of the reciprocal window width $1/v_p$ has not been justified. Nor is (2) a signed estimate for the remaining band. A further comparison has to preserve cancellation in the sums in (1), not just count rounded hits. For what can and cannot be discarded using endpoint primes see the [catalogue price](endpoint-modulus-catalogues.md).
