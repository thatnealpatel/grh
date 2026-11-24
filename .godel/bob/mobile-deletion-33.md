# Moving the delete-33 seed knots at depth 39/20

At the exact depth $c=39/20$, the two unfolded first caps and a necessary three-site disk price rule out positive failure surplus in two neighborhoods of the [426-slab seed](deletion-laws/delete-33-unfolded-seed.txt):

- **Fixed laws, wider knot moves:** If each knot moves by at most $1/5$ and the slab laws remain unchanged, then $M-8/9<-1.2055\cdot10^{-6}$. This part also holds for independent probability mixtures of positions for each jump, even if the resulting profiles do not come from a prime law.
- **Joint refit, smaller knot moves:** If each ordered knot moves by at most $1/1000$, then one may replace the entire law on every slab whose *seed* left endpoint is nonnegative, and up to $1/4$ of the law on every other slab, by arbitrary laws on $0\le u\le1$. Then $M-8/9<-3.0\cdot10^{-8}$.

These are bounds over real knot positions and real atom sites, not displacement or atom grids. The joint bound does not cover unrestricted changes on the negative slabs, nor inserting extra knots.

Use $X=2u^2-1$, $T(X)=4X^3-3X$, $A=\mathbb E X$, $B=\mathbb E T(X)$ and $U=\mathbb E u$. Keep $X=0$ on the left ray and the last slab infinite. Define the normalized jumps $a_l=\Delta A_l/C_t$, $b_l=\Delta B_l/C$, and $d_l=\Delta U_l$ using the [unfolded caps](unfolded-deletion-33.md#prime-laws-and-first-replies), with $C=\cosh(39/20)/3$, $C_t=C/(2\cos(\pi/12))$. Use zero as the initial level for each jump sum; for $U$ the difference from the true left level is confined to a negative ray, where the failure weight vanishes. The first knot is at $-4.48$ before displacement. For moved knots $t_l$ put

$$w=1/2+ix,\qquad E_t(x)=e^{-\bar w t}/w,\qquad W(t)=(1+t_+)e^{-t_+}.$$

Then $V_A=\sum_l a_l E_{t_l}$, $V_B=\sum_l b_l E_{t_l}$, and **$M=\sum_l d_l W(t_l)$**, by integration on each slab, including the infinite one. To allow mixtures, replace each summand by its integral over a probability measure supported on $[z_l-1/5,z_l+1/5]$, where $z_l$ are the seed knots. No ordering inequalities are needed for the upper bound.

## A convex necessary price and a separable upper bound

Write $d\mu=dx/(2\pi|w|^2)$, $h=13/25$, $s_0=6/25$, and $H=e^{is_0x}L(hx)$, where $L(\theta)=\sum_{j=-1}^1 \lambda_j e^{ij\theta}$ with $\lambda=(2685,3623,3692)/10000$. Let $m=V_B$; the actual first mean has sign $-m$, which does not change its square. If its second moment $n$ has the three zero replies then

$$\Re\int H m^2\,d\mu\le\int |L|(1-|m|^2)\,d\mu$$

by $|n-m^2|\le1-|m|^2$. Since $|m|\le1$, any even real Laurent majorant $p\ge|L|$ gives the weaker necessary inequality

$$Q(m):=\int \big[p(hx)|m|^2+\Re(Hm^2)\big]d\mu\le P:=\int p(hx)d\mu.$$

Crucially $Q$ is a nonnegative quadratic form in the *field*, even for arbitrary trial fields that fail the first cap: its integrand is bounded below by $(p-|H|)|m|^2$. For the seed field $m_0$ let $g(t)=\Re\int(p(hx)\overline{m_0}E_t+Hm_0E_t)\,d\mu$. Expanding $Q(m-m_0)\ge0$ now gives

$$2\sum_l b_l g(t_l)\le P+Q(m_0).$$

The same formula holds with the integrals over knot mixtures. In particular **the tangent has the necessary direction**, without assuming convexity in the knot positions. On the seed $Q(m_0)-P<-4.3065\cdot10^{-5}$; the price is not being imposed as an equality there.

For the first caps take finitely many support cuts $\Re(\gamma_r V_{Y_r}(x_r))\le1$, $|\gamma_r|\le1$, $Y_r\in\{A,B\}$. If $k_{A,l}=a_l$ and $k_{B,l}=b_l$, multiplying the cuts by $\beta_r\ge0$ and the tangent by $\alpha\ge0$ gives

$$M\le \sum_r\beta_r+\alpha(P+Q(m_0))+\sum_l\sup_{|t-z_l|\le1/5}\left[d_l W(t)-2\alpha b_l g(t)-\sum_r\beta_r k_{Y_r,l}\Re(\gamma_r E_t(x_r))\right].$$

This inequality discards most of the full-domain first-cap information and does not require a sufficient three-site completion. Failure under the necessary conditions also rules out passing the exact Gram-corrected completion in the stated families.

## Price arbitrary atoms on the moved slabs

Write the summand at a given knot, before taking the supremum, as $d_l W(t)-\Delta A_l a(t)-\Delta B_l b(t)$, where

$$a(t)=\frac{1}{C_t}\sum_{r:Y_r=A}\beta_r\Re(\gamma_rE_t(x_r)),\qquad b(t)=\frac{2\alpha g(t)+\sum_{r:Y_r=B}\beta_r\Re(\gamma_rE_t(x_r))}{C}.$$

On the $l$th moved slab, let the new law have the form $(1-\eta_l)\mathcal P_l+\eta_l\mathcal Q_l$, with $\mathcal P_l$ the seed law on that slab. Since the affine price depends only on the moments, summation by parts shows that the additional allowance to the fixed-law bound is at most

$$\sum_l \eta_l\sup_{t,s,u}\bigl[F_l(t,u)-F_l(s,u)\bigr],\qquad F_l(t,u)=(u-U_l)W(t)-(X(u)-A_l)a(t)-(T(X(u))-B_l)b(t).$$

Here $t,s$ range over the two neighboring displacement windows, $u\in[0,1]$, and $F_l(\infty,u)=0$. We may drop the ordering constraint inside each supremum. The baseline affine price remains valid even if the fixed-law profiles at these particular moved knots fail either cap: it bounds the fixed-law contribution to the right side, not a new conditional solution. The atom formula includes the slab starting at the moved zero knot and the infinite terminal slab.

Partition each endpoint window into sixteen equal cells. For fixed $u$, bound the difference of $F_l$ from its chord on a cell of width $d$ by $d^2D_2/8$, where $D_2$ bounds $|W''|+2|a''|+2|b''|$ on the window. The bounds for $a'',b''$ use their center values and the piecewise third derivative bounds. When the window crosses zero, $W'$ is Lipschitz with constant at most one, so the same chord bound applies there. Bilinear interpolation in $t,s$ then reduces the remainder-free upper bound to the maximum over pairs of window nodes. For each node pair the atom price is a sextic in $u$. Its Bernstein coefficients on any subinterval give an upper bound; maximize each coefficient over left nodes and minimize the corresponding coefficient over right nodes. De Casteljau subdivision of $[0,1]$ gives a certified upper bound for the maximum over all $u$ and all node pairs. Add back the two chord errors. Thus the nodes only organize the computation; they do not restrict the certified laws.

## What the replay checks

The [rational inputs](deletion-laws/delete-33-mobile-dual.json) give $\alpha$ in units $10^{-12}$, rows $(100x_r,\mathbf 1_{Y_r=B},10^{12}\Re\gamma_r,10^{12}\Im\gamma_r,10^{12}\beta_r)$, and the degree-80 even Laurent coefficients of an unpadded $p_0$ in units $10^{-15}$. Add $2\cdot10^{-7}$ to its constant coefficient to obtain $p$. The [checker](check-mobile-deletion-33.py) proves $|L|>.065$ by using its real part when $|\cos\theta|>.76$ and its imaginary part otherwise. The exact coefficient $\ell^1$ error of $p_0^2-|L|^2$ is $<1.620\cdot10^{-9}$. It is smaller than $.065^2$, so the positivity of $p_0$ at angle zero extends everywhere, and $|p_0-|L||\le\|p_0^2-|L|^2\|_\infty/.065$. This verifies the majorant on the entire circle, not just its nomination nodes.

For $P$ use the Poisson moments $e^{-|j|h/2}$. Evaluate $g(t)$ by differentiating the [sum and difference kernels](unfolded-deletion-33.md#exact-three-site-completion) against the fixed seed. In the sum kernel set $v=t+z_k+s_j$; in the difference kernel set $v=t-z_k+jh$. Split the seed sums by the *exact* sign of $v$ at each evaluation; the prefix/suffix polynomials incorporate $e^{-t/2}$. Both kernels after multiplication by $e^{-t/2}$ are $C^2$ in $t$ at $v=0$. Their third derivatives off the joins have magnitude at most $4e^{-t/2}$ and $2e^{-t/2}$, respectively: on $v>0$ use $e^{-v/2}|-1+2v-v^2/2|$ and $e^{-v/2}|1-v|$, and on $v<0$ the third derivatives vanish. Thus the second derivatives are Lipschitz and Taylor remainder bounds hold through the moving joins. Split at $t=0$ for $W$, whose third derivative on each side has magnitude $<3$. For the cap terms use $|E_t^{(3)}(x)|=|w|^2e^{-t/2}$. Cover each closed displacement window by adaptive midpoint boxes, using a monotonicity test to price an endpoint where possible and an outward quadratic Taylor upper bound elsewhere. The cubic remainder is the derivative bound times the cube of the half-width divided by six. The replay uses rational knots, coefficients and box endpoints, and 128-bit outward real/complex balls for transcendental evaluations. It uses no numerical optimizer during verification.

From the repository root, with assertions enabled:

```sh
OPENBLAS_NUM_THREADS=1 /opt/sage-10.9/bin/python .godel/bob/check-mobile-deletion-33.py
```

The squared modulus coefficient error is $1.61900795350956\cdot10^{-9}$ to the shown precision. The replay covers the wider windows in 30,681 Taylor boxes and bounds the surplus above by $-1.20556985660021\cdot10^{-6}$ to the shown precision. In the smaller windows it gives the following price decomposition (shown rounded; the checker compares with exact rational thresholds):

| Term | Value in units of $10^{-6}$ |
|---|---:|
| Upper bound with fixed laws | $-2.244106565$ |
| Allowance for full replacement on negative slabs | $3.736543251$ |
| Allowance for full replacement on nonnegative slabs | $1.279455316$ |
| Upper bound at one-quarter negative replacement and full nonnegative replacement | $-0.030515436$ |

In particular the sum of both full allowances is too large for the same test to rule out unrestricted slab replacement.

## Joint exploration and decision

At $39/20$ a separate floating-point search moved the ordered knots and transferred mass between atoms on the corresponding slabs, allowing both $A$ and $B$ to change. The trust-region cuts used sampled first caps with continuous local peak searches and an adaptive three-site dual direction; they did not certify all frequencies or disk completion. The target reserves were $8\cdot10^{-7}$, $2\cdot10^{-5}$ on the first caps and $5\cdot10^{-7}$ on the three-site price, with some smaller reserves accepted in the search. The price slack here is the numerical minimum of radius minus center over the locally optimized real three-site directions with coefficient sum one; it is not a guaranteed completion slack. With displacements allowed up to $.0049$ and the zero knot pinned, the best observed mean with both estimated caps below one and this estimated slack positive was **$M-8/9\simeq-2.38168\cdot10^{-6}$** on the existing atom sites. The estimated maxima were $.9999992395$ and $.9999801830$, and the estimated price slack was $1.61\cdot10^{-7}$. This iterate moved 425 knots by at most $.000160$ and used 1181 signed transfers. Adding sites at the dominant atom plus/minus $.0005$ and $.002$ on nonnegative slabs reached $-2.38748\cdot10^{-6}$ before stopping. Knot-only trials reached $-2.57999\cdot10^{-6}$. The sustained steps were limited by the crowded $t$ cap peaks and the $3t$ cap/second-price tradeoff, not by reaching the displacement window. These are search observations, not rigorous bounds for joint refits. No positive-surplus candidate was rationalized, and no off-grid Gram completion is asserted.

**Decision.** Do not widen the knot search alone around this seed, or iterate smaller positive-side atom transfers in the certified joint neighborhood. On fixed seed knots, numerical maximization of the unrestricted per-slab atom price with these same cuts gives an additional allowance of about $4.00\cdot10^{-6}$ over the fixed-law bound of $-2.49\cdot10^{-6}$: about $3.42\cdot10^{-6}$ of the allowance comes from negative slabs. That price does not exclude a general joint refit. If revisiting the joint path, try substantially changing the negative-side laws while preserving the continuous first caps, or add new cuts that pay for that freedom. The all-real comparison at $39/20$ and the unrestricted separator question remain open.
