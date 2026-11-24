# The least maximum radial order at two heights is ten

At scaled depth $c=1.95$, one can trade orders at $t$ for orders at $3t$. The prime phases at the two heights are linked, not independent. The conclusion of the signed test is a deep zero **at one of the two windows**, not necessarily at $t$. In this expanded fixed-translate limiting comparison the least separating maximum order on the zero-answer path is ten: Orders $(10,3)$ suffice, and one common law passes $(9,9)$. This does not lower the least maximum order twelve for the [original one-height decision](translated-step-witness.md).

**Test the extra information in isolation.** On the original order-eleven witness let $A(z)$ be its prescribed cosine and $B(z)=4A(z)^3-3A(z)$ its cosine at $3t$. With the Fejér mask $(N,h,b)=(6,2/5,0)$ defined below, the normalized first price at $3t$ is $T_1(3t)/I(2/5)=-1.2329766363\ldots$ in this model. A shallow window even with *no* higher-order measurements there requires its absolute value to be at most $\cosh(c)/3=1.1951602753\ldots$. This distinguishes the old law using just one translated first sum at the additional height. To check the integral, at each jump $\Delta B$ at $z_l$ and each shift $s$, integrate the ramp from $k=\max(z_l,-s)$ to infinity, obtaining $(k+s+1)e^{-k}\Delta B$. The [original witness checker](check-translated-step.py) now encloses this ratio. This is a single-law exclusion, not yet the two-window result.

## Signed measurement and its limiting price

Use $t=2q^{3/5}$, $R=(9/5)\log q$, $V=R^2$, $D=\log V$, and $d=D(\beta-1/2)$. Use the same whole smoothed splines, normalization $R^{-(j+1)}$, and order of limits as in the [one-height identity](long-cutoff-moments.md). For height $y$, call its [translated sum](phase-shifted-cutoff.md#the-two-measurements) $T_j(y;h,b)$: Take shifts $s=lh+jb$ with coefficients $r_l e^{-s/2}$, $r_l=(6-|l|)/36$, $|l|<6$, before smoothing. The zero-side multiplier is $H_h(x)e^{ijbx}$ where $H_h=\sum_l r_l e^{ilhx}\ge0$ has mass $I(h)=\sum_l r_l e^{-|l|h/2}$ against the trace probability. Use $(h,b)=(1/10,1/25)$ at $t$ and $(1/5,7/25)$ at $3t$. Abbreviate the resulting sums by $T_j$ and $U_j$ respectively. They require distinct prime measurements, not just rescalings of the old sums.

For degree $k$, let $v_i=\sqrt{2/(k+2)}\sin((i+1)\pi/(k+2))$, $0\le i\le k$, and $s_{kj}=2\sum_{i=0}^{k-j} v_i v_{i+j}$. Put $C_k=\cosh(c)/(3s_{k1})$ with $s_{k1}=2\cos(\pi/(k+2))$. Use $a=.2885$, $b_0=.0048$, and measure the following single combination (the normalization matters):

$$ X_{nm}=\frac{a\cosh c}{s_{n1}}\sum_{j=2}^n\frac{s_{nj}T_j}{\cosh(jc)}+
\frac{b_0\cosh c}{s_{m1}}\sum_{j=2}^m\frac{(-1)^j s_{mj}U_j}{\cosh(jc)}. $$

| Orders $(n,m)$ | Measured premise | Limiting upper bound if both windows are shallow |
|---|---:|---:|
| $(10,3)$ | $X_{10,3}\ge-.000012$ | $<-.00002103$ |
| $(11,2)$ | $X_{11,2}\ge-.00042$ | $<-.00043486$ |

At a sufficiently large real high-endpoint failure each row forces a right zeta zero with $d>1.95$ within $(2/\epsilon)\log D$ of $t$ **or** $3t$, centers included. Fix sufficiently small $\epsilon>0$ before taking $q$ sufficiently large. Zero higher answers meet both premises. Neither signed premise has been established for actual failures.

**The common first price.** Write $z=D-\log p$, $u=|\cos((t/2)\log p)|$, $v=z_+$, and $L_j$ for the Chebyshev polynomial, so that the two cosines are $L_2(u)$ and $L_6(u)$. The failure gives $\int vu\,d\nu\ge8/9-o(1)$ with $d\nu=V^{-1}\sum_p(\log p)\delta_{D-\log p}$. Let $f,g$ be the two first ramps, **including** their respective weights $a,b_0$, i.e., the weighted sums of $r_l e^{-s/2}(z+s)_+$ with $s=lh+b$. Then the first-order smoothing bound at the two fixed heights gives

$$ aT_1-b_0U_1\ \ge\ P+o_*(1),\qquad
P=8/9+\int_{\mathbb R}e^{-z}\min_{0\le v_0\le1}\{f(z)L_2(v_0)-g(z)L_6(v_0)-z_+v_0\}\,dz. $$

Indeed subtract the failed angular mean inside the prime sum and minimize before using PNT, exactly as for the [short third-harmonic price](short-third-price.md). Only the phase-free continuous, piecewise Lipschitz minimum, zero sufficiently far to the left and of at most linear growth to the right, is integrated by PNT with the Chebyshev tail estimate. No PNT with a rapidly oscillating weight is used. Errors denoted $o_*(1)$ have arbitrarily small limsup in the stated order.

The [price checker](check-paired-radial.py) proves $P>.16532885137$. On the angular mesh of spacing $1/1024$ subtract $(4f+51g)/(8\cdot1024^2)$ from the sampled minimum: The second derivative is bounded above by $4f+51g$ since $f,g\ge0$ and $-L_6''\le252/5$. At an interior minimum the derivative vanishes; endpoints are sampled. Between consecutive radial mesh points all ramps are affine (every knot is included), so their pointwise minimum after the angular test is concave there. Integrate chords of the node lower bounds, then beyond $8$ use the endpoint value plus the minimum slope times $z-8$. This certifies the full radial and angular domains.

**Why the third-height signs alternate.** The cosine polynomial $|\sum_{r=0}^k v_r e^{ir\theta}|^2$ has constant one and coefficients $s_{kj}$. Its harmonic extension is nonnegative on the shallow depth strip, as in the [finite moment test](finite-cutoff-budget.md). Apply it to the zero phase $\phi+bx$ at $t$, and at $3t$ add $\pi$ to that height's phase $\phi+bx$. Multiply by $H_h\ge0$ before summing. Since both log heights divided by $R$ tend to $1/3$, the two inequalities, after positive rescaling and addition, give

$$ X_{nm}\le a C_n I(1/10)+b_0 C_m I(1/5)-(aT_1-b_0U_1)+o_*(1). $$

The phase rotation flips the sign at order one *and at every odd order*, not at even orders. The shared prime-phase floor gives the displayed strict margins. Only the explicit formula at the individual heights is used on the zero side.

**Sharpness and scope.** The [joint witness through nine](two-height-translated-radial.md) uses mixtures on each slab of a *single* prime phase. Both first-price Fourier norms are at most $.62275<C_9$, and a conditional circle law at each shallow height kills every translated answer of orders two through nine. This rules out any smaller maximum order in this model, not every individual trade at maximum order ten. The $(10,2)$ pair is unresolved: A sampled phase fit missed both caps by about $.0004$, which cannot rule out a different law. Neither the two-window separation nor the obstruction decides the old one-window problem from fewer one-window measurements. There is no demonstrated improvement in an unconditional depth guarantee, conductor threshold, or runtime.

Run `sage .godel/bob/check-paired-radial.py`, `sage .godel/bob/check-translated-step.py`, and `sage .godel/bob/check-two-height-radial-witness.py` with assertions enabled.
