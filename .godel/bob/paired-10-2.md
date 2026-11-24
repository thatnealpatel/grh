# Order ten at $t$ and order two at $3t$ separate

At depth $c=39/20$ the third radial order at $3t$ is **not necessary**. The finite signed combination $X$ below has limiting shallow upper price less than $-.00002546$. At a sufficiently large real high-endpoint failure, measuring $X\ge-.000025$ forces a right zeta zero with $D(\beta-1/2)>c$ within $(2/\epsilon)\log D$ of **$t$ or $3t$**, including the centers. As in the [paired comparison](paired-radial-price.md), $t=2q^{3/5}$, $R=(9/5)\log q$, $D=\log(R^2)$, and sufficiently small $\epsilon>0$ is fixed before taking $q$ sufficiently large. Zero higher answers meet this signed premise. No such measurement bound is proved for an actual failure.

The [$(9,9)$](two-height-translated-radial.md) and [$(11,1)$](translated-step-11-1.md) common laws therefore make $(10,2)$ coordinatewise minimal on the fixed-translate zero-answer path. This is not a saving in number of shifts, runtime, or depth at the original window alone. In fact using just the **untranslated** second cutoff at $3t$ instead of the new second-order weight leaves a shallow witness, as shown below.

## A first-price floor valid for arbitrary common laws

The [integer table](paired-10-2.txt) gives $l,10^7b_{t,l},10^7b_{3t,l}$, with missing coefficients zero. Write $h=1/25$ and, for $y=t,3t$, put

$$H_y(x)=\sum_l b_{y,l}e^{ilhx},\qquad f_y(z)=\sum_l b_{y,l}e^{-lh/2}(z+lh)_+.$$

These are **signed** first weights. For any trigonometric polynomial $H=\sum_l b_l e^{ilhx}$ with real coefficients, let $T_j(y;H)$ denote the order-$j$ prime measurement at $y$ with shift $lh$ and coefficient $b_l e^{-lh/2}$, summed over $l$ in the [whole spline before smoothing](phase-shifted-cutoff.md). This convention is used also at higher orders. Let $u=|\cos((t/2)\log p)|$, so the cosines at the two heights are $A(u)=2u^2-1$ and $B(u)=4A(u)^3-3A(u)$. Write $z=D-\log p$. Subtracting the failed angular mean, as in the paired comparison, gives

$$\sum_y T_1(y;H_y)\ge P+o_*(1),\qquad P=\frac89+\int e^{-z}\min_{0\le u\le1}\{f_t(z)A(u)+f_{3t}(z)B(u)-z_+u\}\,dz.$$

The minimum is pointwise, before any averaging or choice of conditional law. Only the phase-free minimum needs the PNT: It is continuous, zero to the left of the first knot, and at most linear in absolute value on the right. Chebyshev controls the right tail. The fixed-test smoothing errors have arbitrarily small limsup in the stated order of limits.

The [checker](check-paired-10-2.py) proves $P>.16405490$. For each radial node sample the full angular interval at spacing $1/1024$ and subtract $(4|f_t|+420|f_{3t}|)/(8\cdot1024^2)$ from the smallest sample lower bound. Indeed $B''(u)=960u^4-576u^2+36$ has absolute value at most 420 there; an interior minimizer has zero derivative, and the endpoints are sampled. Between radial nodes all the functions of $z$ being minimized are affine, since every knot and zero are nodes. Their minimum is concave, so the checker integrates the chord of the node lower bounds with weight $e^{-z}$. For $z>8$ it uses the lower bound at 8 plus $z-8$ times a separately bounded minimum slope. Neither a finite angular grid nor a finite radial range is assumed for the law.

## Turn the low continuous cost into actual finite measurements

Paying $\int |H_y|\,d\mu$ suggests a cheap separator, but using a variable phase $\arg H_y(x)$ directly at every order need not give translated splines. Instead use a finite identity. Take $L=256$, $N=512$, $\alpha=\pi/(L+1)$, $v_r=\sqrt{2/(L+1)}\sin((r+1)\alpha)$, $0\le r<L$. Define $D_L(\theta)=|\sum_r v_r e^{ir\theta}|^2=\sum_{|l|<L}d_{|l|}e^{il\theta}$. By the sine product formula,

$$d_l=\sum_{r=0}^{L-1-l}v_r v_{r+l}=\frac{(L-l)\cos(l\alpha)+\sin((l+1)\alpha)/\sin\alpha}{L+1}.$$

In particular $d_0=1$ and $d_l>0$. For $\theta_p=2\pi p/N$, $0\le p<N$, put $K_p(x)=D_L(hx-\theta_p)$ and at each height define

$$V_{y,p}=\sum_l (b_{y,l}/d_{|l|})e^{il\theta_p},\qquad H_{y,j}(x)=\frac1N\sum_p |V_{y,p}|e^{ij\arg V_{y,p}}K_p(x).$$

Zero $V$ terms are omitted. **At order one $H_{y,1}=H_y$ identically**: Average each $e^{i(l-k)\theta_p}$ for table index $l$ and mask index $k$. Only $l=k$ survives, since $|l|+|k|<N$. At every order the coefficients of $e^{ikhx}$ are real by pairing $p$ with $-p$ modulo $N$, although individual masks need not be even. Thus $T_j(y;H_{y,j})$ uses only allowed real shifts and coefficients. The rotation is multiplied by $j$, not held fixed across orders.

At height $y$ take $n_t=10$, $n_{3t}=2$. For each $n=n_y$ use the [degree-$n$ sine vector](finite-cutoff-budget.md) $w_r=\sqrt{2/(n+2)}\sin((r+1)\pi/(n+2))$, $s_{nj}=2\sum_{r=0}^{n-j}w_rw_{r+j}$, $s_{n1}=2\cos(\pi/(n+2))$, and $C_n=\cosh c/(3s_{n1})$. Define the measured price

$$X=\sum_{y=t,3t}\frac{\cosh c}{s_{n_y1}}\sum_{j=2}^{n_y}\frac{s_{n_yj}}{\cosh(jc)}T_j(y;H_{y,j}).$$

Under shallowness apply the nonnegative polynomial $|\sum w_re^{ir\theta}|^2$ at the rotated phase $\phi+\arg V_{y,p}$, extended harmonically from strip depths $\pm c$. Its $j$-th term acquires the factor $\cosh(jd)/\cosh(jc)$ at depth $d$. Multiply by $|V_{y,p}|K_p(x)/N\ge0$, then sum in $p$. This proves positivity pointwise at **every real frequency** before trace integration. The [explicit formula comparison](translated-cutoff-budget.md) now applies to the combined real multipliers with precisely the stated signs. The constant uses the trace characteristic function $\int e^{isx}d\mu=e^{-|s|/2}$ and the common height factor $1/3$. Consequently

$$X+\sum_y T_1(y;H_y)\le C+o_*(1),\qquad C=\sum_y\frac{C_{n_y}}N\sum_p |V_{y,p}| I_p,\quad I_p=1+2\sum_{l=1}^{L-1}d_l e^{-lh/2}\cos(l\theta_p).$$

Here $I_p=\int K_p\,d\mu$ exactly. The finite sum is **not** a quadrature bound on a continuous norm. The checker encloses $C<.16402944$ with 128-bit balls. Together with the first-price floor this gives the claimed strict gap. The table was located by a sampled cone search for small Fourier cost and then rounded; neither the optimizer nor its cost estimate is needed for the proof.

## Why the raw second-order zero answer does not suffice

Mix the $(9,9)$ and $(11,1)$ common laws with probabilities $89/200$ and $111/200$ on every slab. Dilute the resulting law with probability $1/6000$ of the constant atom $\cos\theta=0$. This dilution makes both first-price profiles $5999/6000$ times their mixture and contributes $1/\sqrt2$ to the conditional angular mean on its own component. It changes the mean and the Fourier caps together. The [raw checker](check-raw-10-2.py) replays both tables. By linearity of the mean and the triangle bound on the Fourier moduli, the new law has failure mean $>8/9+.000013$, first cap $<C_{10}$ at $t$, and first cap $<C_1$ at $3t$. Thus the usual conditional circle construction kills orders two through ten at $t$, while matching all first ramps at both heights. The same prime law still gives zero limiting higher prime answers: Both cosine profiles vanish below the first knot, and the fixed smoothed spline bounds of the $(11,1)$ witness still apply.

At $3t$ write $G(x)=\sum_i b_i e^{iz_i x}/(1/2+ix)$ for $b_i=e^{-z_i/2}\Delta\mathbb E[B(u)\mid z_i]$, using jumps on the combined knots. The matching circle first moment is $m=-3G/\cosh c$. To kill just the second answer at shift $s$ one needs zero integrated real second moment of the rotated angle $\phi+sx/2$ (the constant shift multiplier scale does not matter). By the [two chord extrema](phase-shifted-cutoff.md#why-the-raw-decision-cannot-just-inherit-the-rotated-depth), for this first moment the exact test is that both real and imaginary energies of $e^{isx/2}G$ are at most $\cosh^2(c)/18$. These energies equal $(L_0\pm S_s)/2$, where

$$L_0=\sum_{i,k} b_i b_k(2+|z_i-z_k|)e^{-|z_i-z_k|/2},\qquad S_s=\sum_{i,k} b_i b_k(1+v_++v_+^2/2)e^{-|v|/2},\quad v=z_i+z_k+s.$$

The shift only enters the sum kernel, from integrating $e^{isx}G^2$, not the difference kernel for $|G|^2$. At $s=0$ the larger energy is $<.71211$, below the cutoff $.71420404\ldots$. A mixture of the two chord laws therefore realizes the raw zero answer. This does **not** kill the shifted answers simultaneously. Indeed already at $s=1$ the real energy exceeds $.78831$ for this first representer. This is a test of the proposed observable on a specific law, not an unrestricted separation for that shift.

Replay both certificates from the repository root with SageMath 10.9 and assertions enabled:

```sh
sage .godel/bob/check-paired-10-2.py
sage .godel/bob/check-raw-10-2.py
```

**Next decision.** Can the order-two weight at $3t$ be a single translate rather than this signed mask? Start with shift $1$, not the raw shift $0$. For a primal witness impose the two rotated *integrated* energy bounds, not a conditional order-two Fourier cap. For a separator the higher multiplier at $3t$ must actually be a multiple of $e^{ix}$, not merely a mask whose first weight is centered there. This question concerns the second measurement only; the first translates and the translated prefix at $t$ remain available.
