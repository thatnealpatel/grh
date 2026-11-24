# The third-height first ramps do not replace order twelve

At scaled depth $c=39/20$, one common abstract prime phase law is compatible with shallow windows at both $t$ and $3t$, with **all first translates at both heights and zero answers at orders two through eleven at $t$**. There is no higher-order requirement at $3t$. Thus adding even the whole family of first ramps at $3t$ does not replace the twelfth radial cutoff on this path. This is compatibility in the [fixed-translate limiting comparison](translated-cutoff-budget.md), not a construction of zeta zeros or of a failing conductor.

## The common law and its certificate

Use $R=(9/5)\log q$, $V=R^2$, $D=\log V$, $t=2q^{3/5}$, and $z=D-\log p$. At each $z$ give $X=\cos\theta$ the law in [the slab table](translated-step-11-1.txt): The first integer in a row is $1024z_j$, and the remaining integers are pairs $(10^{10}X,10^{10}p)$ of atoms and probabilities on $[z_j,z_{j+1})$. There are 236 slabs. Use the point mass $X=0$ for $z<-8$ and extend the last slab from $16$ to infinity. Lift each atom by $\theta=\arccos X$. The same law gives all three profiles

$$A=\mathbb E[X\mid z],\qquad B=\mathbb E[4X^3-3X\mid z],\qquad U=\mathbb E[\sqrt{(1+X)/2}\mid z].$$

Here $B$ is the prime cosine at $3t$, not $4A^3-3A$. Likewise the failure mean uses $U$, not the square root evaluated at $A$. The checker verifies the nonnegative normalized law exactly and integrates $U$ against $z_+e^{-z}\,dz$ using the difference of $(1+z)e^{-z}$ at nonnegative slab endpoints. A sampled cone program with peak exchange located the profile and its moments were rounded by reconstructing the finite mixtures; the optimizer and the sampled peaks are not part of the certificate.

For $Y=A,B$ let $J_Y=e^{-z/2}Y$ and use $\widehat J_Y(\xi)=\int J_Y(z)e^{-i\xi z}\,dz$. The [checker](check-translated-step-11-1.py) certifies:

| Quantity | Certified bound | Slack above the certified cap at depth $1.95$ |
|---|---:|---:|
| $\int_0^\infty ze^{-z}U(z)\,dz-8/9$ | $>7.65\cdot10^{-5}$ | — |
| $\|\widehat J_A\|_\infty$ | $<.615455$ | $>9.4150\cdot10^{-6}$ below $\cosh(c)/(6\cos(\pi/13))$ |
| $\|\widehat J_B\|_\infty$ | $<1.195120$ | $>4.0275\cdot10^{-5}$ below $\cosh(c)/3$ |

Both rational caps are also below the requested truncated cutoffs $.615464415$ and $1.195160275$. For each real profile the transform is $e^{2i\xi}N(\xi)/(1/2+i\xi)$, where $N(\xi)=\sum_j b_j e^{-i\xi(z_j+2)}$, $b_j=e^{-z_j/2}\Delta Y_j$. Beyond $|\xi|=64$, the absolute jump sum divided by 64 bounds the modulus by $<.375086$ and $<.355891$, respectively. On $[0,64]$ the checker proves $Q=|N|^2-C^2(1/4+\xi^2)<0$ by midpoint Taylor enclosures in 541 and 270 dyadic boxes, respectively, with $C$ the corresponding rational cap. The fourth derivative bound is $\sum_{k=0}^4{4\choose k}D_kD_{4-k}$ for $D_k=\sum_j|b_j||z_j+2|^k$. Real profiles supply the other frequencies by conjugation. All decisive comparisons use outward real or complex balls at 128 bits or exact rationals.

Replay from the repository root, with SageMath 10.9 and assertions enabled:

```sh
sage .godel/bob/check-translated-step-11-1.py
```

The replay encloses the angular excess at $7.6550432308769962\ldots\cdot10^{-5}$. It also gives the [unshifted short third-harmonic price](short-third-price.md) $C_3=-.89846391188319868\ldots$, below $-.72$. The earlier shallow-depth-$1.40$ exclusion around $3t$ on that branch is consistent with the new depth-$1.95$ model.

## Match the prime answers with shallow conditional laws

At either height use the trace probability $d\mu(\xi)=d\xi/(2\pi|w|^2)$, $w=1/2+i\xi$, and depths $\pm c$ equally. For a fixed finite translated first ramp $f(z)=\sum_s a_s(z+s)_+$ with real coefficients, put $H(\xi)=\sum_s a_s e^{sw}$. The Fourier transform of $e^{-z/2}f$ is $H/w^2$. By Plancherel the first prime answer at a height with profile $Y$ is

$$\int f(z)Y(z)e^{-z}\,dz=\int\Re(HG_Y)\,d\mu,\qquad G_Y=\frac{\bar w}{w}\overline{\widehat J_Y}.$$

The phase-free prime density on fixed slabs is $e^{-z}\,dz$; these are the expectations in the abstract phase law. The first-order tent and smoothing errors vanish in the iterated limit as in the [translated comparison](translated-cutoff-budget.md). At either height the shallow signed first residue is $-\cosh(c)\int\Re(Hm)\,d\mu/3$ for conditional first complex moment $m$; the trace factor is $1/3$ also at $3t$ since $\log(3t)/R\to1/3$. Use $m=-3G_Y/\cosh c$. This gives one matching first moment for every translate, rather than a bound for each ramp separately.

* At $t$ take $Y=A$. The first cap gives $r=|m|<1/(2\cos(\pi/13))$. On angles $\psi_l=(2l+1)\pi/13$ for $0\le l<13$, use masses $(1-2r\cos\psi_l)/13$, nonnegative since $\cos\psi_l\le\cos(\pi/13)$. The roots-of-unity sum gives total mass one and first moment $-r$, and annihilates moments two through eleven: In the cosine-weighted sum the frequencies are $j-1,j,j+1$ and none is divisible by 13 for these $j$. Rotate by $\arg(-m)$ when $m\ne0$. The first moment is then $m$ and higher zeros persist conditionally on $\xi$.
* At $3t$ take $Y=B$. The second cap gives $|m|<1$. For $m=re^{i\alpha}$ take phases $e^{i\alpha}$ and $-e^{i\alpha}$ with masses $(1+r)/2$ and $(1-r)/2$, choosing any $\alpha$ when $m=0$. This supplies the first moment only; no vanishing higher residue there is claimed.

At $t$ the higher residue answers are zero for every fixed translate because the relevant moments are zero conditionally. On the prime side $A$ vanishes for $p>e^8V$. With the [whole smoothed spline](long-cutoff-moments.md), supremum $O_{j,\epsilon,H}(1+D^j)$, Chebyshev bounds each normalized order $j\ge2$ prime answer in absolute value by $O_{j,\epsilon,H}((1+D^j)R^{1-j})=o(1)$. Prime powers are negligible by the same long-cutoff truncation for sufficiently small fixed $\epsilon$. These are exact zeros of the limiting comparisons, not exact zeros of finite prime sums. No identification of the microscopic zero phases at the two windows is assumed by that comparison.

**Decision.** The extra first ramps can exclude a particular deterministic order-eleven model without excluding the common-law relaxation. To get a depth-$1.95$ separation on this path while keeping order eleven at $t$, add genuinely new information (such as a higher order at $3t$), not a search over additional first translates. The witness makes no claim about the optimum depth, a different allocation of higher orders, or nonzero answers.
