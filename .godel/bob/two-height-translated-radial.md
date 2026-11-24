# A common two-height witness through order nine

At $c=39/20$, one common prime phase law matches all first ramps and all zero answers through nine at both shallow heights $t$ and $3t$. Thus any separation on this **zero-answer path** in the fixed-translate limiting comparison must use radial order at least ten at one height. This does not construct an exceptional conductor or a pair of zeta zero windows.

Use $R,V,D,t$ and the whole smoothed splines $B_j$ from the [long-cutoff identity](long-cutoff-moments.md). Write $z=D-\log p$, $u=|\cos(\theta/2)|$, and put

$$A(u)=2u^2-1,\qquad B(u)=4A(u)^3-3A(u),\qquad v(z)=z_+.$$

The prime assignment at $t$ and $3t$ is $(a,b)=(E[A(u)\mid z],E[B(u)\mid z])$. The mean condition is $\int v(z) E[u\mid z]e^{-z}\,dz\ge8/9$. The exact joint condition on the three expectations is membership in the convex hull of $(A(u),B(u),u)$ for $0\le u\le1$: It is the image of phase probability laws, and every finite mixture lifts by $\theta=2\arccos u$. Compactness and Carathéodory give the same hull for arbitrary measures. In particular $B(E[A])$ is not the mixture's third moment, and $\sqrt{(1+a)/2}$ is only an upper bound on its angular mean. The [order-eleven single-height witness](translated-step-witness.md) with its deterministic phases does not pass even the order-nine third cap: Its unshifted short price is about $-.90284$, whereas the unshifted order-nine ramp can have magnitude at most $C_9=.62280824\ldots$.

## Witness through nine for every translate

[The witness replay](check-two-height-radial-witness.py) gives exact phase probabilities on 119 rational slabs. For $z<-6$ use $\theta=\pi/2$, giving $a=b=0$; beyond the final knot keep its phase law. The checker constructs $a,b,E[u\mid z]$ as rationals, verifies the probability sums and support, and integrates the angular mean on each slab using the difference of $(1+z)e^{-z}$ at its endpoints. Finite-grid cone optimization with peak exchange located this law; only the frozen rational mixtures are used in the certificate. The sampled maxima before rounding were about $.62269229$ and $.62269224$, with final slab-moment reconstruction residual below $10^{-9}$ in the solver. Neither the finite grid nor the solver is needed for the bound.

In the Fourier convention $\widehat J(x)=\int J(z)e^{-ixz}\,dz$, set $J_y=e^{-z/2}y(z)$ for $y=a,b$. The checker obtains

$$\max(\|\widehat J_a\|_\infty,\|\widehat J_b\|_\infty)\le .62275<C_9,\qquad C_n=\frac{\cosh c}{6\cos(\pi/(n+2))}.$$

For a step law $y$, with jumps $\Delta y_l$ at $z_l$, the transform is $\sum_l e^{-z_l/2}\Delta y_l e^{-ixz_l}/(1/2+ix)$. Check this also against direct slab integration at three frequencies. The sum of the absolute weighted jumps divided by 80 gives the tail bound on $|x|\ge80$. On $[0,80]$ the checker bounds the squared numerator minus $.62275^2(1/4+x^2)$ by midpoint Taylor enclosures with a fourth-derivative remainder, as in the one-height witness. Real profiles cover negative frequencies by conjugation.

For a fixed first ramp $f=\sum_s A_s(z+s)_+$, write $w_0=1/2+ix$, $H=\sum_s A_s e^{s w_0}$ and $d\mu=dx/(2\pi|w_0|^2)$. The transform of $e^{-z/2}f$ is $H/w_0^2$ (substitute $z+s$ for $z$). Plancherel gives

$$\int f(z)y(z)e^{-z}\,dz=\int\Re(HG_y)\,d\mu,\qquad G_y=\frac{\bar w_0}{w_0}\overline{\widehat J_y}.$$

At each height use the trace marginal $\mu$, depths $\pm c$ with equal probabilities, and conditional first circle moment $m=-3G_y/\cosh c$. For $r=|m|$ put masses $(1-2r\cos\psi_l)/11$ on $\psi_l=(2l+1)\pi/11$. They are nonnegative because $r\le1/(2\cos(\pi/11))$. The roots-of-unity identities (also checked in a cyclotomic field) give total mass one, first moment $-r$, and exact zero moments two through nine. Rotate by $\arg(-m)$ for $m\ne0$. The first price matches by the displayed formula and the residue factor $-\cosh(c)/3$. The zeros hold **conditionally on $x$**, hence for all fixed translated multipliers at the higher orders. The two shallow circle laws can be chosen separately; the two prime profiles come from the *same* law.

On the prime side nonzero profiles are confined to $p\le e^6V$. The bound $O_{j,\epsilon,H}(1+D^j)$ on the whole smoothed spline and Chebyshev price those primes by $O_{j,\epsilon,H}((1+D^j)R^{1-j})=o(1)$ at each fixed order $j\ge2$ and both heights, after division by $R^{j+1}$. Prime powers are negligible by the long-cutoff truncation for sufficiently small fixed $\epsilon$. These are exact higher zero answers in the stipulated limiting model, not exact zeros of finite prime sums.

## Replay

At the repository root, with SageMath 10.9 and assertions enabled:

```sh
sage .godel/bob/check-two-height-radial-witness.py
```

The witness angular excess is $2.999974097\cdot10^{-6}$; the Fourier bounds use 413 and 518 finite boxes and tail bounds $<.571242$ and $<.575622$, respectively. The cap slack at nine is $5.82478084\cdot10^{-5}$. All decisive bounds are covered by outward enclosures; the roots-of-unity check and the prime mixture probabilities use exact arithmetic.

