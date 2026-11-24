# One second-order translate at $3t$ does not separate at depth $1.95$

In the [fixed-translate common-law comparison](paired-10-2.md), there is a single rational common prime phase law at depth $c=39/20$ with failure mean $>8/9$, matching every first translate at $t$ and $3t$ and giving zero answers at orders two through ten at $t$. **For each fixed real shift $s$**, a shallow circle law at $3t$ also matches the zero second-order answer at that shift. The prime law is independent of $s$; the circle law at $3t$ can depend on $s$. This does not assert simultaneous matching of multiple second-order translates, separation at another depth, or the existence of actual failure conductors or zeta zeros.

## Exact law and first-price certificate

Use $R=(9/5)\log q$, $D=\log(R^2)$, $t=2q^{3/5}$, and $z=D-\log p$. Each row of the [table](single-shift-10-2.txt) contains $64z_j$ followed by pairs $(10^8X,10^8p)$ of atom and probability for $X=\cos\theta$ on $[z_j,z_{j+1})$. Use $X=0$ to the left of the first knot $-8$, and extend the last slab from $16$ to infinity. The 152 rows are finite mixtures supported in $[-1,1]$; lift each atom by $\theta=\arccos X$. The same law defines $A=\mathbb E[X\mid z]$, $B=\mathbb E[4X^3-3X\mid z]$, and $U=\mathbb E[\sqrt{(1+X)/2}\mid z]$. In particular $B$ is not the cubic evaluated at $A$.

For $Y=A,B$ let $b_j=e^{-z_j/2}\Delta Y_j$, $w=1/2+ix$, and $\widehat J_Y(x)=\int e^{-wz}Y(z)\,dz$. Direct slab integration gives $\widehat J_Y=\sum_j b_je^{-iz_jx}/w$. The first representer is

$$G_Y=\frac{\bar w}{w}\overline{\widehat J_Y}=\frac{\sum_j b_je^{iz_jx}}{w}.$$

The [checker](check-single-shift-10-2.py) constructs the moments from the table, checks normalization exactly, and integrates $U$ against $z_+e^{-z}\,dz$ by differences of the tail weight $(1+z)e^{-z}$ on nonnegative slabs. It certifies

| Quantity | Bound |
|---|---:|
| Failure mean minus $8/9$ | $>6.52\cdot10^{-6}$ (enclosed value $6.52469815633\ldots\cdot10^{-6}$) |
| $\|G_A\|_\infty$ | $<.61864<C_{10}=\cosh(c)/(6\cos(\pi/12))$ |
| $\|G_B\|_\infty$ | $<.96<C_1=\cosh(c)/3$ |
| $\int |G_B|^2\,d\mu$ | $<.70601<\cosh^2(c)/18=.71420404190244\ldots$ |

For each all-frequency cap $C$, center the numerator at $-2$ and set $N(x)=\sum_j b_je^{-i(z_j+2)x}$ and $Q(x)=|N(x)|^2-C^2(1/4+x^2)$. On $[0,64]$ dyadic bisection certifies $Q<0$ by a Taylor enclosure through order three with fourth derivative bound $\sum_{k=0}^4{4\choose k}D_kD_{4-k}$, where $D_k=\sum_j|b_j||z_j+2|^k$. The replay uses 464 boxes for $A$ and 86 for $B$. The other half-line follows by conjugation; the tail bound $D_0/64$ for $|x|\ge64$ is below $.477173$ and $.186800$, respectively. The caps do not rely on sampled frequency maxima. The checker also cross-checks each jump expression against direct slab integration at three rational frequencies. All computations used for the certificate are exact rationals or 128-bit outward Sage real/complex balls. Replay from the repository root with SageMath 10.9 and assertions enabled:

```sh
sage .godel/bob/check-single-shift-10-2.py
```

## Matching, with one shift at a time

The shallow comparison uses $d\mu=dx/(2\pi|w|^2)$ and equal depth weights at $\pm c$. For a real first spline $f(z)=\sum_s a_s(z+s)_+$ write $H=\sum_s a_se^{sw}$. Plancherel with the transform $H/w^2$ of $e^{-z/2}f(z)$ gives $\int f(z)Y(z)e^{-z}\,dz=\int \Re(HG_Y)\,d\mu$. Thus at each height the conditional circle mean $m=-3G_Y/\cosh c$ matches all first translates. At $t$, use the twelve angles $\psi_l=(2l+1)\pi/12$, $0\le l<12$, with probabilities $(1-2|m|\cos\psi_l)/12$, then rotate by $\arg(-m)$ (arbitrarily at $m=0$). The first cap ensures nonnegative weights; the roots-of-unity sum gives first moment $m$ and zero moments of orders two through ten. The prime answers at all the higher orders in question tend to zero by the [same fixed-spline estimate as for $(11,1)$](translated-step-11-1.md#match-the-prime-answers-with-shallow-conditional-laws): the first cosine profiles vanish for $p>e^8R^2$, and the normalized higher prime sum on the remainder is $O_{j,\epsilon,H}((1+D^j)R^{1-j})$ with negligible prime powers in that comparison.

At $3t$, let $m_s=e^{isx/2}m$. For a fixed $x$, the vertical and horizontal chord laws through $m_s$ have real second moments $2(\Re m_s)^2-1$ and $1-2(\Im m_s)^2$, respectively. They exist by the strict first cap, have mean $m_s$, and the endpoints give the extrema by nonnegative coordinate variance. When the integrated extrema straddle zero, a constant mixture of the two laws attains integrated zero. Rotating back by $e^{-isx/2}$ preserves the required unrotated mean $m$ and makes the measured second moment at shift $s$ vanish. Equivalently one needs both energies of $e^{isx/2}G_B$, meaning the integrals of the squared real and imaginary parts, to be at most $\cosh^2(c)/18$. Their sum is independent of $s$:

$$L_0=\int |G_B|^2\,d\mu=\sum_{j,k} b_jb_k(2+|z_j-z_k|)e^{-|z_j-z_k|/2}.$$

The kernel is the Fourier integral of $1/(2\pi|w|^4)$; differentiating the transform of $(a^2+x^2)^{-1}$ in $a$ and setting $a=1/2$ gives the expression. Since both energies are nonnegative, the checked strict bound for $L_0$ certifies both energies for **every** real $s$ individually, with slack $>.00819$. No shift grid, derivative estimate in $s$, or shift cutoff is needed.

For a pointwise diagnostic the checker also forms the energies $(L_0\pm S_s)/2$, with $S_s=\sum_{j,k}b_jb_kK(z_j+z_k+s)$ and $K(v)=(1+v_++v_+^2/2)e^{-|v|/2}$. Indeed $S_s=\Re\int e^{isx}G_B^2\,d\mu$; the inverse transform of $1/(w^3\bar w)$ is the convolution of $z_+^2e^{-z/2}\mathbf1_{z\ge0}/2$ and $e^{z/2}\mathbf1_{z\le0}$. At $s=1$ the real and imaginary energies are enclosed at $.67948033117\ldots$ and $.02651965205\ldots$.

## Discovery and limits

The accepted [baseline replay](check-raw-10-2.py) passed the real-energy test at $s=0$ ($.71210709372\ldots$) but missed at $s=1$ ($.78831623984\ldots$). Preserving $A$ on negative slabs automatically preserves the failure mean there, but leaves both the $B$ cap and the shifted energies to check. Numerical searches varying $B$ at fixed baseline $A$ only on negative slabs, even without the $B$ cap, did not reach the target. Increasing $(9,9)$ weight to $.6$ gave promising energy numerically but missed the $A$ cap; tried negative-slab corrections and translation did not recover both cap and mean. These restricted probes are not infeasibility claims.

The witness instead came from a joint slab moment search, imposing the sufficient quadratic constraint on $L_0$ directly. A sampled cone program maximized failure mean over slabwise convex hulls of $(X,4X^3-3X,\sqrt{(1+X)/2})$ for a finite atom dictionary, sampled caps with peak exchange, and target $L_0\le .706$. Its floating point profiles were reconstructed by finite atom mixtures and rounded in atom locations and probabilities to the integer scales in the table. A coarser $1/8$ dyadic positive slab spacing missed the mean target in the tested run. The optimizer, its problem tolerances and the sampled results are not needed to replay the final certificate.

**Next decision.** Do not search for a separating *single* translated second-order weight at $3t$ on this zero-answer common-law path at $c=39/20$: each gives a compatible model. To refine the signed-mask result, ask about the fewest distinct shifts in one higher weight or about simultaneous separate measurements. Neither follows from the shift-by-shift choice of chord law above.
