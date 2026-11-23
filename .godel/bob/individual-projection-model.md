# What the individual projection detects that a density estimate misses

The one-sided projection in [(7) of the signed test](adjacent-zero-counts.md) need not be small for a symmetric, simple zero set satisfying the strip, the unit counts, the fixed-width Poisson estimates, and the normalization of the positive test. This holds even with only $O((\log T)^{1/4})$ right-hand zeros **in total** up to $T$. There is one such set whose signed responses at every fixed positive integer multiple of a sparse sequence of named heights are consistent with **one probability law on phases** at each log-prime scale. Thus merely coupling several signed responses by trigonometric moment inequalities does not repair the inference. This is a countermodel to a proof from particular estimates, not a counterexample for zeta.

## One set of simple points

Use $B=7/8$, $\Delta=B-1/2$, $a=1/4$, $b=1/2$, $r=127/128$, and $P_s(u)=s/[\pi(s^2+u^2)]$. Choose admissible heights $t_n=2q_n^{3/5}$ starting large, $X_n=(3\log(t_n/2))^2$, $D_n=\log X_n$, $Q_n=X_n^{1/8}$, and $R_n=t_n^{1/3}$. Take $t_{n+1}\ge 8n t_n$ and $Q_{n+1}\ge 2Q_n$; unbounded odd prime conductors suffice. On the critical line start with density $\ell(y)=(2\pi)^{-1}\log(\max(2\pi e,|y|)/(2\pi))$. In the block $|u|=|y-s|\le R_n$ about each $s=\pm k t_n$, $1\le k\le n$, modify the densities by

* Adding $Q_n r^k(4P_b(u)-2P_a(u)\cos(D_nu))$ on **each** of the lines $B$ and $1-B$;
* Subtracting $4Q_n r^k(P_{b-\Delta}(u)+P_{b+\Delta}(u))$ on the critical line.

The different widths matter: $2P_a\le4P_b$ makes the oscillating density positive almost everywhere, while $b>\Delta$ permits positive-width compensation on the line. Even doubled blocks are disjoint; the subtracted density is $O(Q_n)=o(\log t_n)$ on each. On each vertical, round the positive half-density by placing one atom where its cumulative integral first reaches each positive integer, and reflect about the real axis. Use the same atoms on the two reflected verticals. These are simple points, with interval count error $O(1)$ per line, **not per block**. Integration by parts bounds rounding against a decaying absolutely continuous test $K$ by $O(\int |K'|)$.

The unit counts are $O(\log(2+|y|))$. Up to positive ordinate $T$, the absolute continuous count changes on all lines total $O(\sum_{t_n\le 2T}Q_n\sum_{k\ge1}r^k)=O((\log(2+T))^{1/4})$. Thus the positive right-hand count obeys this last bound, and the full count is $T\log(T/(2\pi))/(2\pi)-T/(2\pi)$ with the same error for large $T$.

## Fixed-width tests at arbitrary centers

For every fixed $\sigma\ge1$, uniformly in $y$, the model satisfies

$$\sum_\rho \frac{\sigma-\beta}{(\sigma-\beta)^2+(\gamma-y)^2}=\tfrac12\log(2+|y|)+O_\sigma(1).$$

For the background alone use $\pi P_{\sigma-1/2}*\ell$ and the integrability of $\log(2+|u|)$ against the kernel. For a block first extend its three changes to the whole real line. The nonoscillating changes cancel exactly by $P_s*P_{s'}=P_{s+s'}$: For instance $(\sigma-B)+b=(\sigma-1/2)+(b-\Delta)$. For the oscillating part with $d=\sigma-\beta\ge1/8$, the Fourier transform $\widehat P_d(\xi)=e^{-d|\xi|}$ bounds the convolution at **every** displacement, apart from a fixed factor, by

$$ Q_n r^k\int e^{-a|\xi|}e^{-d|D_n-\xi|}\,d\xi\le r^k\int e^{-(a-1/8)|\xi|}\,d\xi.$$

Here $Q_n=e^{D_n/8}$ exactly. There is at most one block whose doubled interval contains $y$. Extending this one costs $O_\sigma(Q_nr^k/R_n)$; all the other truncated changes together cost $O_\sigma(\sum_{m,j}Q_m r^j/R_m^2)=O_\sigma(1)$ by distance and mass. Rounding costs $O_\sigma(1)$ by variation. This proves the estimate. The [positive test $\Phi$](adjacent-zero-counts.md#a-positive-analytic-test-on-the-full-zero-strip) has its stated normalization too: Its inverse-square bound prices the nearby changes at $O(Q_n)=o(\log(2+|y|))$ as that center tends to infinity, and the distant ones at $O(1)$. Its derivative has an integrable bound on the three lines. On the background, dominated convergence after division by $\log |y|$ gives $(2\pi)^{-1}\int \Phi(1/2+iu)\,du=211/224$.

## A nonvanishing response on the correct side of (7)

Fix $k\ge1$, let $n\to\infty$, and use $u=\gamma-k t_n$ and the **frozen** $X=X_n$, $D=D_n$. Let $A_\beta(w)=M(\beta+iw)/(\beta+iw)^2$ for the fixed log-window filter of the signed test, its [critical-radius version](critical-radius-projection.md), or $M=1$. For fixed $c>0$ the right-hand selection $\beta>1/2+c/D$ is eventually just the line $B$. Its demodulated residue, including the minus sign, satisfies uniformly for $v$ in bounded intervals

$$ -\sum_{\beta=B}X^{B-1}e^{iDu}A_B(u+v)\ \longrightarrow\ r^k\int P_a(u)A_B(u+v)\,du. \tag{1} $$

Indeed $X^{B-1}Q_n=1$. Multiplication of $2\cos(Du)$ by $e^{iDu}$ in the local density gives $1+e^{2iDu}$. The latter frequency and the carrier from $4P_b$ cost $O_M(1/D)$ by integration by parts. Extending the local density to all $u$ costs $o(1)$. The remote blocks have a summable inverse-square bound before multiplication by $1/Q_n$, and global rounding costs $O_M((1+D)/Q_n)$. The bounds use $|A_B|+|A'_B|\ll_M(1+w^2)^{-1}$. Truncation at $|u|\le J$ with $J\to\infty$ also gives (1): The local density tail is integrable after scaling, and the two new boundary jumps in the rounding test cost $O_M(1/Q_n)$. Centered shifts have bounded first derivative in $v$ for bounded $v$, by the same inverse-square mass bound (or by unit-interval rounding on this line). Thus for the two-box measure $\mu$ of (7), $\int e^{iDv}\,d\mu=1$, $\|\mu\|=\pi/2$, and shrinking support give the limit in (1) at zero for the averaged, **un**demodulated signed residue. The whole-line identity (7) is a counting identity here too. Its projection on the core has this same limit for the filters at their certified radii: Their original tail estimates use only the strip and unit counts.

For example, with $H=\pi/D$, $b_0\le b'<B$, and $w=H/2$, the count difference in (7) is

$$ E_{b'}(H/2)=-8 r^k P_a(0) Q_n/D+o(Q_n/D). $$

The two cosine integrals on the adjacent boxes are $2/D$ and $-2/D$; the slowly varying $4P_b$ cancels up to $o(1/D)$ before scaling. All the differences in this window are $O(Q_n/D+1)$ by density and rounding. Thus neither excess multiplicity nor a loss from taking absolute count differences is needed for the large projection.

The critical-line contribution to the demodulated full residue tends to zero: The local correction costs $O(Q_n/\sqrt X)$, distant changes $O(1/\sqrt X)$, and rounding $O_M((1+D)/\sqrt X)$. In the background integral, $\ell(kt_n+u)/\log t_n$ tends to $1/(2\pi)$ against the inverse-square amplitude with $o(1)$ absolute replacement error, also for bounded shifts. Use $\log t_n/\sqrt X=O(1)$ and Fourier decay for the resulting constant density. If the reflected vertical is included for a fixed-strip filter defined there, its local cost is $O_M(Q_n X^{-7/8})$ with negligible remote and rounding costs. The critical-radius shift does not cross that vertical. Thus a near-line residue canceling the response is not being suppressed in (1).

## All fixed harmonics share one limiting phase law

Let $W_M$ be the inverse Laplace weight of $M(s)/s^2$, and let $z=\log(X/p)$. Fourier inversion on the line $B$ rewrites the right side of (1) as

$$ \int W_M(z)e^{-z}\,r^k g(z)e^{-ivz}\,dz,\qquad g(z)=e^{(1-B)z-a|z|}\in(0,1]. \tag{2} $$

Indeed $A_B(u+v)$ is the Fourier transform at $u+v$ of $W_M(z)e^{-Bz}$, and $\widehat P_a(z)=e^{-a|z|}$. For the fixed-strip filter, inversion on either side of $B$ gives integrability; for the critical-radius filter use two verticals strictly inside $[1/2,1]$ on either side of $B$. The ramp $W_1=z_+$ works directly.

Conditional on $z$, take the circle law that with probability $1-g(z)$ is uniform, and otherwise is harmonic measure at $r$ in the unit disk (density $(1-r^2)/(2\pi|1-re^{i\theta}|^2)$). Its $k$th Fourier moment is exactly $r^k g(z)$ for every $k\ge1$, by the geometric series. Thus (2) is compatible with $k$th powers of the **same** abstract phase and with bounded height shifts. The sequence of blocks was diagonalized so that every fixed $k$ is covered eventually; there is no uniform asymptotic asserted in growing $k$. This checks the continuous log-prime weight envelope, not the prime phases $p^{-it_n}$.

Under the ramp probability $z e^{-z}\,dz$ on $z>0$, its first real moment is

$$ c_1=\frac{r}{(B+a)^2}=\frac{127}{162}>\frac{47}{81}. $$

For small fixed filter perturbations the smoothed response is also greater than $47/81$: The unperturbed $W_0=\mathbb E(z+Z)_+$ dominates $z_+$ and the weight error is small in $L^1(e^{-z}dz)$ by the prime-comparison envelopes. In particular the signed core projection at $k=1$ exceeds the peak margin, not just a positive unsigned packet cost. Even the [stronger necessary angular condition for an endpoint failure](sampled-principal-peaks.md#if-the-first-harmonic-barely-passes-price-the-third) is consistent: Since $|\cos(\theta/2)|\ge (1+\cos\theta)/2$, its mean is at least $289/324>8/9$. This does not construct a real character selecting the favorable signs.

**Proof decision.** A fixed-width Poisson error of bounded size can hide the $D$-frequency of $O(X^{1/8})$ right-hand zeros while the projection reads it at order one. Even testing positive definiteness across the fixed harmonics of the prime phases does not distinguish this model. To use the explicit formula to exclude it requires more than another such moment inequality: For instance the bounded Poisson remainder for zeta on $\sigma>1$ has the specific Euler-series coefficients $-\Lambda(m)m^{-\sigma}$ after removing the completion terms. The construction has not matched those coefficients, the exact arithmetic identity at finite height, or any twist correlations. No one-sided upper bound for the actual zeros follows.
