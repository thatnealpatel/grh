# What must be counted on the genuine high-amplitude shell?

A small value at $t$ need not suppress the integral even on $[t,5t/4]$. On the reconstruction's finite fixture the **whole** restricted high branch lies between $11290$ and $13440$ unit endpoint scales. No interval of length $1000$ accounts for as much as $25.2\%$ of it. Below is also a one-sided sampling bound for large $t$: To bound the high branch one can count values on a coarser grid than the [exact signed quadrature](centered-height-mesh.md), with coefficient $1+o(1)$ and a slightly relaxed amplitude cutoff. Neither statement bounds the eventual arithmetic count.

## A coarser upper sum from curvature

Use $c_i,Z,s,K_t,n,w_i,H_{ij},W_2$ of the [reconstruction](balanced-height-reconstruction.md), at either radius. Evaluate the same explicit $W_2$ formula wherever $s>0$. Put $L=X/D$, $m=X^{-1/10}$, $\Delta=L X^{-1/3}$, and $\eta=X^{-1/5}$. Let $U$ be either $[t,5t/4]$ or the full high height band $t^{7/10}\le |\tau|\le t^{13/8}$. For any origin $b$, put $u_j=b+j\Delta$. Then

$$
\int_{U\cap\{s\ge m\}} K_t W_2\,d\tau
\ \le\ (1+o(1))\Delta\!\sum_{\substack{\operatorname{dist}(u_j,U)\le\Delta\\s(u_j)\ge (1-\eta)m}} K_t(u_j) W_2(u_j) + O(t^{-3/2+o(1)}).
$$

For the single shell there is no additive error. Conversely the grid sum with $\operatorname{dist}(u_j,\mathbb R\setminus U)>\Delta$ and $s(u_j)\ge(1+\eta)m$, including its $\Delta$ factor, is at most $(1+o(1))$ times the displayed integral plus the same additive error. These are inequalities, not exact quadrature on an indicator. The spacing $X^{2/3}/D$ exceeds the earlier sufficient common spacing of order $\log t$ by a power of $X$. There is no corresponding assertion here about $M_3$ or about a single prime-locked phase.

**Proof.** Uniformly $A=\sum w_i\ll D^2$, and $\max\omega_i\ll1/L$ for $\omega_i=\log(1+d/i)$. Thus $|Z'|\ll A/L$ and $|Z''|\ll A/L^2$. Within distance $\Delta$ of a retained point the modulus changes by $O(A X^{-1/3})=o(\eta m)$. For $\tau$ in a grid cell with $s(\tau)\ge m$, project $Z$ onto the unit direction of $Z(\tau)$. Linear interpolation of this real function at the endpoints $u,v$ has error $O(A(\Delta/L)^2)$ by the second derivative bound. Each endpoint modulus dominates its projection. Hence, with $\lambda=(v-\tau)/\Delta$,

$$
s(\tau)^n\le(1+o(1))\big[\lambda s(u)^n+(1-\lambda)s(v)^n\big].
$$

Indeed $nA(\Delta/L)^2/m=o(1)$, so the additive interpolation error before taking powers has relative cost $1+o(1)$ after taking powers; then use convexity. A first derivative estimate alone gives no such relative bound at this spacing.

Write $E=\log(W_2/s^n)=-(n^2/2)\sum H_{ij}x_i x_j$ with $x_i=\Re(c_i/Z)$. Where $s\ge m/2$, $|x_i|\le w_i/s$ and $|x_i'|\ll (w_i/L)(1/s+A/s^2)$. Set $C_d=\sum H_{ij}w_i w_j$. Since $w_*\ll D^2/X$ and $\sum_j H_{ij}\le 1+2r$, we have $n^2 C_d\le X^{\rho+o(1)}$ with $\rho=0$ or $\xi<1/80$. Consequently

$$
\Delta |E'|\ll n^2 C_d (\Delta/L)(m^{-2}+A m^{-3})=o(1).
$$

This controls the **change** in the correction, not just its size, so the interpolation inequality carries over to $W_2$ with the same $1+o(1)$. Also $W_2\le t^{o(1)}$ there since $|E|\ll X^{\rho+1/5+o(1)}=o(\log t)$ and $A^n=t^{o(1)}$.

On the single shell and its one-cell extension $|K_t'|/K_t\ll 1/t$. For the full band omit neighborhoods of radius $R=t^{1/2}$ of the zeros $z=t+kt$, $k\in\mathbb Z\setminus\{0\}$. There $K_t\ll R^2/(k^2 t^3)$, and the total omitted cost is $O(t^{o(1)}R^3/t^3)$, also for samples since their length charged per neighborhood is $O(R+\Delta)$. Outside the neighborhoods $|(\log K_t)'|\ll1/R$ up to distance $\Delta$ from the retained point: Use the cotangent logarithmic derivative away from all multiples and the removable singularity at $t$. Thus the multiplicative change of $K_t$ is $1+o(1)$, including for the neighboring values used in interpolation.

Integrate the two linear interpolation weights over the charged parts of all cells. Each node receives at most $\Delta$ in total, rather than $2\Delta$; both endpoints qualify for the relaxed cutoff. This proves the upper sum. For the converse, for each contracted node interpolate symmetrically between the two heights $u_j\pm v$ for every $0<v\le\Delta/2$. Both qualify for the original cutoff and height band. Average in $v$; the two half weights give exactly the cell mean. These centered cells are disjoint in measure. The kernel-zero exception is charged on the node side in this direction. No grid origin translates the prime phases relative to the kernel.

## A necessary large-value bound, already on the one shell

At $r=D^2$ there is a stringent test on any proposed $O(B_{\rm unit})$ upper estimate, where $a=1/16$ and $B_{\rm unit}=La^n/t$. Take a shift with $n^2 C_d\le K$ fixed. In the range of the [detection argument](detection-radius.md) the number of discarded shifts is $O(D/K)$, not necessarily $o(D)$ for a fixed $K$. Write $\ell=L/\sqrt n$. For **any** $2\ell$-spaced heights $v_i$ in $[t+\ell,5t/4-\ell]$ with $s(v_i)\ge a$,

$$
\frac1{B_{\rm unit}}\int_{[t,5t/4]\cap\{s\ge m\}} K_t W_2\,d\tau
\ \gg_{K,\gamma} \frac1{\sqrt n}\sum_i \left(\frac{s(v_i)}a\right)^n.
$$

In particular an $O(B_{\rm unit})$ shell estimate implies $O_{K,\gamma}(\sqrt n)$ such separated hits and, on the inner shell, the pointwise cap

$$
s(v)\le a\exp\!\left(\frac{\tfrac12\log n+O_{K,\gamma}(1)}{n}\right)
$$

(with constants also depending on the proposed budget). Thus even a single overshoot of this size with a sufficiently large constant cannot be absorbed by invoking a small exceptional *fraction* of the $t/4$ interval. An upper bound on all of $M_2^{\rm ht}$ would give the same cap up to both ends of this interval, since its height band contains their $\ell$-neighborhoods.

To prove it, first partition the band of starts into $O(X/D^2)$ cells of diameter at most $D^2$. Cauchy on their masses gives $C_d\gg A^2D^2/X$, so $A\ll_\gamma\sqrt K$. At each $v_i$ project $Z$ onto its direction there. Choose the side on which the linear Taylor term is nonnegative (either side if it vanishes). Over length $\ell$ on that side the projected sum stays above $s(v_i)-O(A/n)$ by the second derivative bound. Thus $s^n\gg_{K,\gamma}s(v_i)^n$ there, even when $v_i$ is **not** a local maximum. All these intervals qualify for the high branch eventually, $E\ge -K/(2s^2)$ is bounded below, and $K_t\gg 1/t$ on the genuine shell. Integrating over the disjoint intervals gives the bound.

The [permutation moment](dyadic-prime-pair-moments.md) at order $k=2\lfloor\log(t/4)/(2D)\rfloor$ applies to these frozen coefficients but only gives $\int_{[t,5t/4]}s^k\ll t^{3/4+o(1)}$. At fixed amplitude it allows $t^{3/4+o(1)}/\ell$ disjoint persistence intervals, far more than $O(\sqrt n)$. Nor does the necessary hit count at $a$ alone suffice: More numerous excursions below $a$ can occur in the upper sum.

## Pricing one entire interval without an asymptotic comparison

Run `python3 .godel/bob/check-genuine-shell.py` without `-O`. Take $q=100000007$, $d=26$, $\gamma=1/4$, $r=D^2$, and $B_{\rm unit}=(X/D)16^{-8}/t$. On $[t,5t/4]$ the checker encloses the integral of $K_tW_2\mathbf1_{s\ge m}$, not an uncut moment or a sum at integer ordinates. It gives the bounds above. Although $s(t)<m$, the interval $[133637.9,133638.1]$ alone pays between $127$ and $300$ times $B_{\rm unit}$. Even removing **any** length-$1000$ neighborhood leaves over $8400 B_{\rm unit}$ on the shell. This prices the other excursions rather than inferring their size from the largest sampled value.

The checker propagates the original weighted phases by fixed-point rotations, enclosing initialization, roundoff accumulated over the whole path, and within-cell variation $w_p\omega_p$ times the half width. It prunes cells whose upper modulus misses the cutoff. At depth nine in each surviving unit interval it bounds $|Z|^8$ and the ordered quadratic exponent (including the diagonal) by interval arithmetic. A straddling cell has lower contribution zero. The sinc square is bounded above and below by its Taylor bounds on the actual translate. For the concentration bound every sliding interval is contained, up to null sets, in two adjacent aligned blocks: If their mass is $\le P$ and all other blocks have mass $\ge N$, the fraction is $\le P/(P+N)$.

The finite integral is not the completed $S$, even in sign comparisons with the ungated signed integral. No eventual estimate follows from the finite ratios. For the asymptotic high-branch upper estimate one can now target the *weighted number* of excursions on one coarser genuine grid, including the small threshold buffer. Checking just the central ordinate, bounding the largest local contribution without counting the others, or transferring a crest from height zero does not give that estimate.
