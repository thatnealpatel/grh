# A finite joint successor test at the 127-bit fixture cutoff

For **every** $25107\le X\le25108$, the two numbers $F\le0.9005$ and $B\le0.002389$ from the [adjacent chord test](adjacent-chord-deficit.md) suffice for a finite cap below $0.8877$ on the full signed modulus. No asymptotic weight or prime-gap error is used. This is a statement about the information in the two scalars, not the stronger test that knows [all within-triple phases](triple-endpoint-cap.md).

Precisely, assign any $e^{i\phi_p}$ to each prime $p<X$, use $w_p=(\log p)\log(X/p)/X$, and let $M=\sum w_p$. Order the clipped primes ($p\ge e^{-8}X$) from $p_0$ to $p_n$, put $z_i=\log(X/p_i)$ and $Z=\sum z_i$. For $i\ge1$ let $a_i$ be $\phi_i-\phi_{i-1}$ reduced modulo $\pi$ to $[-\pi/2,\pi/2]$, writing $\phi_i=\phi_{p_i}$. Put $f_i=\cos(a_i/2)$, so $F=\sum_{i=1}^n z_i f_i/Z$. For $1\le i<n$, put $r_i=\cos(2(a_i+a_{i+1}))$, $d_i=p_{i+1}-p_{i-1}$, $H=40\log X$, and

$$t_i=\frac{2}{H}(1-d_i/H)_+\,z_{i+1}(\log p_{i-1})(\log p_{i+1})/X.$$

Then $B=\sum_d(\sum_{d_i=d}t_i r_i)_+$, in particular $\sum_i t_i r_i\le B$. The [checker](check-finite-successor-cap.py) gives the following implication for all $|s_p|\le1$, $s_p$ real:

$$ F\le0.9005,\quad B\le0.002389\quad\Longrightarrow\quad
 \left|\sum_{p<X} w_p s_p e^{i\phi_p}\right|<0.8877<8/9.$$

**Allocation.** Give the triple centered at $i$ mass $c_i=\min(w_{i-1},w_i,w_{i+1})$ with fractions $3/10,4/10,3/10$ from its left, center, and right primes. These allocations cannot overdraw any prime, since the fractions covering it sum to at most one and each $c_i$ is at most its weight. Charge the remainder, including the part below the clip, at full mass. After removing a common rotation, the maximal contribution per unit of triple mass is

$$ U(a,b)=\max_{s,t=\pm1}|0.3s e^{-ia}+0.4+0.3t e^{ib}|,\qquad (a,b)=(a_i,a_{i+1}). $$

Convexity reduces the coefficient cube to signs, and the two flank signs absorb the reductions modulo $\pi$. Consequently the full modulus is at most $M+\sum_i c_i(U_i-1)$.

**Charge the two scalar constraints at their actual finite weights.** Write $D(a)=1-\cos(a/2)$, $\alpha=0.873$, $\beta=0.956$. The sum of half-edge deficits $\sum_{i=1}^{n-1}(z_iD(a_i)+z_{i+1}D(a_{i+1}))/(2Z)$ is at least

$$\delta=1-0.9005-z_0/Z-(z_1+z_n)(1-1/\sqrt2)/(2Z).$$

The term $z_0/Z$ occurs because the chord sum lacks a first edge; each end edge occurs only once instead of twice. Let $A_i=\alpha z_i/(2Z)$, $A'_i=\alpha z_{i+1}/(2Z)$, and $T_i=\beta t_i$. For fixed $X$ let $L_i$ be the maximum over $|a|,|b|\le\pi/2$ of

$$ c_i(U(a,b)-1)+A_iD(a)+A'_iD(b)-T_i\cos(2(a+b)). $$

The desired modulus is thus at most $M-\alpha\delta+\beta\,0.002389+\sum L_i$. Using a different envelope for each prime triple matters here: Simply replacing log factors by $\log X$ introduces errors on the scale of the desired margin.

**Finite verification.** Simultaneous negation permits $a\ge0$. Grid both angles at spacing $h=\pi/96$. Between grid nodes interpolate linearly in each coordinate. For each fixed pair of signs interpolate the *complex vector* first: Its error is at most $0.6h^2/8$ by the one-variable linear interpolation error bound (second derivative norm $\le0.3$ in each variable). The norm of the interpolated vector is at most the interpolant of corner norms; this argument does not differentiate a maximum or a norm at a zero. For $D$ the corresponding second derivative bound is $1/4$, and for the cosine of twice the sum it is $4$ per variable. Thus $L_i$ is bounded by the maximum **combined** score on the grid plus $h^2(0.6c_i+(A_i+A'_i)/4+8T_i)/8$. No assumption that neighboring triples can independently realize their worst cases is required for the upper bound.

The checker evaluates the grid and coefficient intervals with 120-bit directed rounding, then bounds the dot products by outward rounding onto integer grids with denominators $10^7$ and $10^{10}$, respectively. The integer products and sums within each triple are checked to fit in signed 64 bits. All coefficient bounds use the whole cutoff interval at once. In particular [the certified measurements](check-rank-box.py) at $q=2^{127}-1$, $\phi_p=q^{3/5}\log p$, do give a finite exclusion at the raw $8/9$ level by these two scalars alone. The separate within-triple cap there is tighter. The fixture has not been identified as a selected cell. Neither that fixture nor this cutoff-specific implication is a finite Weil endpoint theorem or a large-selected-height margin estimate.

## Large-cutoff consequence

The same checked grid gives one cutoff-independent inequality with looser coefficients:

$$ U(a,b)\le 0.027+0.946\,\frac{\cos(a/2)+\cos(b/2)}2 +0.0315\cos(2(a+b)). $$

Use the maximum combined grid score with equal deficit coefficients $0.946/2$, $T=0.0315$, and $c=1$, and add the same interpolation allowance. This prices both chord losses and the *signed* second-successor angle of the very same triple, before averaging.

Write $D_0=\log X$, $m=1-9e^{-8}$, and $\langle\cdot\rangle$ for the $z_i/Z$ mean (zero for missing edges). By PNT the clip has mass $m+o(1)$, $D_0Z/X=m+o(1)$, and $M=1+o(1)$. Replacing the internal $c_i$ by $m z_i/Z$ against a bounded function costs $o(1)$: The sum of $w_i-c_i$ is at most twice the total variation of the unimodal weights, $O(D_0^2/X)$, the missing endpoints cost $O(D_0^2/X)$, and $\log p_i=D_0+O(1)$ on the clip. A shift of one index in a bounded observable changes its mean by $O(1/Z)$ by monotonicity of $z_i\le8$. Thus the adjacent term in the inequality averages to $F+o(1)$.

For the second-successor term index the edges by their right endpoint rather than their center (one shift). The [gap taper estimate](adjacent-chord-deficit.md) gives $\langle r\rangle\le 1/20+20B/m+o(1)$: The gap-weighted mean loss when inserting $(1-d/H)_+$ is at most $2mX/(HZ)=1/20+o(1)$, both logarithms on the clip equal $D_0+O(1)$, and the resulting signed sum is no larger than its budget after pooling by gap. All errors are independent of the unit phases. Therefore the full modulus satisfies

$$ \left|\sum w_p s_p e^{i\phi_p}\right|
 \le 1-m+m(0.027+0.946F+0.0315/20)+0.63B+o(1). $$

At the specified joint thresholds this is less than $0.882315+o(1)$. Conversely, if the modulus is $\ge8/9-o(1)$ and $F\le0.9005+o(1)$, then eventually $B>0.012825$. Both strict constant comparisons are checked. This limiting margin strengthens the previous asymptotic implication, but cannot replace a finite calibration on a selected list.
