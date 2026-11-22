# Computing a fixed rational theta-band trace without erasing its tail

**Status:** The fixed-band floor core, trace formula, Gram-tail certificate, and clipping obstruction were independently reviewed. They are not Lean theorems. The final section gives an open target, not a convergence rate. Scope: The rational unramified even real-band model with both zero modes removed, half twist, and Sobolev degree four. This is an unsplit global-model calculation, not a calculation of the manuscript's selected shell, a comparison of positive-width and printed zero-width metrics, or a proof of RH. Sources checked against accepted `2fbdcd8d9b109f0d501faded21521ee96082cd58`. The linked Lean theorem supplies band exhaustion; the fixed-band floor core and Gram estimates below are separate arguments.

## What is computed

Use $0\le\alpha<1/2$, $w(x)=e^{2\alpha |x|}(1+x^2)^2$, and $H=L^2(w\,dx;\mathbb C)$. Fix $B>0$. Write $Q_B$ for the orthogonal projection onto the closure $G_B$ of the profiles $e^{x/2}\Theta(a,e^x)$ of even Schwartz $a$ satisfying $a(0)=\widehat a(0)=0$, $\operatorname{supp}\widehat a\subset[-B,B]$. Multiplication by $\sqrt w$ is the unitary to Lean's $L^2(dx)$ coordinate in [`rationalThetaWeightedEvenImage`](../../../Proofs/Lemmas/RationalThetaWeightedLog.lean), at twist $1/2$, $s=4$. Do not use unmodified log convolution after this change of coordinates.

For smooth compact $\rho$, $b\in C_c^\infty(0,\log 2)$, put $f=b'$ and $Tu=M_\rho A_fu$, $A_fu(x)=\int f(y)u(x-y)\,dy$. We compute $\operatorname{Tr}(TQ_B)$, not a trace with a terminal projection deleted. For the model's full theta projection $P$, invariance gives $PA_fQ_B=A_fQ_B$; this is not commutation. See [the weighted trace repair](../../obligations/trace-hardy-diagonal-q.md). Three cutoffs have different meanings: The grid discretizes the **band**, the integration window for the Gram matrix defines or approximates the **metric**, and $\rho$ truncates **output position**. Only the last one occurs in $T$.

## Floor core at fixed band

With $D=\widehat a|_{[0,B]}$, Poisson inversion gives $v_a(x)=2e^{-x/2}\sum_{n\ge1}D(ne^{-x})$. Here $D(0)=D(B)=0$ and $\int_0^B D=0$. Put

$$F_t(x)=2e^{-x/2}\big(\lfloor te^x\rfloor-(t/B)\lfloor Be^x\rfloor\big),\quad 0\le t\le B.$$

Then $G_B$ is the closed **complex** span of the $F_t$. Indeed, summing $D(u)=-\int_u^B D'(t)dt$ over the positive samples gives $v_a=-\int_0^B D'(t)F_t\,dt$; the compensation integrates to zero because $\int tD'=0$. The compensated count is bounded by one and vanishes for $x<L=-\log B$. Its twisted envelope is square integrable in $H$ because $1-2\alpha>0$. Continuity of $t\mapsto F_t$ in $H$ follows by domination off the countably many jump points in $x$. The integral is therefore also an $H$-valued integral.

Conversely, take $S_t=1_{(0,t]}-(t/B)1_{(0,B]}$. Squeeze its zero extension affinely into $[2\epsilon,B-2\epsilon]$ in the horizontal variable, and convolve with a smooth unit-mass bump of radius $\epsilon$. The resulting $D_\epsilon$ have zero integral, uniformly bounded variation, and support compactly inside $(0,B)$. Their even extensions are admissible Fourier data. For $q>0$, comparison to interval averages on $[(n-1)q,nq]$ gives $|\sum_{n\ge1}D_\epsilon(nq)-q^{-1}\int D_\epsilon|\le\operatorname{Var}(D_\epsilon)$. With $q=e^{-x}$, finite sampling converges off a countable set. This bound gives dominated convergence in the **full** metric to $F_t$. At $\alpha=1/2$ even $F_{B/2}$ is not in this space.

## Finite matrices and the correct limit

Let $m=2^d\ge2$, $h=B/m$, and for $k=2,\dots,m$ use the columns

$$E_k(x)=2e^{-x/2}\lfloor k\{he^x\}\rfloor=F_{kh}(x)-k F_h(x).$$

Since $E_m=-mF_h$, these span all the dyadic $F$-nodes at this depth. For the largest nonzero coefficient at $k$, the interval $1/k<he^x<1/(k-1)$ detects it. Thus they are independent. At fixed $B$ the spaces nest, and continuity of the $F$-nodes makes their union dense in $G_B$. This does not assert nesting at unrelated pairs $(B,m)$.

Use synthesis $V c=\sum_k c_k E_k$, $G=V^*V$, and $C=V^*TV$. In entries $G_{ij}=\int E_i E_j w$, $C_{ij}=\int E_i\rho (A_f E_j) w$ (the $E_i$ are real; do not conjugate $f$ or $\rho$). Only $G$ needs an infinite integration range. On the support of $\rho$ the input of $A_f$ is confined to a known compact enlargement. If desired compute $A_{b'}E_j$ by distributional differentiation:

$$ A_{b'} E_j=-\tfrac12 A_b E_j+2(H_{jh}-jH_h),\qquad H_t(x)=\sum_{n\ge1}\sqrt{t/n}\, b(x-\log(n/t)). $$

The upper bound on $n$ here is $B\exp(\sup\operatorname{supp}\rho)$, since the test is supported in positive log time. Now $VG^{-1}V^*$ is the grid orthogonal projection. Finite-rank cyclicity, then strong convergence of the self-adjoint grid projections, give

$$\operatorname{Tr}(TQ_B)=\lim_{d\to\infty}\operatorname{tr}(G^{-1}C).$$

For the trace-norm step: On the compact input and output intervals the weight and its inverse are bounded. Smooth convolution localized there factors through $H^2$ of a containing circle with summable inclusion singular values. Thus $T$ is trace class; finite-rank approximation gives trace-norm convergence after right multiplication by the bounded, strongly convergent self-adjoint projections. Next, at fixed $\rho$, [`Masullo.tendsto_rationalThetaWeightedEvenBand_projection`](../../../Proofs/Theorems/RationalThetaBandClosure.lean) gives the cofinal band limit to $\operatorname{Tr}(TP)$ by the same argument. **Only then** exhaust position. The accepted result is a band-exhaustion theorem, not this fixed-$B$ floor description, a grid rate, or a statement about finite auxiliary levels.

## A relative error certificate for the entire Gram matrix

For a coefficient vector $c$, set $H_c(u)=\sum_{k=2}^m c_k\lfloor ku\rfloor$ on $0\le u<1$, $r=he^x$, and $W_h(r)=r^{-2}w(\log(r/h))$. Direct change of variables gives

$$c^*Gc=4h\int_0^\infty |H_c(\{r\})|^2 W_h(r)\,dr.$$

Fix an integer $N\ge1$. Form $\widetilde G_N$ by keeping $0<r<N$ exactly and replacing the entire tail by its **period-mean matrix**, i.e. adding to the quadratic form

$$4h\left(\int_N^\infty W_h(r)\,dr\right)\left(\int_0^1 |H_c(u)|^2\,du\right).$$

This is not a tail cutoff. With $K_N=(1+1/N)^5$, in Loewner order (quadratic-form order),

$$K_N^{-1}G\;\preceq\;\widetilde G_N\;\preceq\;K_NG,$$
$$\left|\operatorname{tr}(\widetilde G_N^{-1}C)-\operatorname{tr}(G^{-1}C)\right|\le (K_N-1)\|T\|_1.$$

Indeed $\log W_h(e^v)=-2v+2\alpha|v-\log h|+2\log(1+(v-\log h)^2)$ has Lipschitz constant at most $2+2\alpha+2\le5$, including across its cusp. On any period $[n,n+1]$, $n\ge N$, $W_h$ differs from its own period mean by at most the factor $K_N$ in either direction. Multiply by the nonnegative periodic integrand and sum. The interior is exact, so the same bracket holds for the full matrix. For the trace, $U=VG^{-1/2}$ is isometric, $G^{-1/2}CG^{-1/2}=U^*TU$ has trace norm at most $\|T\|_1$, and $G^{1/2}\widetilde G_N^{-1}G^{1/2}$ has spectrum in $[K_N^{-1},K_N]$. Trace duality proves the bound without a factor of $m$ or the condition number of $G$. It applies to arbitrary complex $C$ of this operator form. The estimate is a mathematical integration error, not a floating-point inversion guarantee.

Implementation: Split each exact period at fractions $j/k$, $2\le k\le m$, and also split the weight integral at $r=h$ if needed. On each constant cell, the scalar mass is $4h\int W_h=4\int e^{-x}w(x)\,dx$. On each side of zero these have elementary exponential-polynomial primitives, including at infinity since $\alpha<1/2$. Skip $0<r<1/m$, where **every column is zero**; do not integrate the bare singular weight there. The mean matrix uses rational interval lengths. An often tighter certificate keeps the interior exact and bounds just the added tail by factors $K_N^{\pm1}$. A fixed relative target for the metric uses the same $N$ at any grid dimension, width in range, or band. This does not bound the distance from the finite grid projection to $Q_B$.

## Why clipping the metric is not an alternative

For every finite $X>L$, the restrictions of the genuine fixed-band two-moment core are dense in $H_X=L^2([L,X],w\,dx)$. To see this put $q(x)=2e^{-x/2}D(e^{-x})$. On the observation interval the sum is $\sum_{n\ge1}n^{-1/2}q(x-\log n)$ with zero input below $L$, a finite triangular map. For a target $\phi\in C_c^\infty(L,X)$, extended by zero, its inverse there is $q(x)=\sum_{n\ge1}\mu(n)n^{-1/2}\phi(x-\log n)$. Finite rearrangement uses $\sum_{d\mid n}\mu(d)=1_{n=1}$. This locally finite smooth formula vanishes near and below $L$; cut it off smoothly beyond $X$, keeping it unchanged up to $X$. Recover $D$ and correct its integral with a bump strictly inside $(0,e^{-X})$, invisible to every observed sample. Even extension gives admissible Fourier input. This realizes the dense targets exactly. Bounded restriction and the full-metric floor-span identity now imply density of the restricted dyadic grids.

If both the metric and columns are restricted to $[L,X]$ **before** grid refinement, their finite projections tend to the identity on $H_X$, not the restriction of $Q_B$. In this experiment take $X\ge\sup\operatorname{supp}\rho$. The numerator is unchanged: Causality means no input above $X$ and the columns already vanish below $L$. Use the Moore–Penrose inverse of the clipped Gram matrix if some columns are zero. For $T_X$ the compression by zero extension and restriction, the above trace-norm argument gives the limiting trace $\operatorname{Tr}T_X=f(0)\int_L^X\rho=0$. The diagonal identity follows in the unweighted coordinate by a smooth Fourier expansion of $f$ on a circle exceeding the difference interval, with any periodic wrap kept off that interval; bounded weight multipliers cancel on the diagonal. This conclusion is exact even if $X$ is later exhausted. In contrast, [the fixed-annulus witness](../../obligations/trace-section-collar-q.md) (short scaled derivative control, lines 114–150 at the cited revision) supplies **some** fixed smooth $\rho$ and $f$ at a good width for which the true cofinal level limit is nonzero. Hence some sufficiently large finite $B$ already differ. This does not assert nonzero true trace for every choice of data. The finite Möbius inverse is related to [the level-transport test](../../obligations/trace-level-transport-q.md); that inverse alone does not compare the clipped and whole-line Gram traces.

## Reproducible finite control

Run the [finite control](control.py) from the repository root with SageMath (tested with 10.9):

```sh
sage .godel/adhoc/rational-theta-gram/control.py
```

It uses 160-bit Sage real balls and rational breakpoints, not sampled quadrature. Take $B=2$, $m=2$, $\alpha=1/4$, $X=0$. Then $h=1$ and on the first plateau $(-\log 2,0)$ we have $E_2=2e^{-x/2}$. Choose a nonnegative smooth nonzero $b$ in $(0,\log2)$ and nonnegative smooth nonzero $\rho$ compactly inside $(-\log2+\sup\operatorname{supp}b,0)$. Normalize $-M_{b'}(1/2)=1$ and $\int\rho E_2^2 w=1$ by positive rescaling. Since $M_{b'}(1/2)=-\frac12\int e^{y/2}b(y)\,dy$, both normalizations are possible. The one-column numerator is **exactly** $C_{22}=-1$ for both metrics, no approximation of $b$ needed. The full denominator exceeds the clipped denominator strictly because later periods carry positive mass. This isolates the metric as the sole difference. The control also checks a signed linear combination of seven columns at $m=8$ against narrower enclosures. With $N=512$, the whole-line one-column trace is enclosed in $[-0.0006257,-0.0006160]$, whereas the clipped trace is approximately $-0.13971156$. These are finite-grid values, not band-limit values.

## Open estimate for a growing observation window

Bound the projection error for a specified grid on localized convolution tests, not just the Gram integration error. One target is $|\operatorname{Tr}(M_{\rho_R}A_f(P-P_{B(R),m(R)}))|=o(1)$ for an explicit joint choice of band and dyadic grid, with $\rho_R$ a smooth bounded exhaustion on $[-R,R]$. At fixed $R$, orthogonal-projection convergence gives existence of sufficiently fine choices, not a schedule. For investigating a schedule, the certificate above removes the separate source of error from the infinite Gram integral: It suffices to make $(K_{N(R)}-1)\|M_{\rho_R}A_f\|_1=o(1)$. One can take $N(R)/(1+R)\to\infty$ for uniformly bounded $\rho_R$ and fixed $f$: Partition the output into unit intervals, each using input on a uniformly bounded enlargement; the supremum of the weight-root ratio on each such block is uniform by weight moderation, and the compact smoothing factorization above gives uniformly bounded trace norm per block. Sum over $O(1+R)$ blocks. None of this estimates the grid projection error or evaluates the scalar after the required limits. In particular it neither produces the missing $-M_f(1/2)$ nor authorizes replacing the global iterated limit with the joint local cutoff.

A concrete sufficient estimate is available without access to the kernel of $P$. Use the nested cofinal grids $B_j=2^j$, $h_j=2^{-j}$, $m_j=4^j$, $j\ge1$. Nesting follows by bisecting integral-zero frequency steps and extending them by zero onto the larger band; the old steps lie in the new integral-zero cell-step space. The columns synthesize the images of all such steps because the $m-1$ independent differences $1_{(0,kh]}-k1_{(0,h]}$ span the codimension-one step space. For any fixed dyadic-radius band, this chain contains all its sufficiently coarse-to-fine dyadic steps in the union, so the chain exhausts $P$. Write $P_j$ for its grid projectors. On a unit output block $[l,l+1)$, only input in $[l-1,l+1]$ matters. Periodize $f$ with period 4 on their differences $[-1,2]$, where its periodic extension agrees with $f$. Its smooth Fourier expansion gives packets with output $\rho_R 1_{[l,l+1)}e^{i\pi n x/2}$ and input representing vector $w^{-1}1_{[l-1,l+1]}e^{i\pi n x/2}$; their norm product is uniformly bounded. For any such vector normalized to a unit vector $u$ (omit zero packets), $p_j(u)=\|P_j u\|^2=c^*G_j^{-1}c$ for $c=V_j^*u$. For an **explicit** schedule $j(R)$, a sufficient successor bound is

$$\sup_{u}\ \sup_{k\ge j(R)}\big[p_k(u)-p_{j(R)}(u)\big]=o((1+R)^{-1}),$$

where both packet types with $|l|\le R+1$, $|n|\le 1+R$ are tested. Indeed $P_k-P_j$ is an orthogonal projector: Its pairing on two unit packets is bounded by the geometric mean of their energy gains. Sum with the absolutely summable Fourier coefficients over $O(1+R)$ blocks. The discarded frequencies cost $O_{f,a}((1+R)^{1-a})$ for arbitrary fixed $a>1$ by smoothness. Let $k$ tend to infinity to obtain the desired trace error. The all-finer-grid supremum is essential: Checking two successive meshes numerically does not certify it. This is a sufficient open estimate, not a necessary condition for scalar cancellation, and controlling it would validate a schedule rather than evaluate its limit.
