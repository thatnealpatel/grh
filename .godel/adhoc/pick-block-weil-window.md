# Recovering a Weil window from blocks of right-hand zeta values

This is a paper argument, not a Lean declaration or a proof of RH. The point is to compare **two different finite restrictions** of RH positivity, with their margins, not to introduce another name for the unrestricted criterion. Only the classical right-hand logarithmic derivative and the compact-test explicit formula are needed. No assertion about an idelic trace or a quotient theta image is used.

## A block-to-window limit

Write $\xi(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)/2$ and $F(w)=\xi'/\xi(1/2+w)$. For fixed $b>0$, let $I_N=[N,e^bN]\cap\mathbb Z$, with $N$ tending through positive integers. On this block put

$$
 C_{mn}=\frac1{m+n},\qquad P_{mn}=\frac{F(m)+F(n)}{m+n},\qquad
 d_N(b)=\min_{c\ne0}\frac{c^*Pc}{c^*Cc}.
$$

Let $\lambda(b)$ be the infimum of the rational Weil form $Q(h)/\|h\|_2^2$ over nonzero complex smooth tests supported inside $(-b,b)$, **without** parity or pole-killing conditions. Use the centered normalization specified below. Then

$$
                         \lim_{N\to\infty} d_N(b)=\lambda(b).
$$

More generally the same limit holds for **any** sequence of finite nonempty sets of distinct positive real nodes $J_j$ with $M_j=\min J_j\to\infty$ and $\sum_{m\in J_j}m^{-1}\to b>0$. No bound on the gaps or the largest node is required. Thus the reciprocal sum, rather than cardinality or spacing, determines the limiting test window.

In particular, a strictly positive window floor gives eventually positive whole blocks, even though their dimension grows linearly with $N$. A strictly negative test gives a fixed negative margin on *every* sufficiently far block at the corresponding ratio. Neither assertion gives a rate. The normalization by the Cauchy Gram matrix is essential; ordinary matrix eigenvalues have no such interpretation.

### 1. The same form on two classes of functions

Extend functions on $[0,\infty)$ by zero to the line. Write $S_t h(x)=h(x+t)$ on the half-line, $A_h(t)=\int_{\mathbb R} h(x+t)\overline{h(x)}\,dx$, and $\widehat h(y)=\int h(x)e^{-iyx}dx$. For $h(x)=\sum_{m\in I_N}c_m e^{-mx}$ on the half-line, $\|h\|_2^2=c^*Cc$. On $\Re w>1/2$ there is an **unconditional** representation

$$
 F(w)=L(w)+\int_0^\infty e^{-wt}\,d\mu(t),\qquad L(w)=\tfrac12\log((w+16)/(2\pi)),
$$
$$
 d\mu(t)=\big[2\cosh(t/2)-G_{1/2}(t)\big]dt
       -\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\,\delta_{\log n},\qquad
 G_r(t)=\frac{e^{-rt}}{1-e^{-2t}}-\frac{e^{-16t}}{2t}.
$$

Indeed the two rational terms in $F$ are $1/(w-1/2)+1/(w+1/2)$; the Euler logarithmic derivative gives the atoms. The difference $\psi((w+r)/2)-\log((w+16)/2)$ is $-2\int e^{-wt}G_r(t)dt$: Differentiation gives $\tfrac12\psi'((w+r)/2)-1/(w+16)$ on both sides by the trigamma series, and both sides tend to zero along the positive real axis by Stirling and dominated convergence. This last identity holds also on $\Re w=0$ for $r=1/2,3/2$. It does **not** put $F$ on that boundary. For $r=1/2,3/2$, splitting off $e^{-rt}/(2t)$ and using $0\le (1-e^{-u})^{-1}-1/u\le1$ gives $0\le G_r\le1+(16-r)/2<9$; $G_r$ decays exponentially at infinity. The weighted total variation $M=\int e^{-2t}d|\mu|<7$: The density contributes at most $2/3+2/5+9/2$, and the atoms at most $\sum_{n\ge2}(\log n)n^{-5/2}<0.45$ by the decreasing-function integral test starting at 2.

For $N>2$ the matrix form becomes

$$
 \mathcal E(h)=\int_{\mathbb R} \ell(y)|\widehat h(y)|^2\frac{dy}{2\pi}
          +2\Re\int_0^\infty A_h(t)\,d\mu(t),\qquad
 \ell(y)=\log\frac{|16+iy|}{2\pi}.
$$

In fact $A_h(t)=\sum_{m,n}c_m\overline{c_n}e^{-mt}/(m+n)$ for $t\ge0$. To see the $L$ part, use $\log(1+w/16)=\int e^{-16t}(1-e^{-wt})dt/t$; Plancherel then replaces $1-\cos(yt)$ by $\|h\|^2-\Re A_h(t)$ after integration against $|\widehat h|^2$. Thus $\mathcal E(h)=c^*Pc$ including the factor of two on the measure term.

For smooth tests supported in $[0,2b]$, this same expression is precisely $Q$. The real-place symbol after adding $-G_{1/2}$ is $\Re\psi(1/4+iy/2)-\log\pi$. The atoms give $-2\sum (\Lambda(n)/\sqrt n)\Re A_h(\log n)$, a finite sum. The remaining density gives $\int_{\mathbb R}2\cosh(t/2)A_h(t)dt$, the **two** poles, not a positive rank-one term for all parities. Equivalently, in the repository's [unshifted compact-log formula](../../Proofs/Theorems/RationalExplicitFormula.lean), take $g(t)=e^{-t/2}A_h(t)$ and move the two pole evaluations to the geometric side. Translation between $[0,2b]$ and $[-b,b]$ preserves the entire form.

### 2. Why the support diameter is exactly $2b$

Let $H(s)=\sum c_m/(s+m)$ and $B(s)=\prod_{m\in I_N}(s-m)/(s+m)$. The proper rational function $H/B$ has poles only at the positive nodes, hence is a left-half-plane Hardy function (by partial fractions, its boundary transform lives on negative times). For $0<\eta<N$, its Plancherel norm at $-\eta$ is at most its norm on the axis, where $|B|=1$. Applying Plancherel also to $H$ gives

$$
 \|S_t h\|_2\le \min\{1,\exp[-\eta t+D_N(\eta)]\}\|h\|_2,
 \qquad D_N(\eta)=\sum_{m\in I_N}\log\frac{m+\eta}{m-\eta}.
$$

Here $|B(-\eta+iy)|\le\prod (m+\eta)/(m-\eta)$ pointwise. Thus the line norm of $H$ there is at most $e^{D_N(\eta)}$ times the line norm of $H/B$ on the axis, which equals the axis norm of $H$. Under Plancherel the shifted line norm of $H$ (measure $dy/(2\pi)$) is exactly $\|e^{\eta x}h\|_2$; restricting to $x\ge t$ bounds the tail. With $\eta=\sqrt N$, $D_N(\eta)/\eta=2\sum 1/m+O(\eta^2\sum m^{-3})=2b+o(1)$. For general $J_j$, take $\eta=\sqrt{M_j}$; the same error tends to zero since $\sum m^{-3}\le M_j^{-2}\sum m^{-1}$. This is a norm estimate on the **whole span**, not just on each generator.

There is a matching recovery result. For fixed $\sigma=2$, let $\Pi_N$ project in $L^2(0,\infty)$ onto the span of $e^{-(m-\sigma)x}$ on the block. For $k_p=e^{-px}$ and $p,r>0$ the Cauchy Gram determinant (Schur complement in the Gram matrix with one additional row and column) gives

$$
 \langle (1-\Pi_N)k_p,k_r\rangle=
 \frac{B_N(p)B_N(r)}{p+r},\qquad B_N(p)=\prod_{m\in I_N}\frac{m-\sigma-p}{m-\sigma+p}.
$$

For fixed $p$, $\log B_N(p)=-2p\sum(m-\sigma)^{-1}+O_p(\sum(m-\sigma)^{-3})\to-2bp$. The same computation applies to $J_j$, since replacing $m$ by $m-\sigma$ changes the reciprocal sum by $O_\sigma(M_j^{-1}\sum 1/m)$. The matrix elements therefore converge to those of the tail cutoff $1_{[2b,\infty)}$. The real exponentials are total by Laplace-transform uniqueness; uniform boundedness gives weak operator convergence. Since the limit is an orthogonal projection, $\|\Pi_N f\|^2=\langle\Pi_N f,f\rangle$ upgrades it to strong convergence of $\Pi_N$ to $1_{[0,2b]}$. In particular a fixed ratio does **not** approximate an arbitrary half-line test.

### 3. Passing both sides of the variational bound

For the upper bound take a smooth $h$ supported inside $(0,2b)$. Project $v=e^{2x}h'$ with $\Pi_N$, then set $h_N(x)=-\int_x^\infty e^{-2s}(\Pi_Nv)(s)ds$ on the half-line. This is a sum in the **original** block and $h_N\to h$ in the norm $\|e^{2x}h\|_2+\|e^{2x}h'\|_2$. Indeed the derivative error is $\|\Pi_Nv-v\|_2$, and backwards integration bounds the function error by half that quantity via the $L^1$ kernel $e^{-2u}$, $u>0$. The measure form is continuous in this norm by $|A_f(t)|\le e^{-2t}\|e^{2x}f\|_2^2$ and polarization. So is the log form: In its Frullani expression $|\|f\|^2-A_f(t)|\le\|f\|\min(t\|f'\|,2\|f\|)$ by half-line translation. This avoids claiming that a zero extension with a boundary jump is in whole-line $H^1$. It follows that $\limsup d_N(b)\le\lambda(b)$.

For the lower bound take unit-norm block minimizers along a liminf subsequence. For any fixed $T>2b$, the shift bound gives

$$
 \int_T^\infty |A_{h_N}(t)|d|\mu|(t)
 \le M\exp[D_N(\eta)-(\eta-2)T]\longrightarrow0.
$$

On $[0,T]$ the variation is finite and $|A_{h_N}|\le1$. The perturbation is thus uniformly bounded. The upper bound already proved bounds the energies from above; hence $\int\ell|\widehat h_N|^2dy$ stays bounded. As $\ell$ is positive and tends to infinity, this gives uniform Fourier tails. The shift bound gives spatial tightness of the zero extensions. By the $L^2$ compactness criterion (Fourier tails imply uniform continuity under translation), a subsequence converges strongly in $L^2(\mathbb R)$ to a unit vector $h$. Its support lies in $[0,2b]$ by the same shift bound for each $T>2b$. The correlations converge uniformly by Cauchy–Schwarz; local finite variation and the displayed tail estimate give convergence of the measure term. This includes a possible atom at $t=2b$: The limit autocorrelation at that point is zero because the supports overlap in at most one point. Plancherel and lower semicontinuity of the positive multiplier give $\liminf d_N(b)\ge\mathcal E(h)$.

Finally $\mathcal E(h)\ge\lambda(b)$ holds also for this possibly nonsmooth limit. Contract its support slightly toward the window center, then convolve with a smooth approximate identity small enough to stay inside. These operations converge in the Fourier norm with weight $1+\ell$: Translations are strongly continuous there, dilations near one are uniformly bounded since $1+\ell(ay)\asymp1+\ell(y)$ and strongly continuous by dense smooth Fourier data, and mollification follows by dominated convergence. The measure term is continuous under $L^2$ convergence on this common support since only $[0,2b]$ enters. This completes both inequalities; density in $L^2$ **alone** would not justify the last step.

There is a useful boundary case for the general sets: If $\sum 1/m\to0$ while $M_j\to\infty$, the minimum tends to $+\infty$. Otherwise a subsequence of unit minimizers would have energies bounded above. The lower-bound compactness argument applies for every $T>0$ and produces a unit $L^2$ limit supported at $0$, an impossibility. Thus for a fixed budget $b>0$, the asymptotic worst lower bound over **all** escaping sets with $\sum 1/m\le b$ is $\lambda(b)$. To see the lower bound, take a subsequential budget limit in $[0,b]$ and use monotonicity of the window infimum. For sharpness take contiguous blocks, deleting the uppermost nodes until the budget is at most $b$; the resulting sum still tends to $b$.

## Consequences, controls, and the missing estimate

* **Zeta.** By Weil's criterion, RH is equivalent to $\liminf_N d_N(b)\ge0$ for each positive integer $b$. If RH fails, a single compact negative witness furnishes some $b$ and $\delta>0$ with $d_N(b)<-\delta$ for every sufficiently large $N$. Conversely, the [compact-window preprint](https://arxiv.org/abs/2608.24827), corollary “Positivity for arbitrary test functions,” would give $\lim d_N(0.8)\ge8.9\times10^{-18}$ by the theorem. This uses the preprint's stated result; we checked its form and support conventions, not its computational certificate. At a zero limit nothing here determines the signs of the finite matrices.
* **Sampling prior art.** The unrestricted Pick criterion is classical, not the contribution claimed here. See [Hinkkanen](https://doi.org/10.1080/17476939708815042) and [Lagarias, p. 218](https://matwbn.icm.edu.pl/ksiazki/aa/aa89/aa8932.pdf). Under RH, $F$ is positive real in $\Re w>0$, so all Pick matrices are PSD. Conversely, PSD on all finite subsets of a full integer tail gives by Nevanlinna–Pick and normal families a Schur interpolant $S$ for $(F(m)-1)/(F(m)+1)$. On $\Re w>1$ the Euler product and Stirling give holomorphy and $F(w)=O(1+\log(2+|w|))$. There $((1-S)F-(1+S))/(w+1)^2$ is bounded, and vanishes on a non-Blaschke sequence, so is identically zero. Since $S$ cannot attain 1 in the interior, $(1+S)/(1-S)$ continues $F$ holomorphically to $\Re w>0$. This excludes any right-of-line zero. It is **not** a uniqueness argument on a fixed reciprocal-budget set. The limit above instead identifies a variational quantity at *each* budget.
* **An unconditional finite-matrix control.** For any finite set of distinct real nodes $m\ge2048$ with $\sum 1/m\le 1/384$, one has $P\succeq\tfrac12 C$, regardless of cardinality. In the same shift estimate take $\eta=1024$. Since $\log((1+x)/(1-x))\le3x$ for $0\le x\le1/2$, $D\le\eta/128$. There are no atoms on $[0,1/64]$, and the density there has magnitude less than 12 by $G_{1/2}<9$. For a unit vector $|\int A_h d\mu|\le 12/64+7e^{-8+1/32}$. Since $\ell\ge\log(8/\pi)$, subtracting twice this error leaves more than $1/2$. This is a sign proof at finite nodes, not a numerical eigenvalue computation.
* **Growing conductors.** For a primitive nonprincipal Dirichlet character $\chi$ of conductor $q$, let $F_\chi$ be the logarithmic derivative at $1/2+w$ of the standard completion $(q/\pi)^{(s+a)/2}\Gamma((s+a)/2)L(s,\chi)$, $a=0,1$. Use the Hermitian numerator $F_\chi(m)+\overline{F_\chi(n)}$ (equivalently conjugate the coefficient vector in the preceding integral convention). The log multiplier gains $\log q$; the measure loses the pole terms, uses $G_{1/2+a}$, and multiplies the atoms by $\chi(n)$. Its weighted variation is still $<7$. Fix $0<\epsilon<1$. There is $N_\epsilon$ such that, uniformly over finite sets of distinct real nodes $m\ge N_\epsilon$ with $\sum 1/m\le(1-\epsilon)\log\log q$,

  $$ P_\chi\succeq (\log q-o_\epsilon(\log q))\,C\qquad(q\to\infty). $$

  To see this put $A=\log\log q$, $T=(2-\epsilon)A$, and $\eta=8/\epsilon$. Choose $N_\epsilon$ so that each log factor in $D$ is at most $(2+\epsilon/4)\eta/m$. Up to $T$ the variation is $O((1+T)e^{T/2})=o_\epsilon(\log q)$, using $\Lambda(n)\le\log n$ and $\sum_{n\le X}1/\sqrt n\le2\sqrt X$. Beyond $T$ it costs at most $7\exp[D-(\eta-2)T]\le7e^{-(2+4\epsilon)A}$. This is a uniform partial positivity theorem, not GRH for any fixed conductor. The [three-character Lean file](../../Proofs/Props/DirichletThreeCompletedEdges.lean) uses a different completion without the conductor power; the $\log q$ gain does not follow from that file.

**Where to push.** For zeta the direct total-variation proof loses the signs of both the prime translations and the pole cancellation. Increasing $N$ cannot repair this: At a fixed ratio the exact limiting problem is the *same* Weil window. A falsifiable next step is a lower bound for the whole generalized quotient at a specified larger ratio, for example $b=1$, with all primes $n<e^2$ and both pole terms retained. A lower bound on a trial subspace is not one for this quotient. The `cmd/ff` frequency-mean approach instead bounds an averaged prime packet by close prime pairs; taking absolute values retains the continuous-density contribution near zero frequency. It does not bound the signed off-diagonal form on every test. Likewise the [theta Gram handoff](rational-theta-gram/handoff.md) bounds integration errors at a fixed grid, not projection onto the global theta image. Neither supplies the missing lower bound. No novelty claim is made for the Cauchy product identity, model-space argument, or the use of right-hand samples.
