# Why coefficient refitting alone cannot shorten this mask

Keep **both** first masks from `paired-10-2.txt`. Delete any one of the six indices in [the sparse separator](sparse-10-2.md), leave the other five indices fixed, and allow *arbitrary real* coefficients $a_i$ on them. Even with the ideal sine-square price at $t$, the old separator inequality misses by more than $10^{-5}$:

$$P-\frac{C_1}{2\cos(\pi/12)}\int |H_t|\,d\mu-U(h)<-10^{-5},\qquad h=\sum_i a_i e^{il_i\varphi}.$$

Here $C_1=\cosh(39/20)/3$, $\varphi=x/25$, and $U=C_1\int\max_\theta\Re(H_{3t}e^{i\theta}+h e^{2i\theta})\,d\mu$. The finite $t$ construction that recovers $H_t$ cannot charge less than its ideal cost, by the triangle inequality for its positive spatial masks. This obstruction is to *one sufficient test* on six specified supports. It says nothing against moving the five shifts, refitting the first masks, or a different certificate.

**Two easy one-sided prices.** For an upper bound on the prime-side minimum $P$ of [the paired comparison](paired-10-2.md), split at all knots and at zero. On each subcell pick one trial $u\in[0,1]$ near the numerical minimum at the exponential barycenter. For fixed $u$ the integrand before weighting is affine, so its exact integral is its value there times the cell mass. Use the same rule on the entire final tail, with barycenter one past the endpoint. This gives $P<.164063$ without having to enclose any optimizer. For a lower bound on the trace norm at $t$, sum the moduli of cell integrals of $H_t$ on the folded period; this gives a cost $>.160721$ after the stated factor.

**Uniform lower price at $3t$.** For each deleted index use one probability vector on the angles $2\pi j/96$ per spatial cell. The distribution is constant on its cell; hence it prices the full angular maximum from below there. Let $b$ be the integral of the averaged first term and $e_i$ the integrals of the averaged second columns, without $C_1$. Then

$$U/C_1\ \ge b+\sum_i a_i e_i\ \ge b-\eta\|a\|_1,\qquad \eta=\max_i|e_i|.$$

To handle the residual **without assuming bounded multipliers**, the maximum is also at least $|h|$: At a phase aligning the second term, average the evaluations at that phase and its antipode. Write $G_{ij}=r^{|l_i-l_j|}$, $r=e^{-1/50}$. This is the real trace Gram matrix (the folded integral of the squared modulus for real coefficients). In increasing index order $G_{ij}$ for $i<j$ is the product of consecutive correlations $p_k=r^{l_{k+1}-l_k}<4/5$. The inverse has quadratic form

$$v^T G^{-1}v=v_1^2+\sum_{k=1}^{4}(v_{k+1}-p_k v_k)^2/(1-p_k^2).$$

Indeed the consecutive difference rows in this formula whiten $G$, by its product identity. Using $(y-px)^2\le(1+p)(y^2+p x^2)$ gives $G^{-1}\preceq9I$ (interior coefficient at most $5+4$, endpoints no larger). Consequently

$$\|a\|_1\int |h|\,d\mu\ \ge\int |h|^2\,d\mu=a^TGa\ \ge \|a\|_1^2/45.$$

This also covers fewer than five nonzero coefficients, with zero treated separately. Thus $U\ge C_1 b/(1+45\eta)$; the tiny residuals are *paid for*, not rounded to zero.

**Reproduce.** From the repository root run `sage .godel/bob/check-frozen-deletions.py`. HiGHS only nominates cell probabilities; the checker converts them to nonnegative rationals of sum one and recomputes $b$ and the residuals in ball arithmetic. Moment evaluation uses the folded density $(1-r^2)/(\pi D)$ with $D=1+r^2-2r\cos\varphi$. For a cell, $J_k=\int e^{ik\varphi}\,d\mu$ starts with its exact CDF mass $J_0$. For $J_1$, the real part follows by rearranging $D$ and the imaginary part by integrating $D'/D$. Multiplication by $D$ gives $(1+r^2)J_k-r(J_{k+1}+J_{k-1})=(1-r^2)\int e^{ik\varphi}d\varphi/\pi$. These are interval integrals over the entire folded trace, not evaluations at sample points. For the omitted negative half use the conjugate phases. There is no inference here about zero answers or measured lower bounds at actual failures.
