# The rational singleton trace at the diagonal

**Status:** Provisional pinned-text audit, plus a project argument in the rational trivial compact isotype at $a=1/2$, $I=\{0\}$, and $s=2$. This constructs the global Haar diagonal in the required order in the sense of an $L^1$ limit of box averages. An independent Yah reviewer checked the source interfaces and the $L^1$ argument. It is not a Lean declaration or a local-to-global comparison. Locators below refer to layout extraction of the [digest-matched PDF](../sources/masullo/README.md), not to rendered-page review.

## What the cited kernels supply

- **Domain and order:** Definition 10.4.3.2, p. 470, (10.4.3.26)–(10.4.3.27), names the singleton kernels for $s\ge3$. Theorem 10.4.3.4, pp. 470–471, says $s>1$ but uses those names. Even extending the formulas to $s=2$, (10.4.3.25), (10.4.3.28), and the calculation (10.4.3.32)–(10.4.3.35) give $PA$ and $(1-P)A$, where $P=P_a^{\rm spec}$ and $A=A(\phi)$. The first equality in (10.4.3.29) tests only on the geometric subspace, where $A$ stays in that subspace. This does not identify $A(1-P)$ as an operator on the whole space. The [order audit](trace-spectral.md#which-operator-does-the-series-represent) explains why the difference can affect a fixed output cutoff even if the uncut spectral traces agree.
- **Measure and topology:** In (10.4.3.25) the input integral is against $w(y)^{-1}d\mu(y)$, where $w(y)=(1+|\log|y|_F|^2)^{s/2}$. Formula (10.4.3.26) absorbs that factor and (10.4.3.28) uses Haar. Dividing this Haar kernel by $w(y)$ gives the kernel relative to $w\mu$, as in the first part of (10.4.3.30). These are product-measure representatives, not diagonal values. In the extraction, the second formula of (10.4.3.30) also labels an output-cutoff *spectral* kernel as geometric, contrary to (10.4.3.36) and the subtraction in (10.4.3.37).
- **Diagonal and limit order:** Theorem 12.1.1.3, pp. 502–503, adds diagonal smoothing but again assumes $s\ge3$. Equations (12.1.1.20)–(12.1.1.22) keep the singleton space and the projection-after-convolution order fixed and exhaust the group with $\Lambda\to\infty$, $\varepsilon\Lambda=o(1)$. They do not change the width or cap. The proof on p. 503 invokes (12.1.1.2), p. 499, for the Haar-relative kernel without checking that the weight conversion commutes with diagonal averaging. Nor is this a comparison with the two independently growing local cutoffs of Theorem 12.4.1.1, p. 514. The latter concerns an $S$-local Paley–Wiener kernel, and in the extraction the intervening §12.3 contains a heading and an “Include section” note rather than an identification of the operators.

Thus Theorem 10.4.3.4 does not by itself supply the $s=2$ Haar diagonal of the companion $A(1-P)$ or its normalized local evaluation.

## A trace-norm interface for the repaired Haar diagonal

Use $x=\log|g|_{\mathbb Q}$ and normalize the compact group to volume one, as in the [singleton trace repair](trace-spectral-q.md). Let $H=L^2(\mathbb R,w\,dx)$, $w(x)=1+x^2$, and $T=AP$ on $H$. The singleton repair gives $T$ trace class at $s=2$. Conjugate by $U:H\to L^2(dx)$, $Uf=\sqrt w f$, and write $S=UTU^{-1}$. If $h$ is the Hilbert–Schmidt kernel of $S$ relative to $dx$, the Haar-relative kernel of $T$ is

$$K(x,y)=\sqrt{w(y)/w(x)}\,h(x,y).$$

For a trace-class $S$ with singular expansion $S=\sum_j\sigma_j u_j\otimes v_j^*$ define its trace density by

$$D_S=\sum_j\sigma_j u_j\overline{v_j}\quad\text{in } L^1(dx).$$

Cauchy–Schwarz gives $\|D_S\|_1\le\|S\|_1$. For every bounded measurable $b$, $\int bD_S=\operatorname{Tr}(M_bS)$ by the rank-one formula and absolute convergence. This characterizes $D_S$ independently of the expansion and implies $\|D_{S_1}-D_{S_2}\|_1\le\|S_1-S_2\|_1$.

Let $C_\delta f$ be normalized averaging on $[x-\delta,x+\delta]$ and $B_\delta$ the normalized double average over the square of that interval centered on $(x,x)$. Then $B_\delta h=D_{C_\delta S C_\delta}$: For rank one this is $(C_\delta u)\overline{(C_\delta v)}$, and for the singular expansion the identity passes to the limit in $L^1$. Indeed, for every fixed center the square average is continuous on $L^2(dx\,dy)$, and the integrals of the absolute square averages of the rank-one terms are bounded by $\|C_\delta|u|\|_2\|C_\delta|v|\|_2\le\|u\|_2\|v\|_2$. This also yields $\|B_\delta |h|\|_1\le\|S\|_1$, by applying the same bound to finite sums and passing to the limit. The self-adjoint contractions $C_\delta$ tend strongly to the identity by translation continuity in $L^2$. Approximation by finite rank then gives $C_\delta S C_\delta\to S$ in trace norm.

On the averaging square, $|x'-y'|\le2\delta$ and $|\partial_x\log w|\le1$, so $|\sqrt{w(y')/w(x')}-1|\le e^\delta-1$. Consequently

$$\|B_\delta K-D_S\|_1\le(e^\delta-1)\|S\|_1+\|C_\delta S C_\delta-S\|_1\longrightarrow0.$$

In particular the error against **any** output cutoff $0\le\rho\le1$ is bounded by this same quantity. This is an integrated $L^1$ repair; the estimate does not assert convergence at each center. Write $f$ for the log profile of the radial test $\phi$. On the common positive-log tests, the convolution kernel $f(x-y)$ vanishes on all sufficiently small averaging squares along the diagonal. Thus $G(x,y)=f(x-y)-K(x,y)$ for $A(1-P)$ has double-averaged Haar diagonal tending in $L^1$ to $-D_S$. Integrating against $\rho$ gives the limit $-\operatorname{Tr}(M_\rho AP)$, since $U$ commutes with $M_\rho$. The estimate permits $\rho$ to vary as the squares shrink. Exhausting the line with the global output cutoffs therefore gives minus the capped sum by the singleton trace calculation. This uses neither a change of width nor a trace of the uncut regular convolution.

## The remaining comparison

The repaired global density reduces the missing bridge to an equality of integrated diagonals on the common tests: The normalized $S$-local and orbital contributions, including the two Mellin corrections, must give the same limit as the Haar density of $A(1-P)$ above. If proposed approximants can be transported to the same $L^2(dx)$, trace-norm convergence at a fixed position cutoff is sufficient for $L^1$ convergence of their trace densities there. To remove the cutoff in the manuscript's order, control the scalar cutoff errors in that order too. This is a sufficient test, not a necessary topology for an integrated trace calculation.

Hilbert–Schmidt convergence or operator-norm convergence alone cannot replace this test. On $L^2(dx)$ take $n$ orthonormal smooth bumps supported in disjoint subintervals of $(0,1)$ and let $E_n$ be their orthogonal projection. The smooth kernels of $E_n/n$ tend to zero in Hilbert–Schmidt norm ($n^{-1/2}$) and operator norm ($n^{-1}$); their diagonal integrals against a fixed compact cutoff equal to one on $[0,1]$ are all $1$. This is a topology control, not a counterexample for the actual local level operators. The next comparison must identify those actual operators or their integrated trace contributions; existence of the rational singleton Haar diagonal no longer requires extending the cited kernel theorem. The [full-versus-capped equality](trace-divisor-uniqueness.md#the-common-test-class-and-the-missing-comparison) and the real-place normalization check remain open.
