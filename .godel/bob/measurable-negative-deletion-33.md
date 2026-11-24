# Measurable negative laws for delete-33 at depth 39/20

**Result.** The [same reference and full-negative serialized dual](joint-tail-deletion-33.md#full-negative-replacement-with-a-measurable-tail) certify $M-8/9<-4.13\cdot10^{-8}$ with **no slab-constancy assumption** on either $[-144/25,0)$ or $[29/5,\infty)$. On those two regions take any measurable family of probability laws on $0\le u\le1$, independently at each $t$. Keep $X=0$ to the left of $-144/25$ and the reference laws unchanged on $[0,29/5)$. Keep the two unfolded first caps and the simultaneous three-site second constraints for the third-harmonic field, exactly as in the [joint price](joint-tail-deletion-33.md#joint-price). No Alpöge input is used. This does not release the pre-tail or the left cutoff, weaken the unfolded caps, or establish all-real infeasibility at this depth.

## Price and signed kernels

Write $X=2u^2-1$, $T(X)=4X^3-3X$, $(A,B,U)=\mathbb E(X,T(X),u)$, and $M=\int_0^\infty te^{-t}U(t)\,dt$. Let $a,b$ be the summed price densities in [(1)](joint-tail-deletion-33.md#joint-price) and let $S$ sum the weighted reference slacks. The scaled cut-functional changes sum to at most $S$: each first cut uses a normalized unit direction, and the second tangent drops the nonnegative quadratic at the difference field. Thus

\[
M-8/9\le (M_*-8/9)+S+G_-+G_{\rm tail},\qquad
G_- = \int_{-144/25}^0[-a(A-A_*)-b(B-B_*)]dt.
\]

Here $G_{\rm tail}$ is the unchanged tail score from (1); the pre-tail contributes zero. The sign of the price is negative for the competitor's cut densities and positive for the reference's. The negative mass is identically zero, not a quadrature approximation. The identity for the cut linear functionals extends from steps to all these laws by continuity in $L^1(e^{-t/2}dt)$ on the half-line, as in (1); only the moments of the competitor need be measurable. Endpoints are immaterial to the Lebesgue integrals.

The second primitive kernels are $\mathcal D(y)=(2+|y|)e^{-|y|/2}$ and $\mathcal K(y)=(1+y_++y_+^2/2)e^{-|y|/2}$. With the common multiplier $e^{-t/2}$ their negative derivatives use $J(y)=(1+y_+)e^{-|y|/2}$ and $G(y)=y_+^2e^{-|y|/2}/2$, respectively, for **both** signs of $y$. For example, with $y=t-s$ the weighted $J$ density is $e^{-s/2}$ for $t<s$, and $e^{s/2}(1+t-s)e^{-t}$ for $t\ge s$; the weighted $G$ is zero for $t<s$ and $e^{s/2}(t-s)^2e^{-t}/2$ otherwise. Integrating from $t$ to infinity gives the stated weighted primitives, also at $t=s$.

In `tail_data`, write $p$ for the evaluation index, $k_i$ for the reference indices, $d_h$ for the Laurent shift step, $H=Dd_h$ for degree $D$, and $J_0=k_{\max}-k_{\min}$. For $p\in[l,r]$ the full signed difference-kernel argument $p-k_i+m d_h$ lies in $[d_l,d_r]=[l-k_{\max}-H,r-k_{\min}+H]$. The product exponents add as

\[
(k_i-k_{\min})+(H-m d_h)+(p-k_i+m d_h-d_l)=J_0+2H+p-l.
\]

The middle factor's sign uses $q_m=q_{-m}$. In the sum-kernel array the base argument $p+k_i$ lies in $[k_l,k_r]=[l+k_{\min},r+k_{\max}]$, and the shifts are applied within that array. The product exponents give $(k_{\max}-k_i)+(p+k_i-k_l)=J_0+p-l$. Thus both coefficients are the full signed kernel sums, with the absolute-value exponential table covering the extreme arguments. No condition $k_{\max}\le l$ is required. The checker compares these two convolutions, in both modes, to explicit signed sums on three nonuniform reference knots with signed jumps and evaluation points before, between, at, and after the knots, including arguments equal to zero in both kernels.

## Continuum-to-cell bound

Let $f(t,X)=-a(t)X-b(t)T(X)$ for $-1\le X\le1$. On each cell of width $h=1/1600$ take the interpolating quadratic in $t$ at its endpoints and midpoint, for **each fixed atom**. All the second-kernel branch points $z_i-mh_0$ and $-z_i-s_j$ lie on $\tfrac1{400}\mathbb Z$, hence none is in an open cell. This also lets the branch on each cell extend smoothly to both endpoints for interpolation. The quadratic has Bernstein controls $f_L,\ 2f_M-(f_L+f_R)/2,\ f_R$, with nonnegative weights summing to one and integrating to $h/3$ each. For any measurable law at any cell point the expected quadratic is bounded above by the same weighted sum of the three **separate full-atom maxima** of the controls. Each control is an odd cubic $(3b-a)X-4bX^3$ with its own coefficients; the endpoints give $|a+b|$, and when $0\le (3b-a)/(12b)\le1$ and $b\ne0$ there is also the critical-point value $8|b|[(3b-a)/(12b)]^{3/2}$. If the ball for $b$ cannot be separated from zero the bound $|a|+|b|$ suffices. This argument does not sample or interpolate the competitor law.

A uniform bound on $|\partial_t^3 f|$ on open cells is $L_3e^{-t/2}$. A first cut contributes $\sigma|1/2+ix|^3/D_Y$ to $L_3$ with $D_Y=C_t$ or $C$. On the negative kernel branch the third derivative of the weighted kernels vanishes; on the positive branch, after taking out $e^{-t/2}$, it is $(2-y)e^{-y/2}$ for $J$ and $(-3+3y-y^2/2)e^{-y/2}$ for $G$. These have absolute bounds $3,8$ since $ye^{-y/2}\le2/e<1$ and $(y^2/2)e^{-y/2}\le8/e^2<2$. A second cut therefore contributes

\[
\frac{2\sigma}{C}\|b^*\|_1\big(3\|q\|_1+8\|\lambda\|_1\big).
\]

Here $|X|,|T(X)|\le1$; the reference is not differentiated. The absolute quadratic interpolation remainder on a cell $[l,r]$ is bounded by $\sup|\partial_t^3 f|\,|(t-l)(t-(l+r)/2)(t-r)|/6$. Integrate the absolute cubic factor including $1/6$ to get $h^4/192$. The supremum of $e^{-t/2}$ on a cell is no more than $e^{h/2}$ times its value at any point of that cell. Summing the integrated remainders thus costs at most

\[
E_- = \frac{h^3}{192} L_3 e^{h/2}\int_{-144/25}^0 e^{-t/2}dt .
\]

The reference correction $\int(aA_*+bB_*)dt$ is evaluated by left-minus-right differences of the price primitives on **the reference's own slabs**. No chord is taken across a reference jump, including at $0$. The Bernstein control sum, this signed reference correction, and $E_-$ bound $G_-$ on the whole interval, not only for cellwise constant laws.

## Reproduction and sign

From the repository root, with assertions enabled, run:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-measurable-negative-deletion-33.py
```

The checker runs its focused signed-kernel and cubic tests first (`--self-test` runs only these tests). The earlier accepted-tail replay at $1/2400$ budgets about $3.3692\cdot10^{-7}$ after charging the reference surplus, slack and tail upper price with the signs above. Before evaluating the negative cells the checker requires $E_-<10^{-8}$, well below the gap suggested by the non-certified constant-cell lead. It then checks the sign using the actual ball-enclosed upper prices, with no dependence on that lead. The accepted tail still includes both the chord remainder and the bound beyond $48$; no negative-slab price printed by the shared code enters the new bound. The comparison only needs the reference as a tangent center and does not recheck its feasibility.

The separate `--self-test` invocation passed in 2.29 s. The final full invocation passed in 86.78 s with peak RSS 1,140,924 KiB. Its 128-bit Sage ball output includes:

```text
Negative nominal gain upper  [2.95474001767226954124516e-7 +/- 5.41e-31]
Negative allowance           [1.202945765065813969640455977840661e-10 +/- 1.95e-44]
Negative total gain upper    [2.95594296343733535521480e-7 +/- 5.87e-31]
Tail grid                    [1.8379308447418522030237069476e-7 +/- 2.03e-36]
Tail interpolation           [5.926648782021443558489955898231590e-9 +/- 7.40e-43]
Tail beyond 48               [1.332406212991770305948162686144488e-10 +/- 4.67e-44]
Available negative budget    [3.3692040384790379856488997e-7 +/- 8.57e-33]
Surplus upper price          [-4.1326107504170263043410e-8 +/- 6.18e-31]
```

In particular the upper end of the negative price is strictly below the lower end of the available budget. The last ball encloses the computed **upper price**, not the true optimal surplus.

**Next test.** If also releasing the pre-tail, a feasible nonnegative-surplus profile must contribute more than $4.13\cdot10^{-8}$ there to the integral in (1). That is a score requirement on the whole pre-tail; the proof of the earlier necessary early-band score assumes fixed negative slabs and does not transfer. Before adding more tangents to a pre-tail refit, evaluate the original quadratic second inequality, whose nonnegative difference-field term this certificate discards.
