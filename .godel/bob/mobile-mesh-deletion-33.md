# Full refits on moving delete-33 seed slabs

At depth $39/20$, let **each of the 426 seed knots** $z_i$ move to a real $t_i\in[z_i-1/200,z_i+1/200]$. On each resulting slab $[t_i,t_{i+1})$ choose an independent, arbitrary probability law on $0\le u\le1$. Use $t_{427}=+\infty$, and keep the exterior law $X=0$ to the left of $t_1$. If both normalized unfolded first caps are at most one and the three second replies at $3t$ vanish simultaneously, then $M-8/9<-4\cdot10^{-7}$. This is a sufficient radius, not an optimum. Adjacent windows have disjoint interiors; if their endpoints touch and two knots coincide, the intermediate slab contributes zero and its two jumps combine. In particular the result applies over strictly ordered moves. The zero knot is not pinned.

This extends the [426-slab fixed-grid rejection](mesh-deletion-33.md) without inserting any knots. Unlike the [previous mobile families](mobile-deletion-33.md), it allows complete replacement also on every negative slab, and uses larger windows than the partial-replacement result ($1/1000$). It does not cover the earlier family's much wider fixed-law motion ($1/5$), its independent mixtures of jump positions, or nonconstant laws inside the moved slabs. The proof reuses the accepted mesh dual unchanged; it does not transfer the price of the earlier mobile dual.

## The off-grid dual inequality

Use $X(u)=2u^2-1$, $T(u)=4X(u)^3-3X(u)$, and let $U_i,A_i,B_i$ be the corresponding mean of $u,X,T$ on slab $i$. Set $A_0=B_0=0$, $C=\cosh(39/20)/3$, and $C_t=C/(2\cos(\pi/12))$. With $w=1/2+ix$, $d\mu=dx/(2\pi|w|^2)$, $E_t(x)=e^{-\bar w t}/w$, the normalized first fields are

$$V_A=\sum_i \frac{\Delta A_i}{C_t} E_{t_i}, \qquad V_B=\sum_i \frac{\Delta B_i}{C} E_{t_i}.$$

Write $V_B=\sum_i b_i e^{ixt_i}/w$, with $b_i=e^{-t_i/2}\Delta B_i/C$. Let $s=(-112,96,304)/400$, $h=208/400$, $H(x)=\sum_j \lambda_j e^{is_j x}$, $\lambda=(.73,.98,1)$, and $p(hx)=\sum_{j=-192}^{192} c_{|j|}e^{ijhx}$ be the checked majorant of $|H|$ from the fixed-mesh certificate. Define

$$Q(V)=\int \bigl[p(hx)|V|^2+\Re(HV^2)\bigr]d\mu,\qquad R=\int p(hx)d\mu.$$

The disk $|n-V_B^2|\le1-|V_B|^2$ and the three zero replies yield $Q(V_B)\le R$ under the first cap. Also $Q\ge0$ as a real quadratic form on any finite sums of these fields, independent of the first cap. The matrix of $Q(\sum b_i e^{ixt_i}/w)$ on real coefficients is given by the real, symmetric kernel

$$K(t,y)=\sum_{j=-192}^{192}c_{|j|} (2+|t-y+jh|)e^{-|t-y+jh|/2}+\sum_j\lambda_j(1+v_++v_+^2/2)e^{-|v|/2},\qquad v=t+y+s_j$$

by the [difference and sum transforms](unfolded-deletion-33.md#exact-three-site-completion). For the rational probe $q$ in [the serialized dual](deletion-laws/delete-33-mesh.dual), use its **original** sites $y=k/400$ and denote by $K_{t,y}$ the cross matrix, and by $K_{y,y}$ the probe-only matrix. Positivity on the **union** of sites yields $b^TK_{t,y}q\ge-\sqrt{R q^TK_{y,y}q}$, even when the two site sets overlap or a moved knot coincides with another. No interpolation of the quadratic form or restriction of the probe to the moved mesh is required.

For each `F` row $(j,k,a,b)$ in the same dual take $x=k/10^9$, $d=(a-ib)/10^{13}$, and use $\Re(d V_j(x))\ge-|d|$ by the first cap. Define the primitives $P_A(t)=\sum_{j=A}\Re(dE_t(x))/C_t$ and $P_B(t)=\sum_{j=B}\Re(dE_t(x))/C+e^{-t/2}\sum_y K(t,y)q_y/C$. Define $W(t)=(1+t_+)e^{-t_+}$ and

$$S(t,u)=W(t)u+P_A(t)X(u)+P_B(t)T(u),\qquad S(+\infty,u)=0.$$

For every admissible law and path, summing the lower bounds on the dual fields gives the **upper** price

$$ M-8/9 \le \sum_{\mathrm{F\ rows}}|d|+\sqrt{R q^TK_{y,y}q}-8/9+\sum_{i=1}^{426}\mathbb E_i[ S(t_i,u)-S(t_{i+1},u)]. \tag{1} $$

Indeed $M$ is exactly $\sum_i[W(t_i)-W(t_{i+1})]U_i$ since the failure weight is zero left of the first knot (always negative). The linear jump sums telescope into the same differences of primitives: the first boundary terms involving $A_0,B_0$ vanish; the right boundary terms are $W(t_{426})U_{426}+P_A(t_{426})A_{426}+P_B(t_{426})B_{426}$. The formula for $W$ handles both sides of a moved zero knot, without assigning its slab a fixed sign. The convention at a single endpoint does not change the mean; jumps at a coincident endpoint sum with no contribution from a zero-width slab.

## Continuous-path bridge

Put $N+1$ equally spaced nodes in each closed window, spacing $\delta=2r/N$ for radius $r$. Fix the slab laws when comparing a real path to these grid paths. Round each $t_i$ to its bracketing nodes with the chord weights of that coordinate. Use **the same rounded node for both edges adjacent to a knot**. Independent rounding of different coordinates gives an average of consistent grid-path totals for the expectation in (1). Every combination is ordered because the windows only touch at worst. The last endpoint stays at infinity. Thus once we pay for the chord error, the average is bounded by the maximum over grid paths, even though the slab laws are not subsequently kept fixed when pricing those paths.

For the chord error, regroup (1)'s expectation by the moved coordinates. At a knot the multipliers for $W,P_A,P_B$ are the differences of the corresponding slab means, bounded in modulus by $1,2,2$ respectively; the same bounds cover the first knot with the zero baseline. A uniform bound $D_i$ on the second derivative in coordinate $t_i$ therefore gives excess over the chord of at most $D_i\delta^2/8$. A bound on the Lipschitz constant of the first derivative suffices when the second derivative has a jump. The checker adds this error **once per knot**, not independently per edge.

Here are the bounds over actual windows. For each probe translate let its breakpoint be $a$ and put $v=t-a$. Multiplying the difference/sum transforms by $e^{-t/2}$ gives $e^{-a/2}$ times $e^{-v}(2+v)$ and $e^{-v}(1+v+v^2/2)$ on $v\ge0$, and $2-v$ and $1$ on $v<0$, respectively. Their values and first two derivatives match at zero. The third derivatives on $v>0$, relative to $e^{-t/2}$, have magnitudes $e^{-v/2}|1-v|\le2$ and $e^{-v/2}|-1+2v-v^2/2|\le4$; on $v<0$ they vanish. The latter bound follows by maximizing each monomial times $e^{-v/2}$ separately, giving $1+4/e+8/e^2<4$. Gather equal breakpoints before summing absolute weights. Add the first-cut bounds $|d||w|^2 e^{-t/2}/C_j$ to the corresponding probe bound. If the resulting constants are $L_A,L_B$, then

$$\sup_{t\in[z_i-r,z_i+r]} |P_Y''(t)| \le |P_Y''(z_i)|+r L_Y e^{(r-z_i)/2}.$$

This uses piecewise integration through every breakpoint, not a smoothness assumption on an open cell straddling a join. For $W''$ use zero on wholly nonpositive windows, one on windows crossing or touching zero from the right ($W'$ is continuous there), and $|W''(z_i)|+3r$ otherwise since $|W'''|\le3$ on the positive ray. These estimates give $D_i$ by the coefficients $1,2,2$ above.

## Validated maximum and replay

The probe implementation first groups all translated kernels by breakpoint (exact integer multiples of $1/400$). For arbitrary rational $t$, exact classification by $\lfloor 400t\rfloor$ lets prefix sums evaluate the pieces $e^{-t}$ times quadratics and suffix sums evaluate the affine pieces, including their first two derivatives. It recomputes the probe price at the original sites. The checker smoke-tests both primitives and the price against the independent original lattice convolutions at the first, zero and last knots, and checks the original 426-slab upper bound, including its terminal edge.

An edge of the layered graph is priced by the maximum of $S(s,u)-S(t,u)$ over **all** $u\in[0,1]$, since maximizing over probability laws is equivalent to maximizing over atoms. For an edge into the terminal node use zero for the right primitive. The degree-six Bernstein control hull and dyadic de Casteljau subdivision certify each required upper bound. The path recurrence starts with score zero for every first-window node and keeps an outward upper endpoint at each destination. For faster evaluation, if the control hull of a subdivision lies below an already certified upper bound for an earlier incoming edge plus its predecessor score, that subdivision cannot increase the destination bound. The non-pruned pieces use a slack of $10^{-13}$ relative to a subdivision-point lower endpoint. All coordinates are rational, all primitive, price and maximization bounds use outward 128-bit real/complex balls, and the final strict sign includes the sum of the uniform chord errors.

From the repository root with SageMath 10.9 and assertions enabled:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-mobile-mesh-deletion-33.py --radius 1/200 --cells 40 --threshold=-1/2500000
```

The replay passed with grid upper price $-1.1651253406626828\ldots\cdot10^{-6}$, chord correction $6.4989343260272954\ldots\cdot10^{-7}$, and upper price including the correction $-5.1523190805995329\ldots\cdot10^{-7}$. The checker compares the outward enclosure directly with $-1/2500000$.

The inputs are the retained seed and serialized dual at campaign base `cea364506db26dfbb74b852ac0c3bb4286b31d34`; no dual refit, optimizer, or scratch output is needed for the replay. A preliminary 16-cell screen at radius $49/10000$ gave a negative grid upper price but a positive bound after adding the chord error. That was a failure of the coarse enclosure to certify the sign, not evidence for an adverse path or a feasible witness.

This excludes witness laws only under the stated unfolded constraints and motion/replacement class. It does not settle the all-real delete-33 comparison, the effect of introducing new knots, or arithmetic realizability.
