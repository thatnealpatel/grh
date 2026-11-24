# A joint split-tail price for delete-33 at depth 39/20

**Result.** The positive tail cannot pay the deficit of the 1,257-slab near miss in the families below, even after joint changes of the first and third harmonics. This is an upper bound on the failure mean of **all laws in each stated family** satisfying the unfolded first caps and the three simultaneous second replies. It is not an infeasibility result for all prime profiles at this depth.

Use the [1,257-slab reference](deletion-laws/delete-33-tail-baseline.txt), not the 426-slab [unfolded seed](unfolded-deletion-33.md). Its first knot is $-144/25=-5.76$, and the last is $z_*=29/5=5.8$; the last slab is infinite. Keep $X=0$ before the first knot and keep **all 1,257 knots fixed**. The columns marked by $\eta$ allow $(1-\eta)\mathcal P_I+\eta\mathcal Q_I$ on each original slab $I$ in that region, independently, with $\mathcal P_I$ its reference law and $\mathcal Q_I$ an arbitrary probability law on $0\le u\le1$. This includes all smaller replacement fractions. All added tail slabs have independently arbitrary laws on that same atom interval. The ten extra knot centers, in units of $1/400$, are

```
2340 2360 2400 2480 2560 2720 2880 3200 4000 4800
```

| Tail $[z_*,\infty)$ | $\eta$ left of $0$ | $\eta$ on $[0,z_*)$ | Certified upper bound on $M-8/9$ |
|---|---:|---:|---:|
| Ten extra knots fixed; arbitrary measurable laws beyond $40$ | $1$ | $1$ | $<-2.82\cdot10^{-8}$ |
| Extra knots within $1/6400$ of their centers; arbitrary measurable laws beyond $48$ | $1$ | $1$ | $<-1.15\cdot10^{-8}$ |
| Extra knots within $1/800$ of their centers; arbitrary measurable laws beyond $40$ | $1$ | $1/4$ | $<-3.56\cdot10^{-8}$ |
| Arbitrary measurable law throughout the tail, no slab structure required | $1/4$ | $0$ | $<-1.63\cdot10^{-8}$ |
| Arbitrary measurable law throughout the tail | $1$ | $0$ | $<-2.0215\cdot10^{-7}$ |
| Arbitrary measurable law throughout the tail | $1$ | $2/3$ | $<-1.529\cdot10^{-8}$ |

In the first three rows the final tail law is constant from the last extra knot up to the stated remote cutoff. At and beyond the cutoff the laws need only be measurable. The moving windows are disjoint and preserve knot order. The moving-knot claim is for real knot locations, not just the grid used to check it. No row requires $A$ or $B$ to remain fixed in the regions marked $\eta>0$ or on the tail.

After Work, the [fixed-field price and one-slab witness](tail-fiber-deletion-33.md) show that the necessary early score below is attainable with neither first field changed. A change on one further slab gives a positive surplus at $1.9500036$, not at $39/20$.

## Reference admissibility and the comparison

Normalize the integer weights on each line of the table, with knot and atom units $1/400$ and $10^{-9}$. Write $X(u)=2u^2-1$, $T(X)=4X^3-3X$, $(A,B,U)=\mathbb E(X,T(X),u)$, and $M=\int_0^\infty ze^{-z}U(z)\,dz$. The tail mass at $z_*$ is $(1+z_*)e^{-z_*}=0.02058737226855554028\ldots$, and the reference tail mean of $u$ is exactly $8961144381869405791031/10^{22}$. The reference has

\[
M_*-8/9=-6.6078916263462872\ldots\cdot10^{-7}.
\]

Thus the tail is not small on the scale of the deficit; a mass-only bound is not a discriminator. We price the changes after both normalized first fields and the three-site constraint are charged. The full replay independently checks reference first caps $\|V_A\|_\infty<0.9999998$ and $\|V_B\|_\infty<0.999975$, including the two outer frequency rays. For the reference it also constructs the exact weighted Gram correction by the method in the [unfolded proof](unfolded-deletion-33.md#exact-three-site-completion): use transform size 2048, degree 256, and inputs $(113.71074849,153.65856922,156.52872908)$. The correction has $\ell^1$ norm about $2.83461870818\cdot10^{-6}$; after the exact three-by-three solve the slack in $1-\|g\|_\infty$ is greater than $1.4\cdot10^{-6}$, checked with 65,536 nodes and a chord remainder. A small residual alone is not used as a completion. The reference meets the cap and moment constraints but has the wrong sign of surplus.

## Joint price

Put $c=39/20$, $C=\cosh(c)/3$, $C_t=C/(2\cos(\pi/12))$, $w=1/2+ix$, and $d\mu=dx/(2\pi|w|^2)$. For any profile $Y=A,B$, with normalization $D=C_t,C$ respectively, use

\[
V_Y(x)=\frac{\bar w}{D w}\int e^{(-1/2+ix)z}Y(z)\,dz.
\]

On steps this is $\sum_l b_l e^{ixz_l}/w$ with $b_l=e^{-z_l/2}\Delta Y_l/D$. The phase $\bar w/w$ is important for the second constraint. Feasibility entails $|V_A|,|V_B|\le1$ and a second field $n$ with $|n-V_B^2|\le1-|V_B|^2$ and $\Re\int e^{is_jx}n\,d\mu=0$, $s_j=(6+13j)/25$, $j=-1,0,1$. The actual first field at $3t$ is $-V_B$, with the same square. We impose the two unfolded caps used in the [delete-33 construction](unfolded-deletion-33.md); the disk condition is necessary for simultaneous second replies at $3t$. The bounds here do not exclude shallow constructions outside those imposed caps, e.g. a different realization at $t$ that relaxes its pointwise cap.

Each first cut is $\Re(\bar\gamma V_Y(x))\le1$, $|\gamma|=1$. For a second cut use real $\lambda_j$, $h_0=13/25$, $H=\sum_j\lambda_j e^{is_jx}=e^{is_0 x}L(h_0x)$, and an even real Laurent majorant $q\ge |L|$. The disk inequality gives

\[
Q(V_B):=\int [q(h_0x)|V_B|^2+\Re(HV_B^2)]\,d\mu\le d:=\int q(h_0x)\,d\mu.
\]

Indeed $\Re\int HV_B^2\,d\mu\le\int |H|(1-|V_B|^2)\,d\mu$. Also $Q(Z)\ge0$ for **any** complex field $Z$ in $L^2(\mu)$, not just for admissible fields, because $q\ge|H|$. Thus, writing $V_*$ for the reference $B$ field, the tangent $2\mathcal B(V_*,V_B-V_*)\le d-Q(V_*)$ is necessary, where $\mathcal B$ is the real polarization of $Q$. Each cut has a nonnegative multiplier $\sigma$.

Here is the slab primitive for those linear functionals, including $\sigma$. For a first cut it is

\[
\frac{\sigma}{D}\Re\frac{\bar\gamma e^{(-1/2+ix)t}}{w}.
\]

For a second cut let $b_i^*=e^{-z_i/2}\Delta B_i^*/C$ be the reference jumps. Write $q(\theta)=\sum_k q_k e^{ik\theta}$ with real $q_{-k}=q_k$, and put

\[
\begin{split}
\mathcal D(y)&=(2+|y|)e^{-|y|/2},\\
\mathcal K(y)&=(1+y_++y_+^2/2)e^{-|y|/2},\\
v(t)&=\sum_i b_i^*\left[\sum_k q_k\mathcal D(t-z_i+kh_0)+\sum_j\lambda_j\mathcal K(t+z_i+s_j)\right].
\end{split}
\]

Then the primitive is $2\sigma e^{-t/2}v(t)/C$, and $Q(V_*)=\sum_i b_i^*v(z_i)$. These are the real sum and difference kernel integrals with denominators $w^3\bar w$ and $|w|^4$. For example Laplace representations of $w^{-3}$ and $\bar w^{-1}$ give $\mathcal K(y)=\int_{\max(0,y)}^\infty (r^2/2)e^{-r+y/2}dr$ in the displayed Fourier sign convention. The price at $\infty$ is zero in all primitives. A left-minus-right difference of the primitives prices one slab.

Let $a(t),b(t)$ be the **densities** for all the cuts on $A$ and $B$, i.e. minus the derivatives of the summed primitives. Let $W_0(t)=(1+t_+)e^{-t_+}$, with $-W_0'(t)=t_+e^{-t_+}$. If $S$ is the sum of the reference slacks, including multipliers, every feasible law satisfies

\[
M-8/9\le M_*-8/9+S+\int [t_+e^{-t_+}(U-U_*)-a(t)(A-A_*)-b(t)(B-B_*)]\,dt. \tag{1}
\]

For first cuts the slack is $\sigma(1-\Re(\bar\gamma V_{Y,*}(x)))$; for second cuts it is $\sigma(d-Q(V_*))$. The inequality follows by adding the upper bounds on the changes of the cut functionals. The primitive formula holds first for steps, using their jumps and summation by parts. On real measurable profiles with $|A|,|B|\le1$ and zero to the left of $-5.76$, approximate in $L^1(e^{-t/2}dt)$ by finite steps on the same half-line. The normalized field map is continuous into $L^\infty(dx)$, with norm at most $1/D$, hence also into $L^2(\mu)$. The price densities are bounded by constants times $e^{-t/2}$, as below. This extends the identity for the linear functionals to all the stated profiles. No jump or variation assumption on measurable tail laws is used.

For a fixed slab, integrate $t_+e^{-t_+},a,b$ to get $(m,a_I,b_I)$. Its contribution to (1) is bounded by

\[
\eta_I\left[\max_{0\le u\le1}\{m u-a_I X(u)-b_I T(X(u))\}-(m U_I^*-a_I A_I^*-b_I B_I^*)\right]. \tag{2}
\]

This maxima-over-atoms formula prices the **coupled** change of $U,A,B$; it does not maximize their changes independently. The degree-six polynomial is enclosed on the full interval by Bernstein subdivision. The bound over a free law follows by integrating the atom inequality against its probability distribution. A cutoff past the last tail knot can be ignored for (2), temporarily continuing its last constant law to infinity; the uniform correction for replacing it beyond the cutoff is given below. This continuation is only an auxiliary calculation of the right side of (1). It need not satisfy any cap.

## Remote and continuous prices

For a fixed atom, the tail integrand in (1) equals

\[
g(t,u)=te^{-t}(u-U_*^{\rm tail})-a(t)(X(u)-A_*^{\rm tail})-b(t)(T(X(u))-B_*^{\rm tail}).
\]

The same density applies to differences of two laws by linearity. Differences of $U$ are at most one, and differences of $A,B$ at most two. The first density has complex exponential coefficient $\sigma\bar\gamma\bar w/(Dw)$; its size, first derivative and second derivative are bounded by $\sigma e^{-t/2}/D$ times $1,|w|,|w|^2$. For a second density replace the kernels $\mathcal D,\mathcal K$ in the primitive by $J=(1+y_+)e^{-|y|/2}$ and $G=y_+^2 e^{-|y|/2}/2$, since these are $(1/2-\partial_y)\mathcal D,(1/2-\partial_y)\mathcal K$. They are $C^1$. Bounds for $J$ and $G$, in order, for the operators $1,\partial_y-1/2,(\partial_y-1/2)^2$ are $(2,2),(1,2),(1,4)$. In detail, for $y<0$ the last two operators vanish on each; for $y>0$ the first derivatives in this convention are $-y e^{-y/2}$ and $(y-y^2/2)e^{-y/2}$, and the second are $(y-1)e^{-y/2}$ and $(1-2y+y^2/2)e^{-y/2}$. The bounds follow by maximizing the exponential times a monomial (for the last bound it suffices to use the triangle inequality). The derivatives used for interpolation are bounded almost everywhere, and the first derivatives are Lipschitz on compact intervals.

Consequently, for any two fixed tail laws the absolute difference of their price densities has a size bound $te^{-t}+L_0e^{-t/2}$ and a first-derivative bound $te^{-t}+L_1e^{-t/2}$ on $t\ge z_*$, and the corresponding second-derivative bound is $te^{-t}+L_2e^{-t/2}$. For each first cut the contributions to $(L_0,L_1,L_2)$ are $(2\sigma/D)(1,|w|,|w|^2)$. Each second cut contributes

\[
\frac{4\sigma\|b^*\|_1}{C}\big(2(\|q\|_1+\|\lambda\|_1),\ \|q\|_1+2\|\lambda\|_1,\ \|q\|_1+4\|\lambda\|_1\big).
\]

These bounds are uniform in all the independently chosen laws, including joint refits. For measurable laws the size bound is pointwise, so the exact infinite remainder costs at most $W_0(R)+2 L_0 e^{-R/2}$ beyond $R$. The derivative bounds are used only with both laws fixed while interpolating.

For moving knots, first continue the final slab law indefinitely. With all laws fixed, the derivative of the tail price in each boundary coordinate is the difference of the adjacent densities. Its next derivative is thus bounded by $te^{-t}+L_1e^{-t/2}$, with the other coordinates fixed. For grid cell width $d$ the one-coordinate chord error is at most $d^2/8$ times the supremum of that bound; applying this coordinate by coordinate adds the errors. Use the left edge of each band for the supremum, since both terms decrease on the bands. For every grid path the sum of the interval prices (2) bounds the price of **any** fixed choice of laws. The largest such sum is bounded by a dynamic program: at each node maximize the predecessor bound plus the price of the slab between the two nodes. Induction gives an upper bound at the final node $\infty$ without enumerating all paths. The coordinate interpolation now covers real boundary positions before adding the remote remainder. This avoids charging a different independently chosen displacement at the two sides of each boundary.

For the measurable tail use the pointwise maximum of $g(t,u)$, checked at nodes of spacing $d=1/800$ on $[z_*,48]$. For each fixed $u$ its value is below its endpoint chord plus the error $d^2\sup |\partial_t^2 g|/8$. Maximizing over $u$ is bounded by the chord of the endpoint maxima plus the same error. Integrating gives the trapezoid sum and a remainder bounded by

\[
\frac{d^2}{8}\left[e^d\int_{z_*}^{48} te^{-t}\,dt + e^{d/2} L_2 \int_{z_*}^{48} e^{-t/2}\,dt\right].
\]

Indeed in a cell the supremum of each positive envelope is at most $e^d$ or $e^{d/2}$ times its value anywhere in that cell. For $t\ge48$ use the remote bound with the reference tail as the comparison law.

## Replay and evidence

For the first four rows the external numerical inputs are the [reference law](deletion-laws/delete-33-tail-baseline.txt) and two [split-knot](deletion-laws/delete-33-tail-dual.json) and [measurable-tail](deletion-laws/delete-33-continuous-tail-dual.json) lists of cuts. A row is $[j,x,\Re\gamma,\Im\gamma,\sigma]$, $j=0$ for $A$, $1$ for $B$, or $[1,[\lambda_{-1},\lambda_0,\lambda_1],\sigma]$. The checker reads decimals exactly, normalizes the first-cut direction, and checks the sign of each scale. It uses 128-bit Sage balls for transcendental computations. For a second row, the even degree-192 nomination $p$ comes from a 1024-node transform of $|L|$. The checker proves $|L|>.1$ by splitting at $|\cos\theta|=.9$ and shows $p(0)>0$ in angle coordinates and $e=\|p^2-|L|^2\|_{\mathrm{coeff},1}<10^{-8}$. Thus $p$ stays positive and $q=p+10e$ is a true majorant everywhere. Neither a frequency sample nor a truncation of an infinite series is being assumed to certify the majorant. The lattice convolutions in the checker evaluate the finite Laurent and reference-jump sums, not cutoffs of the weighted integrals over $x$.

Run from the repository root, with assertions enabled:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-tail-deletion-33.py
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-tail-deletion-33.py --skip-baseline-check --movable
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-tail-deletion-33.py --skip-baseline-check --continuous
```

All three invocations passed in the assigned workspace, with these final Sage enclosures of the computed upper prices:

```text
Fixed                           [-2.8208319799708915317152e-8 +/- 3.31e-31]
Moving 1/6400, full pre-tail    [-1.1542184622869815727074e-8 +/- 3.31e-31]
Moving 1/800, quarter pre-tail  [-3.5693469442412254182372e-8 +/- 2.44e-31]
Measurable                      [-1.63769705772566334856127e-8 +/- 6.45e-32]
```

Price components and final upper ends, rounded here in units of $10^{-8}$ (the reference surplus is $-66.07891626346$ in the same units):

| Tail | Cut slack | Negative gain | Pre-tail gain | Tail price through grid/finite slabs | Interpolation | Remote | Surplus upper value |
|---|---:|---:|---:|---:|---:|---:|---:|
| Fixed | 7.182184 | 28.964321 | 26.163286 | 0.220711 | 0 | 0.727582 | $-2.820832$ |
| Move $1/6400$ | 7.182184 | 28.964321 | 26.163286 | 2.432810 | 0.168771 | 0.013326 | $-1.154218$ |
| Move $1/800$ | 7.182184 | 28.964321 | 6.540822 | 18.419169 | 0.675492 | 0.727582 | $-3.569347$ |
| Measurable | 5.027852 | 19.770566 | 0 | 34.295390 | 5.334087 | 0.013324 | $-1.637697$ |

For the fixed and moving cases the finite-slab price continues the last law to infinity before charging the remote correction; it is not literally truncated at the remote cutoff. In the measurable row the same terms give the tradeoff

\[
M-8/9 < 10^{-8}\big(-21.4082+79.0823\,\eta_{\rm neg}+130.2915\,\eta_{\rm pre}\big),\qquad 0\le \eta_{\rm neg},\eta_{\rm pre}\le1,
\]

with conservative rounding. In particular, if both original regions are unchanged the surplus upper value drops below $-2.14\cdot10^{-7}$. In contrast, using the same measurable-tail cuts with full negative freedom and unchanged pre-tail laws gives a **positive** upper bound (about $5.77\cdot10^{-7}$). It is an unpaid allowance, not a witness. With the wider moving knots, replacing the quarter pre-tail allowance by the full one also loses the sign. These are reasons not to infer an unrestricted refit result from the table.

The cut lists were nominated by joint slab-weight LP exchanges, with the same $u$ weights controlling all three observables, an exact-depth normalization, and both first fields and linearized second tests in the exchange. The fixed/variable-knot list uses a fixed tangent center; the measurable list is repriced with all tangents centered on the tabulated reference, **not** copied as an LP optimal value. In a finer exploratory tail run (spacing $1/40$ through $12$, then $1/10$ through $24$), the last observed point still had surplus about $-6.04\cdot10^{-7}$ and both numerically estimated caps violated. No positive exact-Gram nominee emerged. This last search observation is not used in any certificate and does not exclude that finer family.

**Decision.** Do not repeat unrestricted atom-site refits on the fixed mesh with these ten new knots at $39/20$. The bound already includes every real atom site and full refits to its left cutoff. For an independently refittable measurable tail and full negative freedom, the old measurable cuts lose the sign. The joint repricing below pays that allowance. If the intent is to release the left cutoff instead, first price continuous first-cap tests, such as the [positive-side Hankel tests](fixed-third-price-deletion-33.md#a-continuous-test-that-never-sees-the-added-left-slabs) at both heights. Finite first-frequency cuts alone cannot handle arbitrarily far left correction even in the fixed-$B$ subfamily. Neither these certificates nor the nearby witness at $1.95001720$ decide the target all-real obstruction at exactly $39/20$, let alone the unrestricted three-versus-four minimum or the signed arithmetic lower bound.

For the separate 426-knot seed, see the [post-Work motion and swept-band results](swept-bands-decision.md). They do not settle full negative replacement with a measurable tail on this 1,257-knot reference.

## Full negative replacement with a measurable tail

At $c=39/20$, keep $X=0$ before $-144/25$, allow an independent arbitrary law on each of the 494 fixed negative reference slabs, keep the laws on $[0,29/5)$ unchanged, and allow arbitrary measurable laws from $29/5$ to infinity. Under the same two unfolded first caps and simultaneous second replies, the joint price gives **$M-8/9<-2.0215\cdot10^{-7}$**. This closes the fixed-slab full-negative experiment. It neither requires nor permits treating the old positive upper price as a realizable surplus.

The [measurable-negative extension](measurable-negative-deletion-33.md) uses the same cut list and allows independently measurable laws throughout $[-144/25,0)$, with no reference-slab restriction there. With the pre-tail unchanged and the same measurable tail, the certified bound is **$M-8/9<-4.13\cdot10^{-8}$**. The pre-tail replacement fractions below still refer to the fixed negative slabs.

The [new cut list](deletion-laws/delete-33-full-negative-dual.json) has 120 first cuts on $A$, 71 on $B$, and one second cut with $\lambda=(.7264553101249,.9816283566088,1)$. The nomination allowed pre-tail refits as well: It added first cuts at peaks of the fields of trial laws, varied the first-cut phases at active frequencies, and combined directions at a common frequency by vector addition within each field. The search used sampled atoms and a finite tail. Neither its objective nor its feasibility tolerances enter the proof.

For the serialized list, apply (1) and (2) with $\eta_I=1$ on **every** negative slab. Integrate the pointwise tail price as above, now with $d=1/2400$. In units of $10^{-8}$ the upper-price components are as follows (displayed values rounded):

| Reference surplus | Cut slack | Negative gain | Tail trapezoid | Chord error | Beyond 48 | Total |
|---:|---:|---:|---:|---:|---:|---:|
| $-66.078916$ | $13.401578$ | $13.476826$ | $18.379308$ | $0.592665$ | $0.013324$ | $-20.215214$ |

The tail bound maximizes over the real atom interval, not merely the reference support. It does not constrain the variation of the competitor's laws. The independent full replacement price for $[0,29/5)$ on this list is $2.8029019183\cdot10^{-7}$ (rounded). By linearity in the slab replacement fractions in (2), the same proof gives $M-8/9<-1.529\cdot10^{-8}$ even when up to two-thirds of **each** pre-tail slab law is replaced independently. With unrestricted replacement on all those slabs the same price becomes positive, $+7.81381\cdot10^{-8}$ (rounded). This is again an unpaid allowance, not a witness.

The missing gain cannot all be charged to late pre-tail slabs. In units of $10^{-8}$ the full gain on $[1,29/5)$ is below $18.21372$, leaving more than $2.00148$ to be paid on $[0,1)$ even when everything outside that early band is released on the stated mesh. Its own full gain is below $9.81531$. Thus if every early slab has replacement fraction at most $1/5$, even the priced sum with full replacement elsewhere is strictly negative. More generally a nonnegative surplus requires an actual integrated score in (1) greater than $2.00148\cdot10^{-8}$ on $[0,1)$, not merely a large change of its laws.

**Next test.** On the fixed original knots with the measurable tail, enforce this necessary early-band score when seeking a full pre-tail refit. Apply the original quadratic second inequality $Q(V_B)\le d$ to the resulting trial field before adding more tangents. The present certificate uses only its tangent and discards the nonnegative $Q(V_B-V_*)$. A fitted trial profile still needs the continuous first caps and an exact three-site completion to count as a witness. These pre-tail bounds do not release the negative knots or the left cutoff, or settle the all-real comparison.

Replay including the reference cap and Gram checks:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-tail-deletion-33.py --full-negative
```

For the refit and its full quadratic violation, see the [early-score diagnostic and necessary remote-band change](early-refit-deletion-33.md).
