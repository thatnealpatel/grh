# Delete-33: Price additional knots rather than fixing their sites

At $c=39/20$ the midpoint $1/400$ does **not** restore a nonnegative surplus. For that mesh the new bound is $M-8/9<-4.1210\cdot10^{-8}$. The old positive split price measured a limitation of its cut list. Keep the two unfolded first caps, the simultaneous three-site second constraints, $X=0$ left of $-144/25$, and arbitrary measurable laws from $29/5$ onward. On each intervening slab allow its own arbitrary law on $u\in[0,1]$, not necessarily an atom. The variables are $X=2u^2-1$, $T(X)=4X^3-3X$, $(A,B,U)=\mathbb E(X,T(X),u)$, and $M=\int_0^\infty te^{-t}U(t)\,dt$. No early-score or signed regional hypotheses are needed.

## What changed the price

Use the same reference and single tangent to the necessary $Q(V_B)\le d$ as in the [original-mesh bound](full-release-deletion-33.md). For the first rows, do not just change the phases and weights at the old frequencies. Augment the frequency set, including low frequencies, locate peaks of both first fields in a smoothed dual response, and add violated directions. Reoptimize phases and nonnegative weights and freeze the [850 retained cuts](deletion-laws/delete-33-two-knots.json). Of these, 474 are first rows on $A$, 375 are first rows on $B$, and one is the second tangent. Search and truncation need not be accurate or optimal: Normalize each first direction in the replay, construct the second majorant again, and reprice every term. The [joint-price inequality](joint-tail-deletion-33.md#joint-price) applies to the resulting exact list.

The [checker](check-two-knots-33.py) prices the 1,256 original finite slabs over the full atom interval and the measurable tail pointwise. On the tail it interpolates to $48$ at spacing $1/3600$ and adds the infinite remainder. The reference surplus plus weighted slack plus the negative and nonnegative finite-slab gains are, in units of $10^{-9}$, about $-660.7892+132.1277+128.6672+261.3612$. The tail adds $52.6230+2.6344+0.1333$ (grid, interpolation, and remote). The resulting price is $P=-83.2424639520\ldots\cdot10^{-9}$; the cutoff-$40$ allowance printed by the shared routine is not added a second time. Substituting the two half-slab atom bounds just at the requested split gives $-41.2102715121\ldots\cdot10^{-9}$. These enclosures price upper bounds, not attained surpluses.

A separate primal fit imposed the full quadratic, not just the tangent, on an inner mesh for the tail, and added first frequencies where either cap failed. Its fifth iterate, despite meeting the old three jump windows and passing $Q\le d$, had surplus about $-2.5352\cdot10^{-6}$ and $|V_A(1.2187680542591035)|>1.00000030$. This fit was not a witness, and no simultaneous second completion was inferred. The exclusion comes from the upper price, not numerical failure in the fit. Since the bound holds without regional restrictions, no use of old regional bounds is necessary.

## Uniformity in the split sites

For a finite original slab $I=[l,r)$, let $E_I$ denote the atom upper **used** on $I$ in $P$. Price a fully measurable replacement by $N_I$ using the [integrated quadratic Bernstein controls and third-derivative remainder](full-release-deletion-33.md#which-constancy-assumptions-matter). Replacing $E_I$ costs at most $D_I=\max(0,N_I-E_I)$ relative to the computed sum, leaving the signed reference correction unchanged. This is not a claim about the increase of the true optimal surplus. For a single measurable release anywhere, charge the largest upward-rounded $D_I$. Two knots in one original slab cost no more than this.

For splits in **distinct** original slabs, most $D_I$ already suffice. Where $D_I>37\cdot10^{-9}$, bound one real split $s\in[l,r]$ more tightly. Write $p(s)$ for the vector of the two signed primitives and the mass primitive $(1+s_+)e^{-s_+}$. For fixed left and right atoms $u,v$, write $L(w)=(-X(w),-T(X(w)),w)$. The two scores sum to

$$
(p(l)-p(s))\cdot L(u)+(p(s)-p(r))\cdot L(v).
$$

On each $h=1/1600$ cell interpolate $p$ at both ends and the midpoint. Its quadratic Bernstein controls are the two ends and $2p_{\rm mid}-(p_{\rm left}+p_{\rm right})/2$. For each control substitute that **one vector** for $p(s)$ on both sides and take independent degree-six atom maxima. Their sum bounds the interpolated score at the control. Nonnegative Bernstein weights then bound the interpolated sum throughout the cell by the largest such sum. This argument works first for fixed atoms and then for independently chosen laws; it does not differentiate the maximizing atoms or the laws.

The third derivative of the split score uses the **second** derivatives of the densities, paired with the *difference* of the two moment vectors. The shared `curvature` envelope $L_2 e^{-s/2}$ already allows $|\Delta A|,|\Delta B|\le2$, including when the routine returns primitive values. Add $2e^{-s/2}$ on the positive side for $|(se^{-s})^{\prime\prime}|\,|\Delta U|$, with $|\Delta U|\le1$. The branch points are on cell boundaries. Since $\max_{[0,1]}|x(x-1/2)(x-1)|=1/(12\sqrt3)$, the uniform remainder on the slab is at most

$$
(L_2+2\mathbf 1_{l\ge0})e^{-l/2}h^3/(72\sqrt3).
$$

Subtract $E_I$ after taking the maximum over cells and adding the remainder. Round the increment up, clamp below by zero, and take the smaller of this and $D_I$. Where no primitive interpolation was needed retain $D_I$. Call the results $J_I$. The worst two distinct sites cost at most the two largest $J_I$ **on distinct slabs**, regardless of their real positions. A coincident knot or one at an existing boundary needs no extra positive-length piece; the arbitrary tail needs no extra charge either.

The one-measurable-slab upper is $-26.3337843906\ldots\cdot10^{-9}$. For distinct slabs the two largest $J_I$ are at left endpoints $0$ and $-144/25$, about $42.807451$ and $38.575087$ in units of $10^{-9}$. Adding both to $P$ gives an upper of $-1.8599262676\ldots\cdot10^{-9}$. Thus at this depth **every addition of at most two real knots** to the finite mesh still gives $M-8/9<-1.8599\cdot10^{-9}$. This does not allow arbitrary measurable replacements on two slabs at once: Ten pairs are unpaid by the fully measurable prices alone.

## A three-knot test that this cut list does not settle

Split just the first three nonnegative slabs at $1/400,3/400,5/400$. Replace their three $E_I$ in $P$ by the six half-slab atom scores. Evaluating the scores at the six rational atoms in the checker already puts the recomputed upper price above $2.80\cdot10^{-8}$. This is a lower bound **on that price**, not on the surplus of any feasible profile. Selecting six favorable atoms imposes neither cap nor the simultaneous second constraints.

There is still a joint restriction on the six halves. Let $C_3=P-E_{[0,2/400)}-E_{[2/400,4/400)}-E_{[4/400,6/400)}$, and on each half $h$ let $S_h=m_h U_h-a_h A_h-b_h B_h$. For a feasible profile of nonnegative surplus on this particular mesh one needs

$$
\sigma Q(V_B-V_*)\le C_3+\sum_h S_h,
$$

by restoring the positive curvature dropped in the tangent. To isolate a single jump $\Delta Y=Y_R-Y_L$, tilt its two half scores to $S_L+kY_L$ and $S_R-kY_R$ with $k>0$. Maximize each tilted score and the four untouched ones over the atom interval, and add $C_3$, obtaining an upper $H$. Dropping curvature gives $0\le H+k\Delta Y$. This prices each difference individually on the three-knot mesh, without transplanting any windows from the one-knot mesh. The checker gives these necessary lower bounds, rounded down:

| Added knot | $\Delta A$ | $\Delta B$ | $\Delta U$ |
|---|---:|---:|---:|
| $1/400$ | $0.000508$ | $0.00455$ | $0.00457$ |
| $3/400$ | $0.000980$ | $0.00848$ | $0.00305$ |
| $5/400$ | $0.000731$ | $0.00602$ | $0.00143$ |

All three means must rise across **each** added knot. Neither the nine inequalities nor the joint score suffices for feasibility. A preliminary fixed-three-midpoint refit with three rounds of added first cuts reduced a discretized-tail search price to about $+1.19\cdot10^{-8}$; that search value has no certified sign on the measurable tail. Continue first-frequency exchange on this mesh before increasing the search to unknown knot locations. In a primal fit impose the full quadratic and exchange against both unfolded first caps. Before accepting a law, check the continuous caps and simultaneous second completion. Keep the cutoffs at both ends of the finite mesh; there is no exclusion here for unrestricted all-real profiles.

## After Work: How much movement must the three-knot fit allow?

Do not copy the one-knot pilot's half-width hulls into the three-knot fit. Keep the six half-slabs, the slab starting at $-2/400$, and the entire measurable tail unrestricted. On the other original finite slabs with left endpoint $t<-2/400$ or $t\ge6/400$, allow the refit to use, respectively, a fraction $\alpha_-$ or $\alpha_+$ of the full moment hull about the reference. A factor of one allows all laws. The factors are in $[0,1]$. A necessary condition for nonnegative surplus at $39/20$ is

$$128.5(1-\alpha_-)+259.3(1-\alpha_+)<28.01.$$

Indeed, write $K$ for the full moment hull and $v_*$ for the reference moment vector on a slab. For an integrated linear score $S$, the perturbation support on $v_*+\alpha(K-v_*)$ is $\alpha(\sup_K S-S(v_*))$. Thus multiply the **computed upper on the reference-subtracted gain** by $\alpha$, not the raw atom upper, the reference term, or the cap slack. In units of $10^{-9}$, the checker gives a free three-knot price below $28.01$. The sums of the allowances *used in that price* on the two outer groups exceed $128.5$ and $259.3$. Replacing them by their scaled values proves the inequality. It does not assume either group can attain its allowance. A smaller inner atom hull is included in the same test.

In particular, a common width must exceed $0.9277$, even with a completely free tail. Half width on both groups gives $M-8/9<-1.6589\cdot10^{-7}$. Use uncontracted moment hulls and invertible variable scaling for the next full-$Q$ fit; a width above the threshold is not sufficient. Retain the nine jump checks, first-frequency exchange, both continuous cap checks, and simultaneous second completion. [Why this changes the handoff](hull-width-decision.md).

## Replay

From the repository root with SageMath 10.9, leaving assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-two-knots-33.py
```

The [moved-center certificate](three-midpoints-deletion-33.md) now excludes the three fixed midpoints at full hull width, and prices arbitrary positions of three knots.
