# Delete-33: Move the quadratic tangent to exclude three knots

At $c=39/20$, adding the three knots $1/400,3/400,5/400$ together gives
$$M-8/9<-2.51350\cdot10^{-8}.$$
In fact, **any three additional real knots** on the finite mesh give $M-8/9<-1.46808\cdot10^{-8}$. Keep $X=0$ left of $-144/25$, independent arbitrary probability laws on the intervening slabs of the [baseline mesh](deletion-laws/delete-33-tail-baseline.txt) so refined, and arbitrary measurable laws from $29/5$ to infinity. Here $X=2u^2-1$, $T(X)=4X^3-3X$, $(A,B,U)=\mathbb E(X,T(X),u)$, $0\le u\le1$, and $M=\int_0^\infty te^{-t}U(t)\,dt$. Both unfolded first caps and the simultaneous second constraint at sites $(-7,6,19)/25$ are retained. No regional conditions are used. This does not price unrestricted all-real profiles.

## The center is not a law

Use the [joint-price fields, second majorant, and kernel primitives](joint-tail-deletion-33.md#joint-price). The old tangent was at a feasible reference $V_*$. Instead, let $Z$ be the field of a bounded step function $B_c$ on the same lattice, zero before the first knot, constant after the last. Take the reference $B$ jumps and add the 105 signed corrections in the [certificate](deletion-laws/delete-33-three-midpoints.json), **before** multiplying each jump by $e^{-z_i/2}/C$. These are corrections to jumps, not slab values. The cumulative sum defining $B_c$ may leave the moment hull. This is allowed: Its field is in $L^2(\mu)$, and the certified Laurent majorant $q\ge |H|$ gives $Q(V_B-Z)\ge0$ even when neither $Z$ nor $V_B-Z$ is admissible. For every feasible law,
$$2\mathcal B(Z,V_B)=Q(V_B)+Q(Z)-Q(V_B-Z)\le d+Q(Z).$$

Let $a,b$ be the first-cut densities with their nonnegative multipliers, with the density of $2\sigma\mathcal B(Z,V_B)$ added to $b$. The normalized first directions all have right side one. Adding the nonnegative cut slacks thus gives the **raw** upper
$$M-8/9\le K+\int_{-144/25}^\infty[t_+e^{-t_+}U-aA-bB]\,dt,\qquad K=-8/9+\sum_{\rm first}\sigma_i+\sigma(d+Q(Z)).$$
There is no subtraction of a primal reference profile and no auxiliary $A$ or $U$ center. In particular the second constant here is **not** $\sigma(d-Q(Z))$. Use $B_c$ in both the linear kernels and the quadratic constant. The kernel formulas extend to measurable competitor laws by weighted $L^1$ approximation, as in the joint-price proof; only the auxiliary center requires step jumps.

To find the certificate, vary the first directions and weights, add frequencies from both fields, and allow a center perturbation on every twelfth original knot. For replication of the search idea, if $G=LL^\top$ is the $Q$ Gram matrix of the raw jump basis and $h$ is the jump perturbation, use $y=\sigma L^\top h$. In reference-subtracted coordinates the extra term beyond the old tangent is $\|y\|^2/\sigma-2\sigma\mathcal B(Z-V_*,V_B-V_*)$. The second term is linear in $y$ for each competitor. This allows a joint convex search over the center coordinates and positive multiplier rather than alternating law fits. Neither the floating-point factorization nor the search mesh is used in verification. The retained rows are 562 first cuts on $A$, 535 on $B$, and one second cut.

## Repricing

For each finite slab integrate the primitives on that slab, then bound the degree-six score $m u-a_I X(u)-b_I T(X(u))$ by Bernstein subdivision. This optimizes over the full atom interval, hence bounds any law, without the nine necessary jump inequalities. On $[29/5,48]$ interpolate the **raw fixed-atom density** at both ends and the midpoint of each $h=1/400$ cell. All kernel branch points are on cell boundaries. Each quadratic Bernstein control is affine in $(X,T(X),u)$, so price its own degree-six atom maximum and integrate with weight $h/3$. In the [third-derivative remainder](measurable-negative-deletion-33.md#continuum-to-cell-bound) use the jump norm of $B_c$ and add $3$ to $L_3$ for the mass density, since $|(te^{-t})'''|\le 3e^{-t/2}$ here. This remainder is uniform in $u$; no tail law is differentiated. Beyond $48$ the existing $L_0e^{-t/2}$ cut envelope for differences of bounded laws also bounds the raw cut terms ($|A|,|B|\le1$, not $2$). Charge $49e^{-48}+2L_0 e^{-24}$.

On the requested mesh the constant plus finite atom bounds give $-0.0147915161618717170\ldots$. The integrated tail control bound adds $0.0147914908095615757\ldots$, the interpolation allowance adds $5.64531\ldots\cdot10^{-11}$ (rounded), and the remote allowance adds $1.60840\ldots\cdot10^{-10}$ (rounded). Their sum is below $-2.51350\cdot10^{-8}$. A separate primal search imposed the nine bounds from the [two-knot note](two-knots-deletion-33.md), full quadratic budget, and first-frequency exchange on uncontracted inner hulls. It did not produce a candidate for continuous cap verification or simultaneous second completion. Its numerical failures are not the exclusion argument.

## Three real knots, including collisions

Restore the three unsplit atom bounds in the computed price, giving $P=-136.3787151\ldots$ in units of $10^{-9}$. Use the [single-slab accounting](two-knots-deletion-33.md#uniformity-in-the-split-sites) with the new center. For each slab subtract its actual atom bound **used in $P$** from a measurable-release upper, round up, and clamp at zero to get $D_i$. This bounds the cost relative to the computed price, not the difference of two unknown optimal surpluses. If $D_i>32\cdot10^{-9}$, also interpolate the primitive vector on $1/1600$ cells, maximizing the two atom scores with a shared real split position. At a Bernstein control one uses the same primitive vector on the left and the right; interpolating separate maximizing positions would not price a shared knot. The uniform cubic remainder for the primitive uses the second density derivative envelope for **differences** of two atoms. Cap the single-knot increment by the smaller of this split bound and $D_i$; elsewhere keep $D_i$. Denote these nonnegative increments by $J_i$.

For distinct slabs the top three $J_i$ have left endpoints $0,-144/25,1/200$ and are about $42.8083,41.0988,37.7908$ in the same units. Adding all three to $P$ gives an upper below $-14.6808$. For at least two knots on one slab, release that slab entirely and charge at most one split on a different slab. The upper $P+\max_i(D_i+\max_{j\ne i}J_j)$ is below $-38.3716$. This includes three knots in the same slab, since all $J_j\ge0$. Fewer knots, repeated sites, and knots on old boundaries are also included. No union over a discrete grid of possible real positions is assumed. The [shared-knot cell lemma](../../Proofs/Lemmas/SharedKnotCell.lean) formalizes the local control argument; it does not verify the numerical envelopes or the global certificate.

## Beyond three knots: Release entire slabs

Even if two original finite slabs are made fully measurable, the surplus upper is below $-29.25\cdot10^{-9}$: The top two $D_i$ are less than $56.909$ and $50.218$ in the units above. For three fully measurable slabs, order the $D_i$ and test $P+D_i+D_j+D_k$. Only seven triples are not excluded by this sum. In units of $1/400$, **all seven include the slab starting at zero**, and the other two left endpoints are

```
(-2304,2) (-2304,4) (-216,2) (2,4) (2,6) (2,8) (4,6)
```

These indices describe the original slab *starts*, not the new knot sites. A positive sum of independent allowances is not a witness. In particular the original three fixed midpoints are excluded even though they are in the unpaid triple $(0,2,4)$.

For that triple test equal subdivisions of the three slabs while retaining all other original finite slabs. With eight pieces each, restore the discarded quadratic term to obtain the necessary row $M-8/9+\sigma Q(V_B-Z)\le F_8$, where $F_8$ replaces the three old atom bounds by twenty-four new ones. This radius is about the **moved center**, not the reference. To test the change of a moment $Y$ across the midpoint of a refined slab, let $\Delta Y$ be the mean on its right four pieces minus the mean on its left four pieces, giving each piece equal weight. Add $kY/4$ to each left score and subtract $kY/4$ from each right score. If the resulting upper sum including all other terms is $H(k)$, then any nonnegative surplus needs $\Delta Y\ge-H(k)/k$ for each $k>0$. This prices a new contrast; the nine bounds for the single-midpoint mesh do not transfer just by inclusion.

The computed $F_8<9.626\cdot10^{-9}$ gives $Q(V_B-Z)<1.369\cdot10^{-5}$ for any law with nonnegative surplus. The individual necessary lower bounds on the contrasts, rounded down, are:

| Original slab start | $\Delta A$ | $\Delta B$ | $\Delta U$ |
|---|---:|---:|---:|
| $0$ | .001447 | .012667 | .013814 |
| $1/200$ | .003794 | .033494 | .011899 |
| $1/100$ | .004997 | .040836 | .009886 |

A separate *lower* check prices the same raw linear functional on step tails. On each tail step integrate the three quadratic interpolants before taking an atom maximum. For the integral this uses the Simpson weights $(1,4,1)/6$ on each original tail cell. Subtract the uniform integrated interpolation and remote errors. For the integrated score (and the finite slabs) the shared Bernstein routine returns a sampled lower bound plus the specified tolerance, so subtract that tolerance when using it as a lower bound on the support. Independent atoms here need not satisfy either cap or $Q(V_B)\le d$. On tail steps of width $1/10$ from $29/5$ to $48$, with a constant remote tail, the raw linear price exceeds $2.0654\cdot10^{-9}$ using four equal pieces on each of the three finite slabs and $9.0172\cdot10^{-9}$ using eight. Thus improving the atom or tail integration alone cannot certify exclusion on these meshes with these rows and center. This is not a positive surplus. On the eight-piece mesh, test whether the full quadratic, the moved-center radius, and the nine half-slab contrasts are compatible with nonnegative surplus and both first caps before attempting simultaneous second completion.

## After Work: Where the eight-piece fit must move

Any eight-piece fit with nonnegative surplus must change $B$ from the reference by **more than $0.0915$ on at least one original negative slab**. Use the linear response inequality below in the fit, not a guessed slab or a required sign on every slab.

Indeed, put $s_i=w_i(1-\Re(\overline{\gamma_i}V_i))$ for each normalized first cut at its field and frequency. For a feasible law these are nonnegative. Before taking the raw atom suprema the price adds exactly $\sum_i s_i+\sigma(d-Q(V_B))+\sigma Q(V_B-Z)$ to the surplus. In particular,
$$M-8/9+\sigma Q(V_B-Z)+\sum_i s_i\le F_8.$$
This is **one** budget, not a separate allowance on top of the radius. Aggregate the 254 retained $B$ directions with $40\le x_i\le80$. Write $S=\sum_{\rm band} w_i$ and let $p(t)$ be their summed primitive from $t$ to infinity; the $i$th summand is $(w_i/C)\Re[\overline{\gamma_i}e^{(-1/2+ix_i)t}/(1/2+ix_i)]$. The reference band slack exceeds $5.11565\cdot10^{-8}$. Since the band slack at a successful law is at most $F_8$, the directional response must increase by more than $4.1530\cdot10^{-8}$.

Set $h_j=p(z_j)-p(z_{j+1})$. On each unrefined finite slab its response increment is $h_j(B_j-B_{*,j})\le |h_j|-h_jB_{*,j}$. Summing these uppers on $[3/200,29/5)$ costs less than $1.1550\cdot10^{-8}$. On the refined slabs and the infinite tail allow even arbitrary measurable $|B|\le1$: Since $|p'(t)|\le S e^{-t/2}/C$ and $|B-B_*|\le2$, their combined contribution is at most $4S(1-e^{-3/400}+e^{-29/10})/C$. Subtract both costs from the required response. The default checker below gives
$$\sum_{z_j<0} h_j(B_j-B_{*,j}) > 1.9284\cdot 10^{-8}.$$
With $|B_j-B_{*,j}|\le0.0915$ on every negative slab, sum the smaller of $0.0915|h_j|$ and $|h_j|-h_jB_{*,j}$ on each; this cannot pay the computed residual. This localizes a necessary change, not an impossibility at full width. In a restricted-frequency pilot include the aggregate row even if its individual weights are small; keep the full quadratic, both continuous caps, and simultaneous second completion for a witness. [Reason for changing the fit order and handoff](first-fit-decision.md).

## Replay

From the repository root with SageMath 10.9:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-three-midpoints-33.py
```
