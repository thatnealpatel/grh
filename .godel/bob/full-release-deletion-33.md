# Delete-33: Exclusion at the original knots

**Decision.** At $c=39/20$ the original knots cannot support the requested refit: Every law satisfying the two unfolded caps and simultaneous second replies has $M-8/9<-6.6728\cdot10^{-9}$. Keep $X=0$ left of $-144/25$, allow any independent probability law on $u\in[0,1]$ on **each** of the 1,256 finite reference slabs, and allow arbitrary measurable laws on $[29/5,\infty)$. Here $X=2u^2-1$, $T(X)=4X^3-3X$, $(A,B,U)=\mathbb E(X,T(X),u)$, and $M=\int_0^\infty te^{-t}U(t)\,dt$. No previously derived regional-score, support-count, or shape condition needs to be imposed. This is not an exclusion for unrestricted all-real laws or a relaxation of the unfolded caps. No Alpöge input is used.

## What changed the sign

Keep the [previous 106 and 57 first frequencies](all-slabs-deletion-33.md), on $A$ and $B$, respectively, and the **one** reference-centered second tangent. Refit the first multipliers as complex vectors (charge their Euclidean norms), and vary the second multiplier. A smoothed Newton search using the stationary atoms of each slab score, not a final frozen list of atom sites, nominated the [new dual](deletion-laws/delete-33-full-release.json). The finite-tail search objective, about $-1.01\cdot10^{-8}$, is not the certificate.

For the certificate apply the [joint-price inequality](joint-tail-deletion-33.md#joint-price). Every admissible law satisfies the first directional cuts and $Q(V_B)\le d$. Dropping $Q(V_B-V_*)\ge0$ gives the retained tangent; thus even this relaxation suffices to exclude the requested **full** quadratic fit. On every finite slab maximize $m u-a X-b T(X)$ jointly over the full atom interval by Bernstein subdivision, with $m,a,b$ integrated over that slab. On the tail maximize pointwise, charge interpolation at spacing $1/4800$, and pay the remainder past $48$. The signed reference corrections use the same law and moment normalizations throughout.

| Term in the surplus upper bound | Value, rounded |
|---|---:|
| Reference surplus | $-6.60789162635\cdot10^{-7}$ |
| Weighted slack | $1.29072531406\cdot10^{-7}$ |
| Negative-slab gain | $1.34407737397\cdot10^{-7}$ |
| Nonnegative finite-slab gain | $2.66882727184\cdot10^{-7}$ |
| Measurable tail: grid, interpolation, and remote | $1.22138365429\cdot10^{-7}+1.48173411294\cdot10^{-9}+1.33259736189\cdot10^{-10}$ |

The ball for their sum $P$ is centered at $-6.672807369519869562408\cdot10^{-9}$ with radius below $4.1\cdot10^{-31}$. This encloses an **upper price**, not the optimal surplus. The allowance printed for a cutoff of $40$ is not added to the measurable-tail price.

In parallel, a primal conic fit used independent negative slab moments, the early and signed regional requirements, and the full (not rank-truncated) quadratic kernel. The solver stopped with a numerical error. Its iterate passed $Q\le d$ by about $4.46\cdot10^{-6}$ but had $|V_A(61.56771\ldots)|>4.31$ and $|V_B(4.51849\ldots)|>1.00037$. No completion or witness follows. The exclusion depends only on the dual replay, not on the solver's termination.

## Which constancy assumptions matter?

To remove constancy on any subset of finite slabs use [the release checker](check-released-slabs-33.py). For each slab $I$ let $E_I$ be the exact upper **used** in the fixed-slab computation (the slab atom upper, before its reference correction). Let $N_I$ bound the integral of the pointwise maximum of the same atom density. Clearing the constancy restriction costs at most $\max(0,N_I-E_I)$ **relative to the computed bound**: In the new sum one can replace $E_I$ by $N_I$, leaving the identical reference integral untouched. This does not assert that the increase of the true optimum is bounded by the difference of two uppers. Round each difference upward before adding or sorting.

For $N_I$, on each $h=1/1600$ cell interpolate the density of a *fixed* atom quadratically in the real coordinate. The three Bernstein weights are nonnegative and have integral $h/3$ each. Bound their controls by three independent atom maxima, and charge the integrated remainder as in the [signed-kernel derivation](measurable-negative-deletion-33.md#continuum-to-cell-bound). On negative cells use the cubic maximum over $X$; on nonnegative cells all three controls are degree at most six in $u$. The new mass term has third derivative $(3-t)e^{-t}u$, bounded in modulus by $3e^{-t/2}$ for $t\ge0$. Thus add $3$ to that derivation's $L_3$ on these cells. Zero and all kernel branch points lie on cell boundaries. No competitor or maximizing selection is differentiated.

* Keeping the original slabs to the left of $1/2$ but allowing arbitrary measurable laws everywhere from $1/2$ onward costs less than $2.688\cdot10^{-9}$. The upper bound is still below $-3.985\cdot10^{-9}$.
* Keep only the 179 original slabs with the largest upward-rounded release costs, each with its **own arbitrary** constant law. Release all other finite slabs to measurable laws. The list of protected left knots, in units of $1/400$, is generated by the checker. The remaining costs sum to less than $6.438\cdot10^{-9}$, leaving an upper below $-2.34\cdot10^{-10}$. This guarantees one specified set of 179 suffices, not that any 179 suffice or that 179 are necessary. Both comparisons keep the left cutoff and the same constraints at $39/20$.

## A one-knot test and a depth check

Insert just the midpoint $1/400$ of the slab $[0,2/400)$. Evaluate the **integrated** atom scores for $u=14/1000$ on the left half and $u=41/1000$ on the right half using the exact primitive differences. Subtract $E_{[0,2/400)}$. The increment exceeds $4.2014\cdot10^{-8}$, so adding it to $P$ gives more than $3.53\cdot10^{-8}$ even though only one old slab was changed. This gives a lower bound on the re-evaluated *price with this cut list and the other allowances unchanged*. It is not a feasible law. A numerical reoptimization at the same first frequencies and second center on a discretized tail still priced the split near $+3.18\cdot10^{-8}$, also not a certificate.

In the opposite direction, the original-knot exclusion persists slightly above $39/20$. In units normalized at $c_0=39/20$, put $r=\cosh(c)/\cosh(c_0)$. The new first radius is $r$, and homogeneity gives $Q(V_B)\le r^2d$. Hence all density and atom terms are unchanged in the fixed coordinates: Only add $(r-1)\sum_{\rm first}\sigma+(r^2-1)\sigma_{\rm second}d$ to $P$. The checker verifies that this is below $-5.16\cdot10^{-11}$ at $c=1.950000042$, hence negative throughout $0\le c\le1.950000042$ by monotonicity. This last claim concerns the original slabs, not the 179-slab release.

## Replay and next decision

From the repository root, with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-all-slabs-deletion-33.py .godel/bob/deletion-laws/delete-33-full-release.json --upper 0
/opt/sage-10.9/bin/python .godel/bob/check-released-slabs-33.py
```

Do not refit on the original knots. The single midpoint above is a small change for which the present exclusion fails. Test it with the full quadratic during the fit and an exchange against violated first frequencies. Keep the old regional scores and curvature budgets only if repriced for the split. Any primal nominee must still pass both continuous caps and simultaneous second completion; a positive dual price by itself is not evidence of feasibility.

## After Work: Which moments must jump at the midpoint?

Keep exactly the one new knot at $1/400$ and the original scope elsewhere, including the arbitrary measurable tail. Let $\Delta Y=Y_R-Y_L$ be the difference of the law means on the right and left halves of $[0,1/200)$. At $39/20$, satisfying the caps and simultaneous second replies with $M\ge8/9$ requires **all three** strict inequalities:

| Moment | Lower bound for $\Delta Y$ | Upper bound for $\Delta Y$ |
|---|---:|---:|
| $U$ | 0.00226 | 0.05243 |
| $A$ | 0.000249 | 0.00666 |
| $B$ | 0.00223 | 0.05937 |

In particular it does not suffice to split the first moment $A$ while tying the expensive quadratic field $B$ across the midpoint, even if $B$ can change on every other slab. The bounds refer to moment differences, not to changes in the individual atom sites, and do not require either half to equal the old reference law.

To see this, retain the old computed price $P$ and the atom upper $E$ **used** there for the whole slab at zero. On each half $i$ put $S_i=m_i U_i-a_i A_i-b_i B_i$, using the exact mass and the differences of the two signed-price primitives at its endpoints. The reference is unchanged, so substitution in the old sum gives

$$ M-8/9\le P-E+S_L+S_R. $$

This uses the actual two laws here and retains the old allowances everywhere else. For a moment function $y(u)\in\{u,X,T(X)\}$ and signed multiplier $k$, bound $S_L+kY_L$ and $S_R-kY_R$ separately by maximizing their atom polynomials over **all** $u\in[0,1]$. Write $H(k)$ for the sum of the two Bernstein uppers. Then $M-8/9\le P-E+H(k)+k\Delta Y$. To prove a lower cutoff $l$ use $k>0$ and check $P-E+H(k)+kl<0$; for an upper cutoff use $k<0$. No dual optimizer, clipping of the admissible atoms, or assumption that the two maxima are compatible with the other constraints is needed. The six signed multipliers and tests are in [the release checker](check-released-slabs-33.py); its replay command above is unchanged.

**Curvature budget for the split.** The [quadratic expansion](joint-tail-deletion-33.md#joint-price) of the sole second cut gives the tangent inequality with the additional term $Q(V_B-V_*)$ on its left. No local coefficient or reference integral changes. With $\sigma$ the multiplier in the new cut list, the stronger joint row is therefore

$$ M-8/9+\sigma Q(V_B-V_*)\le P-E+S_L+S_R. $$

In particular, maximizing the two *untilted* half scores separately gives $Q(V_B-V_*)<5.027\cdot 10^{-5}$ whenever $M\ge8/9$. This reprices the difference curvature for the split; it is not the older original-knot budget and does not replace $Q(V_B)\le d$.

**Next fit.** Keep the full quadratic and first-frequency exchange. Allow all three moments to jump in the indicated direction; do not lock either field across the split. The linear row $S_L+S_R\ge E-P$ underlies all six cutoffs. Use conservative endpoints if representing the row numerically. These are necessary tests, not evidence for a feasible split. The older regional scores still need their own repricing before reuse.
