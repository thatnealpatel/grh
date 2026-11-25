# Delete-33: Freeing a crest slab defeats the released support price

At depth $39/20$, retain the fixed $A$ disk price of the
[third-moment band test](third-moment-band-33.md#one-price-three-release-tests).
Replacing its affine observable by the true nonlinear
common-atom support does **not** suffice if one frees the
exempted crest slabs in that support while imposing the
$B$ caps only on a separate completion. This obstruction
holds for two of the three exemption sets, even when the
completion has no added knots. Keeping the completion's
$B$ on the single crest slab restores a negative bound on
each of the two witnesses, even if the four negative
slabs remain free.

## Which relaxation fails

Use the same $a(t),m(t)$, $l=-144/25$, weights $\omega_i$,
and $c=-8/9+\sum_i\omega_i$ as in the band test. Write
$$
H_t(b)=\sup_{\nu:\ \mathbb E_\nu T_3(X)=b}
           \mathbb E_\nu\big[a(t)X+m(t)u\big],
\qquad X=2u^2-1,\quad 0\le u\le1.
$$
Here $\nu$ ranges over probability measures on $[0,1]$.
Let $R$ be a union of exempted original slabs, with all
supports allowed to vary measurably in $t$. Define
$$
L_R(y)=c+\int_{[l,\infty)\setminus R}H_t(y(t))\,dt
        +\int_R\sup_{|b|\le1}H_t(b)\,dt.
$$
One proposed sufficient test is to show $L_R(y)<-10^{-10}$
for every completion $y$ meeting the 62 inherited $B$ disks
and $Q(V_y)\le d$. This tests the true curved support, not
a tangent at $B_0$. However, it drops the requirement that
the support and the caps use the same $B$ on $R$.

Let $N$ be the four original slabs with starts
$(-2304,-2288,-322,-216)/400$. Use the code's exact rational
fields $y$, each of the form $\operatorname{clip}((1+\alpha)B_0)$
plus five rational shifts on $R$. Clipping is at $\pm(1-10^{-10})$.
The following are outward-rounded bounds in units of $10^{-7}$.
The singleton notation adjoins the original slab with the given
left endpoint.

| $R$ | $\alpha$ | Lower on $L_R(y)$ | Upper on $L_N(y)$ | Upper on $L_\varnothing(y)$ |
|:--|--:|--:|--:|--:|
| $N\cup\{0\}$ | $12/10^5$ | $2.0444$ | $-6.0466$ | $-6.1736$ |
| $N\cup\{2/400\}$ | $6/10^5$ | $1.4771$ | $-2.4608$ | $-2.5877$ |

Both completions satisfy $|y|<1$, all 62 inherited $B$ disk
moduli below $0.99999975$, and $d-Q(V_y)>2.8\cdot10^{-7}$.
The quadratic evaluation keeps all cross terms. No
continuous-frequency $B$ cap is claimed here. Neither a
feasible law nor a positive surplus is asserted: The lower
bounds are on a fixed price with measurable support choices,
not on the objective with the $A$ disks and eight-knot mask
imposed. The negative prices are at the two particular
completions, not uniform estimates over the $B$ constraints.
There is no obstruction here for $R=N$ or for other $A$ prices.

## Verification and next decision

For the lower bound, split the integral at the original
slab edges and the same panel edges as the band checker.
Integrate $a$ by its disk primitive and $m$ exactly in
128-bit ball arithmetic. On each panel use a constant law.
At positive mass a floating atom search only proposes
rational atoms. Their rational mixing weights enforce $y$
exactly on unexempted panels. At zero mass, one exact outer
root (reflected if needed) attains the signed $A$ support.
On exempted panels no $B$ constraint is used. Beyond $60$,
$|A|\le1$ and $mU\ge0$ give the lower tail debit. The two
upper bounds use the band checker's control interpolation,
with its full absolute remainder and remote debit.

Replay with SageMath's Python and assertions enabled:
`.godel/bob/check-released-curvature-33.py`. `--reference`
checks the released and fixed endpoint choices, both mass
regimes, and a rational fixed-moment mixture.

Do not seek a uniform $L_R$ upper for these two sets with
this fixed $A$ price. The next test is to price $B$ jointly
with common-atom support on the crest slabs, keeping the
same $B$ in the inherited disks and $Q$. A first target is
a coupled upper on the original $B$ mesh before allowing
mobile knots or a measurable tail. For such a mesh test,
any redistribution of the linear $B$ price within a finite
slab must preserve its integral there. A measurable $B$
tail instead needs a pointwise price or a tail error debit.
