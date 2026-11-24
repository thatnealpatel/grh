# Delete-33: A coarse five-release refit changes sign

At depth $39/20$, release the original slabs $I_k$ of
length $2/400$ starting at $k/400$ for
$k\in S=\{0,2,4,6,16\}$. Other finite slabs allow independent
constant probability laws, and the tail from $29/5$ is
measurable. Use the inherited zero field left of $-144/25$.
As in the [joint loss note](five-release-curvature-33.md),
$A=\mathbb E X$, $B=\mathbb E(4X^3-3X)$,
$U=\mathbb E u$, $X=2u^2-1$, and $0\le u\le1$.

Refit the `eight-knots` price using the same first
frequencies and the same three coefficients of the second
cut. Move the first weights and directions, the second
multiplier $\sigma$, and the auxiliary $B$ center $Z$.
The dual objective includes the norm cost of each moving
first multiplier and the full quadratic constant
$\sigma Q(Z)$, paired with $-2\sigma\mathcal B(Z,V_B)$.
The new [serialized tangent](deletion-laws/delete-33-five-release-joint-refit.json)
does not separate the measurable domain.

## Price on the full domain

Write the raw price as $R=\kappa+\int(mU-aA-bB)$, with
$m(t)=\mathbf 1_{t\ge0}te^{-t}$. At fixed coefficients,
the relaxed supremum on a finite constant slab is the
support of its integrated coefficients, whereas that on
a measurable slab is the integral of the pointwise support.
At each support call the optimizer is a single atom:

$$
H(a,b,m)=\max_{0\le u\le1}
  \{mu-a(2u^2-1)-b[4(2u^2-1)^3-3(2u^2-1)]\}.
$$

The following bounds are for **one and the same** tangent.
In the two step tests the tail has the same step partition
through $56$ and the same fixed reference law beyond $56$.
Only the five released slabs change spatial mesh.

| Domain | Lower bound on supremum | Upper bound on supremum |
| --- | ---: | ---: |
| Released slabs stepped at $1/3200$ | $-1.6223\cdot10^{-10}$ | $-1.6214\cdot10^{-10}$ |
| Released slabs stepped at $1/25600$ | $6.2475\cdot10^{-10}$ | $6.2485\cdot10^{-10}$ |
| Measurable releases and tail | $6.2475\cdot10^{-10}$ | $7.2\cdot10^{-10}$ |

The observed sign reversal is not a tail-discretization
artifact. Refining just the five slabs buys, respectively,
about $(2.15306,1.90125,1.64823,1.42205,0.74522)\cdot10^{-10}$.
The lower bracket uses an evaluated atom in every cell, so
positive raw price on the full domain is rigorous. Those
atoms have not been verified feasible under the caps or
second replies. A separate floating refit on the finer
mesh left a positive raw maximum near $6.21\cdot10^{-10}$.
Varying all inherited first multipliers and allowing the
center seven interior jump sites on each released slab
left a floating value near $6.17\cdot10^{-10}$. Neither
fit bounds all possible inherited-frequency certificates.

The full measurable upper and the exact polarization
identity imply that a feasible law with $M-8/9\ge-10^{-10}$
must satisfy

$$
\tfrac12\sum_iw_i|V_i-\gamma_i|^2+\sigma Q(V_B-Z)
 <8.2\cdot10^{-10},\qquad
\sqrt{Q(V_B-Z)}<0.00108.
$$

The radius is specific to the moved center and inherited
quadratic form. It is not a bound on the sup norm.

## Which within-slab variation pays for the sign?

For each released slab write $\bar b_k$ and $\bar m_k$
for the exact averages of those coefficients. Define

a signed price increment for each field by

$$
D^B_k=-\int_{I_k}(b-\bar b_k)B,\qquad
D^U_k=\int_{I_k}(m-\bar m_k)U.
$$

Flattening one coefficient leaves the joint atom law
arbitrary; it is not an assumption of a chosen law or a
product of separate moment ranges. The original price
equals the flattened price plus the corresponding
increment. On the full measurable domain, flattening
all five $b$ coefficients gives an upper below
$-6.5\cdot10^{-10}$. Flattening just $m$ on any one of
the five slabs gives an upper below $-1.7\cdot10^{-8}$.
Thus a feasible law with nonnegative surplus needs
$\sum_kD^B_k>6.5\cdot10^{-10}$ and
$D^U_k>1.7\cdot10^{-8}$ **on every slab**. For surplus
at least $-10^{-10}$ the respective thresholds are
$5.5\cdot10^{-10}$ and $1.69\cdot10^{-8}$.

Allowing the law to choose the sites of its positive
$D^B_k$ does not make one site sufficient: The checker
maximizes over every singleton and pair of unflattened
sites. All pairs except $\{4,6\}$ have raw upper below
$-9\cdot10^{-12}$. The exceptional raw upper is
$8\cdot10^{-11}$, which does not establish realizability.

## The exceptional pair cannot pay the joint loss

Refit the first weights and directions, the second
multiplier, and the full quadratic tangent again, using
only the inherited frequencies and second form. Write
$R_1$ for this [new raw price](deletion-laws/delete-33-five-release-pair.json),
and keep $D^B_k$ defined using the **previous** tangent.
For every feasible law the cap and polarization identity
gives $M-8/9\le R_1$, so

$$
M-8/9-\sum_{k\in\{0,2,16\}}D^B_k
\ \le\ R_1-\sum_{k\in\{0,2,16\}}D^B_k.
$$

The right side is another linear price on all the
released laws. On $I_k$ for $k\in\{0,2,16\}$ its $B$
coefficient is $b_1+\bar b_k-b_k$, not simply the
mean of $b_1$. The first cap and second form can thus
charge variation on these slabs even though the signed
increments being tested are those of the earlier tangent.
Neither the other finite slabs nor the tail are frozen.

The full measurable upper is below $-7\cdot10^{-13}$
(the computed ball is centered near $-7.54505\cdot10^{-13}$).
Consequently nonnegative surplus requires
$D^B_0+D^B_2+D^B_{16}>7\cdot10^{-13}$, excluding the
exceptional pair too. In fact the **third-largest** of
the five $D^B_k$ must exceed $7\cdot10^{-13}/3$: Choose
the two largest sites, use the corresponding flattened
upper, and bound each of the three remaining increments
by the third-largest. This conditions the remaining
search, but does not exclude three or more positive sites.

## Replay and next test

```sh
/opt/sage-10.9/bin/python .godel/bob/check-five-release-joint-refit-33.py
/opt/sage-10.9/bin/python .godel/bob/check-five-release-pair-33.py
```

Sage real balls enclose the exact primitive differences
and signed kernel prices. Bernstein subdivision brackets
each scalar atom support in the step tests. On measurable
slabs (including the tail), quadratic interpolation of
the coefficient vector, sublinearity of $H$, and the
branchwise third-derivative allowance bound the integral.
The tail bound includes the analytic remainder after
$60$. Flattening a coefficient preserves the same error
allowance, since the replacing constant has zero third
derivative. The checker retains the fixed-slab supports,
so these tests do not freeze any of the other laws.

The pair check splits the release interpolants by de
Casteljau subdivision before taking atom supports;
this reduces the convexity gap without resampling the
coefficients. On the three corrected slabs it adds the
third-derivative allowances for both tangents. Its tail
is independently repriced through $68$ with an analytic
remainder, and every segment retains the full jump
support in its convolutions.

**Next test.** Recover a near-optimal joint law of the
unrestricted inherited-frequency refit. On that same law,
compare its surplus to the refit target and check both
inherited disk moduli and the full second quadratic cap
before ranking off-list violations. The [scout decision
replay](five-release-scout-decision.md) gives a cellwise
atom-weight test and records why the raw support proxy did
not supply such a law. If a useful law emerges, use its
cap violations and a dual refit on the full measurable
domain to test whether a small set of additional frequencies
can pay the positive unrestricted margin. A refit conditioned
only on at most two positive increments cannot decide the
unrestricted question.
The five-release and eight-knot frontiers remain open.
The seven-knot exclusion is unchanged. Keep the Alpöge
exclusion.
