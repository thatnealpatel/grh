# Delete-33: Five point caps and the quadratic loss budget

At depth $39/20$, release the five original slabs starting
at $(0,2,4,6,16)/400$ and allow a measurable tail from $29/5$.
Every other finite slab still allows an independent constant
law. This note separates three tests on that same domain.

* A [seven-atom law](deletion-laws/delete-33-five-release-five-caps.json.gz)
  satisfies the disks at $A(0)$, $B(0)$, $A(1)$, $A(611/10)$,
  and $B(2/5)$. All five moduli are below one, and all nine
  fixed raw tangent prices are above $3.5\cdot10^{-11}$.
  The smallest is the `eight-knots` price, about
  $3.64574905\cdot10^{-11}$. Adding these five cap penalties
  to a convex combination of the nine raw prices cannot
  certify a negative bound. This does not verify the
  continuous first caps.
* Retaining the full second-reply quadratic loss puts all
  nine corrected prices below $-0.0033$ on both this law
  and the [earlier frequency-one law](five-release-frequency-one-33.md).
  For `eight-knots`, the losses are about $0.00358261433$
  and $0.00337956329$, respectively. Thus none of the
  positive raw margin survives on either law. This is a
  rejection of the two witnesses for the corrected-price
  relaxation, not an exclusion of their release set.
* Uniformly on the entire release set, the `eight-knots`
  raw price is below $1.07\cdot10^{-9}$. Consequently any
  feasible law with surplus at least $-10^{-10}$ must have
  $\sqrt{Q(V_B-Z)}<0.0013$ for this certificate, where $Z$
  is its auxiliary $B$ center. This necessary condition
  holds without any finite mesh restriction on either the
  five released slabs or the tail.

## Identity and uniform localization

Use the [moved tangent](three-midpoints-deletion-33.md#the-center-is-not-a-law)
and the [unfolded kernels and majorant](joint-tail-deletion-33.md#joint-price).
Write $R$ for a raw price, $w_i$ for its first-cut weights,
$V_i$ for the corresponding normalized field values, and
$\gamma_i$ for the unit directions. Let $\sigma$ be the
second multiplier and $d$ the majorant integral. For any
law, the exact real polarization identity is

$$
R = M-8/9 + \sum_i w_i(1-\Re(\bar\gamma_i V_i))
      +\sigma(d-Q(V_B))+\sigma Q(V_B-Z).
$$

The last term is the full remainder for this quadratic
cut, not $\sigma Q(V_B)$, and $Z$ need not be realizable.
For a feasible law all three added terms are nonnegative.
Also $|V_i-\gamma_i|^2\le 2(1-\Re(\bar\gamma_i V_i))$ by
$|V_i|\le1$. The uniform raw upper therefore gives the
stronger joint restriction

$$
\tfrac12\sum_i w_i|V_i-\gamma_i|^2+\sigma Q(V_B-Z)
       <1.17\cdot10^{-9}
       \quad\text{if }M-8/9\ge-10^{-10}.
$$

Here the `eight-knots` multiplier is about $0.000703546$.
The radius is for the $Q$ seminorm, not for the sup norm.
The uniform raw bound uses the unsplit finite supports,
five measurable-release increments priced at spacing
$1/6400$, and the pointwise tail price at spacing $1/800$
through $60$, with the interpolation and infinite-tail
allowances. Its checked value is about $1.06394326\cdot10^{-9}$.

One cannot close this gap by charging only the radial
mismatch of $Z$ in the second constraint. By Cauchy--Schwarz
for $Q$, the best lower bound on
$\sigma(d-Q(V_B)+Q(V_B-Z))$ using only $Q(V_B)\le d$ is
$\sigma(\sqrt d-\sqrt{Q(Z)})^2$: Equality in the relaxed
field space occurs on the ray through $Z$ at radius $\sqrt d$.
For this certificate the charge is less than $1.1\cdot10^{-15}$,
already much smaller than the checked positive raw price.
Using the profile constraints to get a stronger directional
bound is a different test.

## Replay and next test

Both serialized laws use weights and sites in units of
$10^{-12}$, the original slab boundaries with $1/3200$
subdivisions on the five released slabs, and the existing
step tail through $48$. The remaining tail has $A=B=0$
and $U=1/\sqrt2$. The checker evaluates the raw prices and
point disks from those rational laws. To evaluate curvature,
it forms the weighted jumps of the difference, including
its last jump at $48$ because the center continues beyond
that point. The sum and difference jump convolutions are
paired with the two exponential kernels by prefix moments.
An explicit ordered-pair check replays the kernel evaluation
on a small asymmetric step field. No discretization in the
frequency integral is used for the quadratic loss.

```sh
/opt/sage-10.9/bin/python .godel/bob/check-five-release-curvature-33.py --jobs 6
```

**Next test.** Refit for the joint loss budget on this set
before adding more point caps to the linear relaxation. In
particular, try the full convex $Q$ constraint at the
inherited directions, and check whether a positive price
survives within the budget, rather than trying to repair
these two far-off raw witnesses. A new negative price must
cover arbitrary released laws and the measurable tail,
not just the fit mesh. Both the full five-release and the
full eight-knot frontiers remain open. The seven-knot
exclusion is unchanged. Keep the Alpöge exclusion.
