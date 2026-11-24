# Delete-33: A signed six-release obstruction to reusing prices

The five-release class is [excluded][five] at depth $39/20$.
For the next test, release the six baseline slabs starting at
$(-216,0,2,4,6,8)/400$, each of length $2/400$. These slabs
and the entire tail from $29/5$ admit arbitrary measurable
common laws. Each other finite slab has its own constant
common law, and the field vanishes left of $-144/25$.
The parent question is whether a law on this domain can
reach $M-8/9\ge -10^{-10}$ while satisfying the 581 inherited
$A$ disks, 62 inherited $B$ disks, and $Q\le d$. No Alpöge
input is used.

**Decision:** Repricing more finely, mixing the eight listed
inherited prices, and compressing or recentering the resulting
mix cannot separate this mask. On the support domain, which
retains the common laws and constancy conditions but drops
the disks and $Q\le d$, one profile makes every such compressed
and recentered convex mixture exceed $2.6\cdot10^{-8}$.
The inherited `five-release-disk-price-k8` functional alone
has full-domain support less than $3.36\cdot10^{-8}$, so its
positive price is not an artifact of a loose interpolation
upper. The profile violates even the inherited $A(0)$ disk:
$V_A(0)>2.8$. This is not a feasible law, and it gives no lower
bound on the maximum under the original disks and quadratic.

## One profile, including the best constant discounts

The checker uses the `five-release-disk-price-k8` price as
anchor. Its [serialized profile][profile] has a rational point
atom $u\in[0,1]$ on each unchanged slab, on each $1/1600$ cell
of a released slab, and on a step mesh on the tail through
$56$. After $56$ it uses $u=1/\sqrt2$, so $A=B=0$ there and
only mass remains. Sage balls enclose the primitive differences
at the profile's actual endpoints. In particular the mass
primitive is constant on $[-216,-214]/400$. Floating point
selected the rational witness but is not used to verify it.

For price $i$, write $P_i(H)$ for its raw affine evaluation
on profile $H$, $s_i$ for the sum of raw disk weights, $W_{ik}$
for its total complex disk vector at key $k$, and $(\sigma_i,Z_i)$
for its quadratic multiplier and center. All eight prices use
the same keys and the same [positive semidefinite form][form].
For convex weights $\theta_i$,
compressing the disk rows and recentering at
$\bar Z=\sum_i\theta_i\sigma_iZ_i/\sum_i\theta_i\sigma_i$
keeps the linear term fixed. The new affine value is the
weighted raw evaluation minus two constant discounts:

$$
\begin{aligned}
D_{\rm disk}&=\sum_i\theta_i s_i-\sum_k\left|\sum_i\theta_i W_{ik}\right|,\\
D_Q&=\sum_i\theta_i\sigma_i Q(Z_i-\bar Z).
\end{aligned}
$$

Use the anchor's unit vectors $\gamma_k=W_{0k}/|W_{0k}|$ and
center $Z_0$. The disk norm dominates projection on $\gamma_k$,
and the weighted variance about $\bar Z$ is no greater than
that about $Z_0$ by positive semidefiniteness. Hence the sum
of the two discounts is bounded above by the convex average
of the individual debits

$$
 s_i-\sum_k\Re(\overline{\gamma_k}W_{ik})
 +\sigma_i Q(Z_i-Z_0).
$$

Subtract these from the profile evaluations for the following
prices: `five-release-disk-price-k8`, `five-release-disk-price`,
`eight-knots`, `five-releases`, `five-release-joint-refit`,
`five-release-pair`, and the independent and recentered
weight variants of `five-release-joint-refit`. Every difference
exceeds $2.6\cdot10^{-8}$. The same witness therefore rules out
all convex weights, including arbitrary choices of which of
these prices to use. Older signed-mask prices with different
disk keys are not included. This does not cover independent
multipliers or new directions on the same keys, arbitrary
centers outside the mixture, or retaining the quadratic loss.

## Signed upper and next test

For the anchor upper, use the baseline slab supports and
measurable tail through $60$ plus the analytic remote upper.
Replace the six local supports using the signed release
routine, with zero density and the odd-cubic support on the
negative slab. The negative replacement alone adds about
$3.1454\cdot10^{-8}$ to the upper; the eight-source lower
obstruction above does not rely on these local upper
increments or on a remote-tail upper bound.

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-six-release-support-33.py --jobs 4
```

The new calculation calls for genuinely new multipliers or
keeping a constraint in the maximization, not another blend.
A bounded floating disk-halfplane and quadratic-tangent
exchange at the inherited keys returned no usable nomination:
Its last solved LP had surplus about $-4.91\cdot10^{-11}$
with $Q-d\approx1.12$ and a largest disk violation above $11$,
and its extracted dual repriced to about $+1.59\cdot10^{-6}$
on the fixed-remote atom mesh. The next LP timed out. This is
neither a feasible witness nor a dual certificate. A separate
smoothed dual fit with the reference-center return direction
only reduced the floating mesh support from about
$2.92\cdot10^{-8}$ to $2.59\cdot10^{-8}$. Before another
unfocused exchange, identify which of the remaining eight-knot
masks are unpaid after cross-pricing with the accepted five-release
refit, or solve this case with disks and the full quadratic kept
as constraints on a conditioned mesh. Six releases, eight
knots, and unrestricted measurable profiles remain open.

[five]: five-release-disk-price-33.md#one-refit-prices-the-complete-five-release-frontier
[form]: five-release-curvature-33.md#identity-and-uniform-localization
[profile]: deletion-laws/delete-33-six-release-support-witness.json.gz
