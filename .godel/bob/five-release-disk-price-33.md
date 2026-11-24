# Delete-33: Exclude the five releases at 0, 2, 4, 8, and 10

At depth $39/20$, impose the 581 inherited $A$ disks, the
62 inherited $B$ disks, and the inherited quadratic $Q\le d$.
For each assignment below the five slabs, each of length
$2/400$, and the tail from $29/5$ admit arbitrary measurable
common laws. Each other finite slab admits its own constant
common law, and the field vanishes to the left of $-144/25$.
The [disk-normal price][table] gives these upper bounds:

| Release starts in units of $1/400$ | Upper for $M-8/9$ |
|:--|--:|
| $(0,2,4,8,10)$ | $-3.0\cdot10^{-10}$ |
| $(0,2,4,6,14)$ | $-1.5\cdot10^{-9}$ |
| $(0,2,4,6,16)$ | $-3.8\cdot10^{-9}$ |
| $(0,2,4,8,12)$ | $-3.6\cdot10^{-9}$ |

The first row is a new exclusion at the target $-10^{-10}$.
The other three improve [previous exclusions][previous].
Only the assignments $(0,2,4,6,k)/400$ for $k=8,10,12$
remain unexcluded at the [five-release frontier][frontier].
Neither the eight-knot frontier nor the seven-knot exclusion
changes. No Alpöge input is used.

## Price and check

If multiple supporting halfplanes use one disk $|V_i|\le1$,
combine their nonnegative weights and unit normals to form
$W_i=\sum_j w_{ij}\gamma_{ij}$. The single nonnegative slack
$|W_i|-\Re(\overline{W_i}V_i)$ has the same linear term and
no larger constant than the sum of those halfplane slacks.
This permits moving the normal without adding a frequency,
including at zero where the older table has repeated rows.
The checker treats each stored direction as an exact decimal
pair and normalizes it before applying its separate positive
weight. It verifies equality of the distinct disk keys and of
the quadratic parameters with the inherited price.

The quadratic slack remains $\sigma(d-Q(V_B)+Q(V_B-Z))$.
The center $Z$ is an auxiliary field, not a candidate common
law. A nonnegative weighted combination of tangents can be
recentered at their weighted mean: The linear term is
unchanged, and the constant decreases by the weighted sum
of $Q$ of the center differences. This uses the ambient
positive semidefiniteness of the [inherited form][identity].
Here the stored center is on the inherited knot lattice.
The replay evaluates its own constant $\sigma(d+Q(Z))$
and its own linear term; it assumes no numerical agreement
with the optimizer's tangents or residuals.

The floating search used disk halfplane and $Q$ tangent
exchange on the 2,701-cell recovery mesh, with independent
local alternatives for the common atom. Its selected
multipliers nominated the new normals and a slightly moved
center. The floating mesh reprice was approximately
$-4.10\cdot10^{-10}$, with the law beyond $56$ frozen;
no candidate primal from that search passed the disk and
$Q$ tests. The mesh reprice alone was not an exclusion of
measurable laws. An earlier nominated price gave a full-domain
upper of about $-4.16\cdot10^{-11}$ and did not separate.

The checker uses the [existing measurable pricing][previous]:
Bernstein upper support over the full atom interval, with
quadratic interpolation and uniform residuals on the
released slabs and on the tail through $60$, plus an
analytic remote allowance. One finite price and one tail
price suffice for all seven assignments; only the five
local release replacements change. The checked upper for
$(0,2,4,8,10)/400$ is approximately $-3.0586710\cdot10^{-10}$.

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-five-release-disk-price-33.py
```

This replay needs no optimizer or scratch state. For the
three open sets with last start $8$, $10$, or $12$ in units
of $1/400$, the same price gives uppers of approximately
$8.7684\cdot10^{-9}$, $4.6632\cdot10^{-9}$, and
$1.2828\cdot10^{-9}$, respectively. These are not lower
bounds or feasible laws. Recenter and refit the inherited
disks first for $(0,2,4,6,12)/400$, the smallest of those
three prices, and reprice all three before freezing another
certificate. No new frequency is required for this exclusion.
Use the mesh stop to nominate a price for that replay; a fixed
extra mesh margin [did not help][mesh-stop] on the last seed.

[mesh-stop]: five-release-mesh-stop-decision.md
[table]: deletion-laws/delete-33-five-release-disk-price.json
[previous]: five-release-independent-price-33.md
[frontier]: eight-piece-deletion-33.md#price-exactly-two-knots-and-refine-five-releases
[identity]: five-release-curvature-33.md#identity-and-uniform-localization
