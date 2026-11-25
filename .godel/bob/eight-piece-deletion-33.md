# Delete-33: Price four slab releases and seven added knots

At $c=39/20$, keep $X=0$ left of $-144/25$, both unfolded
first caps, and simultaneous second replies at $(-7,6,19)/25$.
Use the [1,257-knot baseline](deletion-laws/delete-33-tail-baseline.txt).
On each retained finite slab one may choose **any** constant
probability law independently, not necessarily the reference law.
The law from $29/5$ onward is arbitrary measurable. Then:

* Dividing each of the first three nonnegative slabs into eight
  equal pieces gives $M-8/9<-4.60062\cdot10^{-8}$.
* Allowing arbitrary measurable laws throughout $[0,3/200)$ still
  gives $M-8/9<-4.13718\cdot10^{-8}$.
* Allowing arbitrary measurable laws on **any four** original
  finite slabs gives $M-8/9<-3.83838\cdot10^{-9}$.
* Allowing arbitrary measurable laws on **all negative** original
  finite slabs gives $M-8/9<-4.68429\cdot10^{-8}$. In this case
  the nonnegative finite slabs still have arbitrary constant
  laws, not fixed reference values.
* Inserting **any six real knots** in the original finite slabs
  gives $M-8/9<-3.38686\cdot10^{-10}$. The five-knot bound is
  $-2.78406\cdot10^{-8}$. The pieces on either side of each
  new knot may have unrelated laws.
* Inserting **any seven real knots** gives $M-8/9<-10^{-10}$.
  This uses several tangents, selected by slab assignment.
* Releasing all negative slabs and inserting **one** real knot
  in a nonnegative finite slab gives $M-8/9<-4.0298\cdot10^{-9}$.

Each bullet is a separate class, and each knot allowance is an
upper limit. Knots at baseline boundaries change no slabs.

Here $X=2u^2-1$, $T(X)=4X^3-3X$, $(A,B,U)=\mathbb E(X,T(X),u)$
for $u\in[0,1]$, and $M=\int_0^\infty te^{-t}U(t)\,dt$.
No regional condition is required. These are profile-class
exclusions, not an all-real exclusion.

## Certificate and replay

Use the [moved tangent inequality](three-midpoints-deletion-33.md#the-center-is-not-a-law)
with the [new cut and center table](deletion-laws/delete-33-eight-piece.json):
577 first cuts on $A$, 426 on $B$, one second cut, and 419 signed
raw $B$ jump corrections at original knots. The center $Z$ need
not be a law. Ambient positivity of $Q$ gives the linear upper
price with constant $-8/9+\sum_{\rm first}w_i+\sigma(d+Q(Z))$.
The finite cell score is maximized over all atoms using the
integrated primitive coefficients, with no restrictions on jumps
of competitor moments. Neither the search's tail discretization
nor its floating-point Gram factorization is used in replay.

The checker encloses the following terms in Sage balls (rounded
here):

| Term | Value |
|:--|--:|
| Constant plus finite atom supports | $-0.0147915284560820353989$ |
| Pointwise tail controls through $48$ | $0.0147914820310787765200$ |
| Tail interpolation allowance | $8.374041\cdot10^{-11}$ |
| Remote allowance | $3.349721\cdot10^{-10}$ |
| Sum on the eight-piece mesh | $-4.6006290764\cdot10^{-8}$ |

To price any set of measurable releases, start from the unsplit
mesh, whose price $P$ is about $-1.9200840981\cdot10^{-7}$.
For each original slab $i$, compute an upper increment $D_i$ by
subtracting its unsplit atom bound from a pointwise atom integral
bound. Clamp the increment at zero and round upward. On
$1/1600$ cells the integral bound comes from interpolating the
score of each fixed atom at both endpoints and the midpoint.
Each Bernstein control admits its own atom maximum. Charge
also the uniform integrated third-derivative remainder,
including the mass term, as on the tail. No law is differentiated.

For a release set $S$ the upper price is $P+\sum_{i\in S}D_i$.
Thus the sum of the four largest increments prices every set of
at most four slabs, without assuming where the release lands.
The four largest are at starts $0,1/200,1/100,3/200$; in units
of $10^{-9}$ they are about $56.9077,50.2166,43.5123,37.5334$.
For all negative slabs the added allowance is about
$145.1654\cdot10^{-9}$. This last test strengthens the earlier
[measurable-negative result](measurable-negative-deletion-33.md),
which froze the nonnegative finite slabs to the reference.

The same sum with five releases has positive upper price,
$2.86494\cdot10^{-8}$, attained as a **price bound** by the first
five nonnegative slabs. Releasing every finite slab has positive
upper price $5.18163\cdot10^{-7}$. Neither sign produces a
feasible law. For a five-release extension, fit on the current
worst five slabs first, then reprice the best five over the whole
mesh with the new certificate; the maximizing set can change.

## Price of a shared split coordinate

For one real knot in slab $[l,r)$, bound the sum of the atom
supports on $[l,x)$ and $[x,r)$ with the **same** unknown $x$.
For each fixed pair of atoms this sum before maximizing is a
constant plus the primitive coefficient vector at $x$ paired
with their moment difference. Interpolate in $x$ on $1/1600$
quadratic cells. At each Bernstein control maximize the sum
separately over the two atoms, then take the largest control
bound and add the uniform interpolation remainder for a moment
difference. All coefficient branch points are cell boundaries.
Subtract the unsplit support and round upward, capping at $D_i$;
for cheap slabs it is enough to use $D_i$ directly. Call the
result $E_i$.

A budget of $k$ knots can buy $E_i$ for one knot in slab $i$,
or $D_i$ for two or more. The checker maximizes the sum over
these options by a budget recurrence, buying at most one
option per slab. This prices coincident slab assignments and
arbitrary real split locations in one test. For the combined
negative-release and one-knot claim, add the largest $E_i$
among nonnegative slabs to the all-negative price.

The six-knot test uses a [second cut and center table](deletion-laws/delete-33-six-knots.json)
with 548 first cuts on $A$, 50 on $B$, one second cut, and 419
raw $B$ jump corrections. The proof is unchanged. Its unsplit
price is about $-2.0092030\cdot10^{-7}$; after maximizing the
six-knot budget the upper price is about $-3.3868670\cdot10^{-10}$.
It still does not exclude all five measurable releases.

Run from the repository root with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-three-midpoints-33.py --certificate eight-piece
/opt/sage-10.9/bin/python .godel/bob/check-three-midpoints-33.py --certificate six-knots
```

## Seven knots: Use different tangents on different assignments

A single tangent need not price every knot configuration. Record
an assignment by the original slabs having one interior knot
or at least two. Charge $E_i$ and one unit of budget for the
former, and $D_i$ and two units for the latter. This encoding
also covers fewer than seven knots, knots at existing boundaries,
and three or more interior knots in the same slab.

For each tangent, enclose its own unsplit price $P$ and slab
increments. Round each term upward to an integer multiple of
$10^{-16}$. Using the six-knot tangent first, enumerate every
assignment of budget at most seven with integer upper price
at least $-10^{-10}$. Pruning uses the same budget recurrence
as above, applied to the remaining suffix of slabs. Specifically,
if $V_j(k)$ is the best increment on the suffix starting at
$j$ with at most $k$ units, the three available terms are
$V_{j+1}(k)$, $E_j+V_{j+1}(k-1)$, and $D_j+V_{j+1}(k-2)$,
omitting terms that overrun the budget. A partial assignment
whose current price plus $V_j(k)$ falls below the cutoff cannot
have an extension at or above it.

Each subsequent tangent takes the same assignment and reprices
it, including its unsplit term. The four additional tables
are in `deletion-laws/delete-33-seven-*.json`. They use
$1/3200$ shared split cells rather than $1/1600$ cells; their
tail integration ends at $56$ or $60$, with a remote allowance
beyond that endpoint. The slab-release bounds are unchanged
in method but recomputed for each tangent. The names indicate
where the tangents were fitted, not restrictions on their use.

| Tangent | Assignments not yet below $-10^{-10}$ |
|:--|--:|
| `six-knots` | 433 |
| `seven-two-negative` | 38 |
| `seven-minus-216` | 13 |
| `seven-minus-2304` | 6 |
| `seven-nonnegative` | 0 |

This is a cover of assignments by proofs, not a sum of
inequalities from different tangents. The last tangent handles
the assignment with one split in each of the first seven
nonnegative slabs, with upper price about $-2.128678\cdot10^{-10}$.
No statement about eight arbitrary knots or five measurable
releases follows from the cover.

Replay all five tables with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-seven-knots-deletion-33.py --jobs 5
```

Omit `--jobs 5` to check the tangents serially.

## Locate the next gaps before fitting

Add `--frontier` to the same command to screen the two next
classes at the same cutoff. For five measurable releases,
charge $D_i$ one unit and omit the split option. For eight
knots keep the same two options as before. No new coefficient
or atom enclosure is needed.

* **Eight knots:** The five tangents leave 1,289 assignments.
  Every one spends all eight units, uses the slabs starting
  at $0$ and $2/400$, and spends at most two units on negative
  slabs. All but three also use the slab starting at $4/400$.
* **Five measurable releases:** The tangents leave 14
  assignments. Every one releases five slabs including those
  starting at $0$ and $2/400$; at most one start is negative.
  The only assignment omitting $4/400$ has starts
  $(0,2,6,8,10)/400$.

These are necessary location tests for achieving surplus at
least $-10^{-10}$, not constructions of laws. An uncovered
assignment need not attain its upper price. In particular, any
further fit should distinguish spending two knot units in a
single slab from buying two different one-knot increments.

## Price exactly two knots and refine five releases

The 1,289 unpaid eight-knot assignments spend all eight units.
Thus every option encoded as two is now known to be exactly two:
Three actual knots in any such slab would exceed the budget.
A measurable release is still an upper bound for that option,
but it ignores the shared coordinates of the two split points.

Let $P(t)$ be the primitive coefficient vector for the atom
score $U m-Aa-Bb$. Write $H(v)$ for the atom support in this sign
convention. For fixed ordered knots $x\le y$ in $[l,r]$, the
three constant laws give the upper price

$$H(P(l)-P(x))+H(P(x)-P(y))+H(P(y)-P(r)).$$

Interpolate each primitive on the $1/3200$ cells with the
same quadratic interpolation as for one knot. Given $x\le y$,
the two interpolated vectors are the marginals of a convex
combination of **ordered** control pairs. For distinct cells
all control pairs are already ordered. For a common cell with
normalized positions $s\le t$, draw two independent uniform
numbers on $[0,1]$, and let $I$ and $J$ count those at most $s$
and at most $t$, respectively. Then $I\le J$, and their
binomial laws give exactly the two Bernstein marginals. By
convexity of the three-support expression, the maximum over
ordered control pairs bounds the interpolated price. Add the
one-knot interpolation allowance twice: Each primitive error
pairs with the difference of its two neighboring laws. All
kernel branches and the mass branch at zero are cell endpoints.
For an increment over the stored base price, subtract a lower
bound for the unsplit support. The Bernstein atom routine
returns a certified sampled lower bound plus its tolerance,
so subtracting that tolerance provides the needed lower bound.

For a measurable release, use the pointwise atom support and
its usual interpolation remainder, at $1/3200$ instead of
$1/1600$ on the remaining release sites. In the
`five-releases` tangent, the upper increment at slab $0$
drops from about $56.9063\cdot10^{-9}$ to
$56.2501\cdot10^{-9}$. The latter is an upper price, not
an attained gain. All four new tangents also use the full
original partition and include the complete measurable tail.
Their labels describe the fit, not the inequality's domain.

| Screen | Eight-knot unpaid | Five-release unpaid |
|:--|--:|--:|
| Original five tangents | 1,289 | 14 |
| Same tangents, two-knot prices | 933 | 14 |
| `five-releases` | 884 | 9 |
| `five-release-minus-216` | 878 | 8 |
| `five-release-minus-2304` | 812 | 7 |
| `eight-knots` | 776 | 7 |

Only 67 of the remaining eight-knot assignments have a
slab with two knots, and none have two such slabs. The two
assignments omitting slab $4/400$ are
$(-2304,-216,0,2,6,8,10,12)/400$ and
$(-216,0,2,6,8,10,12,14)/400$.

The remaining five-release sets have exactly the following
starts, in units of $1/400$:

* $(0,2,4,6,k)$ for $k\in\{8,10,12,14,16\}$;
* $(0,2,4,8,k)$ for $k\in\{10,12\}$.

In particular, any five-release law reaching surplus at least
$-10^{-10}$ is constant on every negative slab. The eight-knot class is not excluded in full. The prior
local fits were sampled relaxations; no admissible law
with nonnegative surplus is known here.

**Subsequent result.** One [refitted disk-normal price][disk-price]
excludes all seven sets at surplus $-10^{-10}$, with all
five releases and the tail measurable. This closes the
five-release class, but not the eight-knot class.

[disk-price]: five-release-disk-price-33.md#one-refit-prices-the-complete-five-release-frontier

Replay with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-refined-frontier-33.py --jobs 5
```

## Eight knots: Slab 4/400 is necessary

Neither of the two assignments above can attain surplus
at least $-10^{-10}$. Use a $1/6400$ shared-coordinate
mesh on the eight selected slabs, instead of the coarser
bound or a measurable-release proxy. The first assignment
uses `seven-two-negative` and $1/400$ tail cells; the second
uses `five-release-minus-216` and $1/800$ tail cells,
which keep its uniform tail interpolation allowance below
$1.267\cdot10^{-11}$.
The resulting upper prices are about $-2.35418\cdot10^{-10}$
and $-1.17157\cdot10^{-10}$, respectively. Thus **every** law
in the eight-knot class reaching the cutoff must split each
of the slabs starting at $0$, $2/400$, and $4/400$. The
cover leaves at most 774 assignments, 67 with a double slab.

```sh
/opt/sage-10.9/bin/python .godel/bob/check-eight-knots-omit-slab-33.py
```

## Eight knots: Cross-price with the five-release refit

Use the accepted [five-release refit][disk-price]
`five-release-disk-price-k8` on the 774 assignments surviving
the preceding screens. Its disk keys and quadratic parameters
match those of `eight-knots`: 581 $A$ disks, 62 $B$ disks, and
$Q\le d$ at depth $39/20$. The domains of the earlier screens
are unchanged. In particular, only the chosen finite slabs
are split, each resulting piece has its own constant common
law, and the whole tail remains measurable. No Alpöge input
is used.

Recompute the unsplit price with $1/800$ tail cells through
$60$ and a remote allowance. On the finite slabs in the
remaining assignments, first price a measurable release on
$1/1600$ cells with the signed routine (the mass density on
negative slabs is zero). For one knot, use the lesser of this
release price and the shared-coordinate bound on $1/6400$
cells, taking only the release price when its increment is at
most $5\cdot10^{-9}$. For two knots, use the lesser of the
release price and the ordered-control bound on $1/3200$ cells.
Round the base and increments separately upward to multiples
of $10^{-16}$. An assignment is removed only when the sum is
strictly below $-10^{-10}$.

The cross-price removes 619 of the 774 assignments. The 155
unpaid assignments spend all eight units, split the slabs
starting at $0$, $2/400$, and $4/400$, and only 14 have a
double slab. Of the 155, exactly 109 spend one unit on a
negative slab, and 45 spend two. Each of those 154 uses at
least one of the slabs starting at $-216/400$ and $-2304/400$.
The sole all-nonnegative assignment makes one split in each
of the eight slabs starting at $(0,2,4,6,8,10,12,14)/400$.
These are surviving *upper-price* assignments, not feasible
laws. The cross-price does not exclude eight knots or six
measurable releases.

The refined-frontier checker now replays both omissions and
this cross-price. To export the residual masks for a refit,
use `--write-eight` with a scratch destination:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-refined-frontier-33.py --jobs 6 --write-eight /tmp/delete-33-eight.json
```

## Eight knots: Exclude the all-nonnegative class

Change only 42 individual disk weights in the cross-price,
using the [rational deltas][radial] indexed from zero among
its five-entry disk rows. Each integer delta is divided by
$10^{20}$. The modified weights are strictly positive; the
center, disk directions, and quadratic row are unchanged.
Redo the base and measurable tail with the same meshes, then
use direct shared-coordinate bounds at $1/12800$ for one
knot and ordered-control bounds at $1/3200$ for two. The
one-knot calculation uses the signed mass primitive, constant
on negative slabs. Do not carry forward any slab price or
base price from the unmodified tangent.

The all-nonnegative assignment has rounded upper price
$-1.885403\cdot10^{-10}$. Together with the preceding screens,
this excludes **any** insertion of up to eight interior knots
confined to nonnegative finite slabs, at the same cutoff.
The refit also excludes 17 signed assignments; the least
negative integer upper among the 18 exclusions is
$-1.139268\cdot10^{-10}$. A direct $1/6400$ single-knot mesh
with these weights does not pay for the all-nonnegative case;
the finer shared-coordinate bound is needed for this replay.

The remaining 137 assignments still spend all eight knots
and split the slabs starting at $0$, $2/400$, and $4/400$;
13 have a double slab. Their negative slab starts, counted
with knot multiplicity and in units of $1/400$, are:

| Negative starts | Assignments |
|:--|--:|
| $(-2304)$ | 21 |
| $(-216)$ | 71 |
| $(-2304,-216)$ | 41 |
| $(-2288,-216)$ | 2 |
| $(-322,-216)$ | 2 |

Thus every surviving assignment spends at least one knot
on a negative slab. Neither the signed eight-knot class nor
the separate [six-release class](six-release-support-33.md)
is excluded. These are upper-price survivors, not feasible
laws.

Replay the two stages in order with SageMath 10.9 and
assertions enabled. The radial checker pins the canonical
cross-price export by digest, so the input can be reproduced
without a stored copy of the 155 masks:

```sh
work=$(mktemp -d)
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-refined-frontier-33.py --jobs 6 --write-eight "$work/cross.json" &&
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-eight-knots-radial-33.py "$work/cross.json" --write-eight "$work/radial.json"
```

[radial]: deletion-laws/delete-33-k8-radial-deltas.json

## Five releases: Recombining the fixed linear prices cannot suffice

For each of the seven unpaid release sets there is **one**
profile on which all nine raw linear functionals in the
frontier screen exceed $5\cdot10^{-10}$, **even after
restoring both first caps at frequency zero**. Thus taking
any convex combination or the pointwise minimum of the
nine and maximizing over this relaxation cannot certify
a negative upper bound. Adding nonnegative multiples of
the zero-frequency cap slacks cannot help either. This is
stronger than finding a separate maximizer for each tangent;
it does not rule out new nonzero-frequency cuts or retaining
the quadratic loss.

Use at most three atoms per original finite slab except on
the five released slabs, whose pieces have width $1/6400$.
On the tail use step laws through $48$ and $u=1/\sqrt2$
thereafter. Nominate three atoms per interval using the
`eight-knots` price with three small signed shifts to its
zero-frequency coefficients. Round the atoms to rationals
and mix with the fixed probabilities $(.399,.250,.351)$.
Check **the same profile** under all nine functionals with
ball-enclosed primitive differences. The remote tail has
$A=B=0$ and its mass is included exactly. No upper atom
estimates, interpolation allowances, or floating-point
optimizer claims enter this test. The smallest price is
about $6.36057\cdot10^{-10}$, on $(0,2,4,6,16)/400$.
These are not feasible witnesses: Each has $|V_A(1)|>4$.

```sh
/opt/sage-10.9/bin/python .godel/bob/check-five-release-linear-lower-33.py --jobs 5
```

On $(0,2,4,6,16)/400$, a [checked common witness with the
frequency-one cap](five-release-frequency-one-33.md) shows
that adding this one cap still does not suffice. The
[refitted disk-normal price][disk-price] uses the full
inherited disk family and closes the five-release frontier.
