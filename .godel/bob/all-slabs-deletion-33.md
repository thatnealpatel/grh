# An all-slab price for delete-33 at depth 39/20

**Scope.** At $c=39/20$, keep $A=B=0$ to the left of $-144/25$,
as realized by the reference convention $X=0$ there. Allow an
independent arbitrary law on $0\le u\le1$ on each of the 494
negative and 762 nonnegative finite slabs of the
[1,257-knot reference](deletion-laws/delete-33-tail-baseline.txt).
The laws are constant within those slabs; the knots are unchanged.
Allow arbitrary measurable laws on $[29/5,\infty)$, with no variation
bound or fixed tail moments. The two unfolded first caps on $A,B$ and
the three simultaneous second replies at $3t$ are the ones in the
[joint price](joint-tail-deletion-33.md#joint-price). This is not an
all-real or unrestricted three-versus-four test.

## Upper price

Use $X(u)=2u^2-1$, $T(X)=4X^3-3X$, $(A,B,U)=\mathbb E(X,T(X),u)$,
and $M=\int_0^\infty ze^{-z}U(z)\,dz$. With the
[serialized cut list](deletion-laws/delete-33-all-slabs-dual.json),
apply (1)–(2) of the joint price. Each original finite slab is
priced by maximizing its joint degree-six score on the full atom
interval. The last reference slab starts at $29/5$; omit its
constant-law price and use `continuous_tail` instead. This integrates
a bound on the pointwise atom maximum from $29/5$ to $48$, then adds
the uniform infinite remainder past $48$. In particular the separate
`price` diagnostic for a remote cutoff of $40$ is **not** added.

For an upper bound $\eta$ on the replacement fraction in **each**
pre-tail slab, with $0\le\eta\le1$, weight its gain by $\eta$ and
leave the negative and measurable-tail gains unchanged. This uses
nothing about how the replacement fractions or laws are chosen.
The resulting computed upper price has the form
$P_{\rm full}-(1-\eta)G_{\rm pre}$, where $G_{\rm pre}$ is the sum
of the atom prices on $[0,29/5)$. More generally, a law with
nonnegative surplus must earn at least $G_{\rm pre}-P_{\rm full}$
in actual pre-tail score in (1), even if all the negative and
measurable-tail gains are granted. This is a score requirement,
not a constraint on some norm of the law change.

## Nomination versus replay

On the coarse finite-tail discretization (1,884 finite slabs in
all, with tail through $48$), the retained cuts start near
$7.046\cdot10^{-8}$ in double precision. Reweighting those same
rows reached about $7.010\cdot10^{-8}$; it did not approach zero.
Searches with distinct frequencies and refitted phases did better.
The epigraph LP used sampled atoms, exchanged them against the
stationary points of the slab score, and used its row marginals to
nominate new first directions on a frequency grid. The second row
used the retained direction $(.7264553101249,.9816283566088,1)$.
The search used SciPy 1.18.1/HiGHS 1.12.0 (double precision),
increments scaled by $10^8$ or $2\cdot10^8$, feasibility tolerances
$10^{-9}$, and matrix entries below $10^{-11}$ or $10^{-12}$
dropped. A late finite LP objective was about $-1.03\cdot10^{-9}$,
but its proposal repriced at $+4.66\cdot10^{-9}$ even on its own
finite slabs. Neither is a global bound. Same-frequency first directions
were merged by adding their complex multiplier vectors. Dropping
multipliers below $2\cdot10^{-9}$ in a separate run changed one
roughly $2.5\cdot10^{-8}$ internal objective to a serialized reprice
above $10^{-7}$; that pruned list is not used.

The replay reads the JSON decimals without conversion to binary
floating point and checks signs and row types. The existing pricing
routines normalize the first directions, check the global degree-192
second majorant, and use 128-bit Sage balls. Bernstein subdivision
prices all atoms, not just the exchanged sites. The pointwise tail
uses endpoint interpolation with the uniform second-derivative
envelope, not an assumption that the law itself is continuous. The
reference's previously checked first caps and exact three-site
completion can be replayed with `check-tail-deletion-33.py
--full-negative`; they are not rechecked by the new wrapper.

## Certified bounds

The older full-negative list replayed with all finite slabs free gave
$P_{\rm full}<7.814\cdot10^{-8}$ (tail mesh $1/2400$). The new
164-row list has 106 first cuts on $A$, 57 on $B$, and one second
tangent. Its serialized double-precision reprice was
$+2.7694\cdot10^{-9}$ on 4,396 finite slabs. The full rigorous
upper price is different: **$M-8/9 < 5.849\cdot10^{-9}$**. Under
the additional restriction that no pre-tail slab replaces more
than $39/40$ of its reference law, the certified upper bound is
**$M-8/9 < -1.0828\cdot10^{-9}$**, with the negative slabs
and the measurable tail still fully free.

Run from the repository root with assertions enabled (Sage 10.9):

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python \
  .godel/bob/check-all-slabs-deletion-33.py \
  --den 4800 --upper 6.5e-9 --check-pre 39/40 0
```

The same calculation in the assigned workspace passed, with the
following enclosures of upper prices and their components:

```text
Reference surplus  [-6.607891626346287219522721480e-7 +/- 2.91e-35]
Cut slack           [1.2716300153964087098754917e-7 +/- 6.47e-33]
Negative gain       [1.37123636400748329754105e-7 +/- 1.94e-31]
Pre-tail gain       [2.77237611881466717446519e-7 +/- 1.99e-31]
Tail trapezoid      [1.2349805605199380451195374491e-7 +/- 5.69e-36]
Tail chord error    [1.481651172463701902888516400734230e-9 +/- 6.02e-43]
Beyond 48           [1.332557324895265706639732813660635e-10 +/- 5.58e-44]
Full                [5.848050144174229221407e-9 +/- 3.09e-31]
39/40 pre-tail      [-1.082890152862438714756e-9 +/- 3.39e-31]
```

From the displayed balls, $P_{\rm full}-G_{\rm pre}/47$ has a
strict upper endpoint below $-5\cdot10^{-11}$, so even the larger
uniform replacement cap $46/47$ gives an exclusion. Also
$G_{\rm pre}-P_{\rm full}>2.7138\cdot10^{-7}$ is a necessary
actual pre-tail score for any nonnegative-surplus contender.

Inputs, pinned to the reference and checker at `e8dc2290`:

```text
SHA-256
reference 7be0449af83f2b264894d0b0074108139ada0badc0c34a26edc6731d81baaa5c
cut list  c42c34963cd2bdd081bdf9e0a2d004e4dc81211a7776472aaaa7d02b8bbfde11
```

**Decision.** The sign closes only with the stated replacement
cap. The positive full upper price neither produces a contender
nor excludes full independent replacement; the search is not an
infeasibility result. For a full refit on these same knots, use
the necessary pre-tail score above and test the original quadratic
second constraint, not just the retained tangent. Do not transfer
this price to a changed left cutoff or movable original knots.

## The quadratic budget rules out damping the fitted third field

The full price has not spent the curvature discarded by its single
second tangent. Write $V=V_B$, $V_*=V_{B_*}$, and $\sigma=$
$0.000703488828860649$ for that cut's multiplier. Keeping the same
price on every slab and the measurable tail gives the stronger bound

$$M-8/9+\sigma Q(V-V_*)\le P_{\rm full}.$$

Indeed $Q(V)=Q(V_*)+2\mathcal B(V_*,V-V_*)+Q(V-V_*)\le d$,
so one subtracts $Q(V-V_*)$ from the right-hand side of the tangent
inequality. The remaining (linear) integrand and all its upper
prices are unchanged. In particular **every** feasible contender of
nonnegative surplus must satisfy $Q(V-V_*)<8.315\cdot10^{-6}$.
This bounds the difference, not $Q(V)$, and does not assert that
arbitrary fields in the quadratic budget admit a second completion.

This already rules out a natural repair of the [early-score
refit](early-refit-deletion-33.md). Take its rational profile $B_1$
and allow $B=B_*+\theta(B_1-B_*)$ with any constant real $\theta$.
Allow *all* changes of $A$ and $U$ compatible with this $B$; do not
require them to follow the same interpolation. Since
$Q(V_{B_1}-V_*)>0.428$, homogeneity forces $|\theta|<0.00441$.
On $[24,30]$, however, $B_*<-0.819$ and $|B_1-B_*|\le2$, so
$B<-0.810$ throughout. This contradicts the necessary excursion
$B>-0.6828965$ on positive measure proved by the independent
remote-band price. Thus **no refit anywhere on this third-field
line can work**, even with the first field completely refitted.
The two necessary conditions do not exclude independently moving
this band. In fact, restore $B=B_*$ off $[24,30]$ and allow any
law on the band. The integral formula for the field gives
$\|V-V_*\|_\infty\le4(e^{-12}-e^{-15})/C<1.954\cdot10^{-5}$,
since $|B-B_*|\le2$. As $\mu$ has mass one and
$q+|H|\le2\sum_j|\lambda_j|+2\cdot10^{-7}$ by the checked Laurent
residual, **every** such change has $Q(V-V_*)<2.069\cdot10^{-9}$.
For example, the atom $u=1$ meets the required joint excursion on
the whole band at this small curvature cost. This example does not
certify the signed score, the first caps, or the original $Q(V)$
inequality. The cross term with other profile changes must be
retained in a combined fit. Release this band independently rather
than using one damping parameter for the whole line.

## Full-release exclusion just below the requested depth

Use exactly the same knots, left cutoff, measurable tail, and
unfolded constraints at $0\le c'\le 1.949999962$. In coordinates
normalized at $c_0=39/20$, the first caps now have radius
$r=\cosh(c')/\cosh(c_0)$, since both $C$ and $C_t$ scale with
$\cosh c$. The second inequality at $c'$ becomes $Q(V)\le r^2 d$
by homogeneity, so certainly the old second tangent is still
necessary. Tighten just the first right-hand sides from $1$ to $r$.
No price density or maximization changes. Summing the exact decimal
first multipliers gives $W=0.1608365374660396137275050206$.
At the largest $c'$ in the range, $r<0.9999999635078640$, hence

$$M-8/9 < 5.849\cdot10^{-9}-(1-r)W < -2.02\cdot10^{-11}.$$

For reproducibility, sum the last column of the length-five rows
as decimal rationals, and evaluate the cosh ratio with 128-bit
Sage `RealBallField` at the two decimal rational depths. The
exclusion is for **full** independent replacement on the original
slabs; it neither reaches $39/20$ nor gives an exclusion for
the unrestricted all-real comparison.
