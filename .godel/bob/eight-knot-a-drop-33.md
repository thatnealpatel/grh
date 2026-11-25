# Delete-33: Price the A drop on the signed eight-knot frontier

The parent target is to exclude every remaining signed
eight-knot law at depth $39/20$ with $M-8/9\ge-10^{-10}$.
The [first-slab quadratic certificate](eight-knot-local-q-33.md)
left 80 upper-price survivors, not 80 feasible laws. All
80 put exactly one real interior knot in
$[l,r]=[-216,-214]/400$. The question here is whether an
attaining law can have $D_A=A_L-A_R\le3/4$ there. A
necessary large positive drop identifies which masks could
be attacked by an **A-sensitive** constraint. It is not
an exclusion without a separate bound on those drops.

## Project onto a whole-slab law

Use the same atom convention, 1,257-knot partition, disks,
quadratic constraint, radial weights and center as the
first-slab certificate. In particular the laws on the
finite pieces are independent probability laws on
$0\le u\le1$, with moments of $X=2u^2-1$, $T_3(X)$ and
$u$; the tail from $29/5$ is arbitrary measurable. Write
$\mathcal L$ for the accepted raw radial tangent score and
$V=V_B-Z$ for the field relative to its center. The accepted
slack identity gives
$$
M-8/9\ \le\ \mathcal L-\sigma Q(V),\qquad Q(V)\ge0.
$$

For $j=A,B$, let $p_j(t)=\int_t^\infty\rho_j(v)\,dv$
be the corresponding `tail_data` primitive before the
minus sign in the atom score $m u-a X-bT_3(X)$. Define
$c_L=p(k)-p(l)$ and $c=p(r)-p(l)$, where $k$ is the split
position. Thus these are the **signed score coefficients**,
not the arguments $a,b$ to the support routine. The mass
primitive is constant on this strictly negative slab. With
$F_i=(A_i,B_i)$ for $i=L,R$, write
$$
\theta=\frac{c_{L,B}}{c_B},\qquad
\delta=c_{L,A}-\frac{c_A}{c_B}c_{L,B}.
$$
Then the exact local contribution is
$$
c_L\cdot F_L+(c-c_L)\cdot F_R
= c\cdot(\theta F_L+(1-\theta)F_R)+\delta D_A.
$$
The checker verifies $\rho_B<0$ on the whole slab, so
$p_B$ increases and $0\le\theta\le1$, with $c_B>0$.
Mixing the *two probability laws* in these proportions
realizes the vector in the first term (with the same
mixture for $U$). Hence that term is covered by the whole-
slab support in the unsplit base; there is no relaxation to
independent choices of $A$ and $B$ in this step. The
mixture is used only in the local linear support: the
quadratic loss and disk feasibility still refer to the
original law.

## Continuous coefficient bounds

The accepted `tail_data` curvature envelope is
$\mathrm{curv}\,E(t)$, where $E(t)=e^{-t/2}$. It bounds
each individual second derivative of the densities (its
constants price the differences of two laws); equivalently
it bounds each individual third derivative of the
primitives on the smooth branches. In `tail_data`, the disk
factor is $e^{-t/2+ixt}$, with second-derivative factor
$|1/2-ix|^2$. The other density factors, after pulling out
$E(t)$, have the form $(1+s_+)e^{-|s|/2}$ and
$s_+^2 e^{-|s|/2}/2$ for translates $s$ of $t$. Their
second derivatives **with** the factor $E(t)$ are zero
for $s<0$ and otherwise have rescaled absolute values
$|s-1|e^{-s/2}\le1$ and
$|1-2s+s^2/2|e^{-s/2}\le1+4/e+8/e^2<4$.
Summing absolute coefficients gives the inherited envelope
(with its factor for differences of laws). The densities
and their first derivatives match across their branch
sites. These sites are center knots shifted by multiples
of $13/25$ or reflected and shifted by the three inherited
$H$ sites, all on the $1/400$ lattice. The checker
checks all 33 endpoint samples for the density on the
$1/6400$ mesh. Linear secant interpolation costs at most
$\mathrm{curv}\,E(l)/(8\cdot6400^2)$ on each cell. The
outward sample upper is below $-0.000397641$ and the
allowance is below $3.084\cdot10^{-8}$, certifying the sign.
All sample enclosures are within
$[-0.000402265,-0.000397641]$.

For $\delta$, whose ratio $c_A/c_B$ is about
$-7.72645\cdot10^{-7}$, use the same sample positions as
the endpoints and midpoints of 16 closed $1/3200$ cells. The
three Bernstein controls are $d_0,2d_{1/2}-(d_0+d_1)/2,d_1$.
They bound the interpolant by convexity of the Bernstein
weights. The interpolation error is at most
$$
\frac{(1+|c_A/c_B|)\mathrm{curv}\,E(l)}
     {3200^3\,72\sqrt3},
$$
since the maximum absolute product of the three distances
to the nodes on a width-$h$ cell is $h^3/(12\sqrt3)$,
and the Lagrange remainder divides by $3!$. The outward
controls are between 0 and $2.094704\cdot10^{-8}$, with
remainder below $2.473\cdot10^{-12}$. The checker verifies
on all cells
$$
-2.5\cdot10^{-12}\ \le\ \delta\ \le\ 2.096\cdot10^{-8}.
$$
For any cap $0\le a\le2$ and $D_A\le a$, the residual is
at most $J(a)=\max(a\,2.096\cdot10^{-8},5\cdot10^{-12})$.
The first term covers $\delta\ge0$; the second covers
$\delta<0$ because $D_A\ge-2$ even when $D_A$ is negative.
In particular $J(3/4)=1.572\cdot10^{-8}$.

## Complement and frontier test

The complement integer $b$ includes the constant, the
entire unsplit finite mesh (including the whole-slab
support at $-216$), and the measurable tail upper from
the $1/400$ cells through 60 with the inherited remote
allowance.
It also includes the increments for every split **other**
than $-216$: direct shared-position one-knot pricing at
$1/6400$ and ordered two-knot pricing at $1/3200$. For
single splits the checker verifies that the sentinel 1
only selects sites and never caps a result. The single
increment is relative to the very same unsplit price
that is added in `original`, so its subtraction cancels
that base term without subtracting an unknown exact
support. The inherited double routine also adds two
interpolation remainders and restores the atom epsilon
in its base subtraction. Each base or increment is
ceiled in exact units of $10^{-16}$ using outward ball
uppers.

The plain calculation discards $\sigma Q(V)$. For the
five $(-2304,-216)$ masks, the stronger calculation
replaces the *plain* $-2304$ increment by the largest of
the accepted paid cell increments. The old payment is
recomputed with the same tangent and unsplit baseline;
its geometric separation checks run on the union of
sites in those five masks. The paid cells jointly price
the local raw contribution at $-2304$ **minus**
$\sigma Q(V)$, relative to the unsplit price. Thus this
replacement charges the quadratic loss exactly once; the
projection at $-216$ uses only raw linear support.

Write $N=10^{16}$ and $T=-1000000$. For a frontier law
with $D_A\le a$ the chain is
$$
T/N\ \le\ M-8/9\ \le\ \mathcal L-\sigma Q(V)
\ \le\ b/N+\delta D_A\ \le\ b/N+J(a)
\ \le\ (b+\lceil NJ(a)\rceil)/N.
$$
Consequently it must have $D_A>a$ if the last integer is
**strictly** less than $T$; equality does not pay. For
$a=3/4$ the ceiling adds exactly $157200000$. If the gap
$g=(T-b)/N$ exceeds $5\cdot10^{-12}$, the negative-$\delta$
branch cannot pay it even without assuming $D_A\le a$.
Then a frontier law must satisfy
$D_A\ge g/(2.096\cdot10^{-8})>0$.

The rounded unsplit base is $-2187294957$. For the five
masks using $-2304$, its plain increment is $274424971$
and its paid increment is $97311793$ in the same units.
The following are maxima over whole groups; each floor
uses the largest $b$ in that group. Slab indices are in
units of $1/400$.

| Negative starts | Masks | Worst plain $b$ | Worst best $b$ | Common floor for $D_A$ (best) |
| --- | ---: | ---: | ---: | ---: |
| $-216$ | 71 | $-161601452$ | $-161601452$ | $40150363/52400000$ |
| $-2304,-216$ | 5 | $-71217256$ | $-248330434$ | $123665217/104800000$ |
| $-2288,-216$ | 2 | $-274454489$ | $-274454489$ | $273454489/209600000$ |
| $-322,-216$ | 2 | $-280686259$ | $-280686259$ | $279686259/209600000$ |

The plain bound forces $D_A>3/4$ on 75 of 80 masks;
for the other five it still forces at least
$8777157/26200000>0.335$. With the first-slab payment,
**all 80 force $D_A>3/4$**, and the common floors are
respectively above $0.76622$, $1.18001$, $1.30464$ and
$1.33438$. No individual mask is excluded by substituting
the unconditional bound $D_A\le2$.

## Flat local B is a genuine obstruction to this raw price

The exact mask with eight single splits at
$[-216,0,2,4,6,8,10,12]/400$ belongs to the **80**. Put each
knot at the original slab midpoint. On the two halves at
$-216$ use $u=1$ then $u=1/2$, i.e. $X=1$ then $X=-1/2$.
Both have $B=T_3(X)=1$, but $D_A=3/2$. These are genuine
atoms, not moment coordinates chosen independently. In
fact, for any $B\in[-1,1]$ take $\alpha=\arccos(B)/3$.
The two roots $\cos\alpha$ and $\cos(\alpha+2\pi/3)$ have
this same $B$ and a gap $\sqrt3\sin(\alpha+\pi/3)\ge3/2$.
Switching between them on either half preserves the entire
$B$ field and hence its disks and $Q$.

On every other finite piece and $1/400$ tail cell through
48, use the dyadic atom retained by the inherited
Bernstein support routine. Its new optional witness return
tracks the endpoint or subdivision midpoint that realizes
at least the stored lower bound `best`. The default upper
calculation is unchanged; `bern_upper - 1e-14` encloses
`best`, **not** an upper in the lower calculation. The
sum uses the outward lower endpoint after adding the fixed
local scores and the tangent constant. Beyond 48 use
$X=0$ (also set $A=B=0$ to the left of the partition),
so both disk moments vanish there and the omitted mass
contribution on $[48,\infty)$ is nonnegative. This is an
admissible law for the relaxed support. Its checked lower
bound over 1,264 finite pieces and 16,880 tail cells is greater
than $1.47577\cdot10^{-8}$, before adding the remote mass. A
correction depending only on the local $B$ drop and zero
at drop zero leaves this positive score unchanged. The
same explicit atoms give normalized $A$-disk modulus
above $1.36308$ at frequency $0.2424456471998$, so the
witness is not disk-feasible. No quadratic fee is
subtracted in this lower bound.

There is a **different**, low-mass example for the caps
and $Q$ alone. Keep the same two atoms on the negative
split and use $X=0$ elsewhere, except that on each first
half of the seven positive split slabs one can use the
symmetric law on $X=\pm1/2$. This makes each midpoint a
genuine change of law while keeping $A=B=0$ off the
negative slab. For normalization $C_t=C/(2\cos(\pi/12))$,
the normalized Fourier sup norms are at most
$E(l)(r-l)/C_t$ and $E(l)(r-l)/C$, each checked below
$1/80$. Since $q\ge|H|$, $Q(V_B)\le2d\|V_B\|_\infty^2<d$.
Concavity of $u=\sqrt{(1+X)/2}$ gives $M\le1/\sqrt2$,
well below the required mass. Thus disks and $Q$ alone
cannot impose $D_A\le3/4$; this example is separate from
the positive raw score witness.

## Replay

Use SageMath 10.9 (Python 3.14.7 in the checked run) with
assertions enabled. From the repository root, this first
runs the small controls alone, then regenerates the canonical
input and runs the full certificate without search scratch:

```sh
work=$(mktemp -d) || exit
export PYTHONDONTWRITEBYTECODE=1
sagepy=/opt/sage-10.9/bin/python
"$sagepy" .godel/bob/check-eight-knots-a-drop-33.py --reference &&
"$sagepy" .godel/bob/check-refined-frontier-33.py --jobs 6 --write-eight "$work/cross.json" &&
"$sagepy" .godel/bob/check-eight-knots-radial-33.py "$work/cross.json" --write-eight "$work/radial.json" &&
"$sagepy" .godel/bob/check-eight-knots-local-q-33.py "$work/radial.json" --write-eight "$work/local-q.json" &&
"$sagepy" .godel/bob/check-eight-knots-a-drop-33.py "$work/local-q.json"
```

The first three producers regenerated 155 cross-price,
137 radial and 80 local-$Q$ masks, respectively. Their
SHA-256 digests were:

| Export | SHA-256 |
| --- | --- |
| `cross.json` | `b198276408fadb7f791d3ef68a16eee27ae1fd1ebc9773276de30bbb684003ed` |
| `radial.json` | `34df5c789255c8c519db79ca76f915eb2461b44e8b60c332f696e7bcb8ea1ef8` |
| `local-q.json` | `b15f16a1fc3662d4187dbbec71ec0cde6a77579b5fa015d34f5397b04ea4e31f` |

The final checker completed with exit status zero in the
assigned workspace on those regenerated inputs. It pins
the last digest and checks mask structure, group counts,
split multiplicities, the 10 double-slab cases, and that
all 80 split $-216$ exactly once. It uses Sage 128-bit
real and complex balls for enclosures and exact rationals
for the mesh, prices after rounding, and thresholds.
At $D_A\le3/4$, the best capped maxima in table order
were $-4401452$, $-91130434$, $-117254489$, and
$-123486259$, each strictly below $T=-1000000$. The
flat-$B$ check reported a raw lower bound above
$1.47577827\cdot10^{-8}$ and a disk modulus above
$1.36308799$.

Next, use an A-sensitive constraint only if it can bound
this signed drop (or lower the frontier score directly)
for laws at the required mass. Repeating a penalty that
only sees the local $B$ drop is not sufficient for the
fixed raw tangent, and caps without the high-mass premise
cannot supply the missing drop bound.
