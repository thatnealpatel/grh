# Charge global pivot parts through the actual rows

The [global three-ratio count][three] leaves open whether one
frozen space captures enough retained ordered triples in the
[maximizing gap-screen complement][screen]. Its proposed test
was a $q^{-.030-o(1)}$ fraction at radius $.530$. We bound the
capacity of a fixed space, and price a different capture test
with more erasure and a smaller required fraction. These are
upper bounds for passes, not occupancy estimates.

Keep the same single constructed list, reciprocal masks,
radical cuts, and notation. Let $B$ be rational of dimension
at most $(\log q)^{1.44}$. The radius $r$ bounds the prime
product of the erased set by $q^r$. Counts include the actual
common complete input. With uniform $o(1)$ errors, the prices
are as follows. Define

$$
\Phi(C,r)=\begin{cases}
 (7C+11\cdot1.1408)/18+7r/36,&r\le 2(.860-C),\\
 .56C+.44\cdot1.250+.28r,&r\ge 2(.860-C).
\end{cases}
$$

| Coefficient type | Passing exponent | Range used here |
|:--|:--|:--|
| $j\ne0$ | $\Phi(.493,r)$ | $0\le r\le 1.105$ |
| $j=0$, $k'\ne0$ | $55/72+7r/36$ | $0\le r\le 1.912$ |
| $j=k'=0$ | $\Phi(.449,r)$ | $0\le r\le 1.193$ |

In the pure denominator branch the old bound $.86128+.28r$
is also available on its original range. At common radius
$.530$ the maximum price is $14879/15000=.9919333\ldots$.
At the upper radii in the table the union costs at most
$q^{3407/3000+o(1)}$, with $3407/3000=1.1356666\ldots$.
In particular the common radius $1.105$ fits the former
selection budget.

## Single rows, with moving and with fixed inputs

Write $F_i m=N+q\delta$, where $(m,N)=(ca,dY)$ in row
one, or $(m,N)=(ch,dZ)$ in row two. Here $m>0$,
$\gcd(m,\delta)=1$, $m\le V_0=q^{1.720+o(1)}$, and
$|\delta|\le H=q^{.390+o(1)}$, by the row size bounds and
primitivity. The sorted prefixes of $F_i m$ and $N$ give
$c,d$. In row two the first label on that actual column
then specifies $v$. Set $A_1=N$ in row one and $A_2=hN$
in row two. For a fixed set $P$ of at most $(\log q)^{1.44}$
eligible primes, columns with $(A_i)_P\ge q^{b-o(1)}$ cost

$$q^{1.055-.28\min(b,2.110)+o(1)}.$$

Take a divisor $f$ first crossing strictly above $2V_0H$
inside $A_i$. Use only its $P$-part if possible. Otherwise
bin and enumerate the full $P$-part at Rankin exponent $.22$,
and enumerate the multiplier needed for the crossing at
smooth exponent $.5$. There is enough product since
$N=q^{2.500+o(1)}$; the crossing overshoots by at most one
prime of size $q^{o(1)}$. This gives the stated price by the
[Rankin and smooth counts][three]. In row two split
$f=f_hf_N$ with $f_h\mid h$, $f_N\mid N$, at divisor cost.
Use $f_h=1$ in row one. Do not enumerate $h$ first. The
lattice conditions

$$m\equiv0\pmod{f_h},\qquad F_i m-q\delta\equiv0\pmod{f_N}$$

have index $f_hf_N$: Substitute $m=f_h t$ and use that $q$
is invertible modulo $f_N$. This also works when the two
filters have common primes. Two vectors in the box have
determinant at most $2V_0H$ and divisible by the index,
so positivity and primitivity force equality. Recover the
actual column from that vector. In particular $h\mid ch$
allows the filter to use the cofactor even when $c$ varies.

At **fixed actual $v$**, first-row columns with
$(dY)_P\ge q^{b-o(1)}$ instead cost
$q^{.195-.28\min(b,.390)+o(1)}$. Use the same crossing
argument at width $2H$ within $dY$: If $f\mid dY$ then
$v-q\alpha\equiv0\pmod f$ fixes the signed $\alpha$,
and hence $dY$ and its prefix. In particular every column
has at most $q^{.195+o(1)}$ partners at its own $v$.

For a given $P$, suppose the first-row supported product
weights at the two endpoints sum to at least $t-o(1)$, where
$0\le t\le2.110$. Bin the two weights and fix their order,
at subpower cost. Count the heavier endpoint globally, then
the lighter at its actual $v$. If $b_1\ge b_2$ are the weights,
this gives price $1.250-.28(\min(b_1,2.110)+\min(b_2,.390))$.
The sum of minima is at least $\min(t,t/2+.390)-o(1)$:
If $b_1\ge 2.110$ it already suffices; otherwise use
$b_1+b_2$ when $b_2\le .390$, and $b_1\ge t/2-o(1)$ when
$b_2>.390$. Thus we can charge the pair at

$$L(t)=\max(1.250-.28t,\ 1.1408-.14t).$$

The lighter endpoint must be counted conditionally at the
actual input. Using its global count, or dropping its pivot
condition entirely, does not give this price.

## Apply these prices before recovering a monomial

**First-output coefficient nonzero.** Use the [isolation
proof][three], with selected signed support of weight
$u=1.904-r-o(1)$ and its fixed subpower family of binary
masks. For each mask use pivots $P$ of the projected
space. Bin the selected radical weight $t$ on $P$. The
selected pivot data cost $.22t$, including signs and
valuations at subpower on the resulting named support.
Interpolation recovers the signed filter of weight $u$
in $W=dY/(eY_0)$. Extension to the $2.890$ divided
determinant width, then exact $W$ recovery, give price
$.493+r/2+.22t$. The raw first-output products together
have pivot weight at least $t-o(1)$ since each selected
pivot prime divides the product at its own endpoint. Thus
$L(t)$ is a second price on the same bin, without erasure
enumeration. Take their minimum before summing masks.

**Pure denominator.** Use base pivots $P$ of $B$ and let
$t$ be the height exponent of $D_P$. Enumerate $D_P$ at
$.22t$, the erased set at $r/2$, and record its added
pivot data at subpower. As in the [original pure branch][three],
this determines $D$. Its smooth gcd costs at most $.059$
and the fixed ordered-denominator pair costs at most $.390$
for all actual inputs. This gives price $.449+r/2+.22t$.
The full first-row supported weights sum to at least
$t-o(1)$, since $h(D_P)\le(dY)_P(eY_0)_P$. Use $L(t)$
again without any gcd or erasure enumeration.

For each of these two branches, the increasing line
$C+r/2+.22t$ crosses the decreasing $L(t)$ at a positive
$t\le2.110$ throughout the stated range. For $t\ge .780$
it crosses the second line of $L$ at
$t=(1.1408-C-r/2)/.36$; otherwise it crosses the first at
$t=(1.250-C-r/2)/.50$. The breakpoint radius is
$2(.860-C)$. For the first branch one also has
$t\le 1.904-r$ at the intersection. The maximum of the
minimum is at most the crossing value $\Phi(C,r)$.

**Second-output coefficient nonzero, first zero.** Take
base pivots $P$ of $B$ and bin the height of the raw product
$(hdZ)_P(keZ_0)_P$ at $q^{y+o(1)}$. Enumerate it at $.22y$
and split at divisor cost into the $P$-parts of $h,d,Z,k,e,Z_0$.
These give $D_P=d_P/e_P$ and $S_P=k_P Z_P/(h_P(Z_0)_P)$
without a cancellation bound. Choose the erased set at
$r/2$, and complete the base pivots deterministically in
the coordinate-extended space. Name the actual valuations
on the added pivots. Those primes are fixed by $B$ and
the already chosen erased set. Their number and joint
multiplicity in the raw factors are both
$O(\log q/\log\log q)$, so the valuation code costs subpower.
The [row-basis code and uniform exact monomial recovery][three]
now give price $.22y+r/2$ for a relation with $k'\ne0$.

Alternatively one of the two raw second-row products has
pivot weight at least $y/2-o(1)$. Use the moving-input
one-row bound and the unconditional fixed-input partner
cap, at $1.250-.28\min(y/2,2.110)$. Below saturation this
meets the first price at $y=(1.250-r/2)/.36$, in $[0,4.220]$
throughout the stated range. Above saturation the one-row
price is $.6592$, smaller than the intersection value
$55/72+7r/36$. The alternative price does not pay for an
erasure, a cancellation product, or a second congruence
from the opposite row.

## Capacity and the remaining test

Write $C_{\rm off}$ for the gap-screen complement count.
The bounds apply to its hits even when $B$ is chosen from
the list. The old $.530$ test can attain a $q^{-.030-o(1)}$
fraction only if $C_{\rm off}\le q^{1.0219333\ldots+o(1)}$.
This is a capacity obstruction **conditional on size**.
It does not exhibit a large list or logically rule out
proving the old target by contradiction.

At radii $(.658,1.300,.746)$ all three prices are below
$1.0170$. A $q^{-.1185-o(1)}$ fraction in one frozen space,
or a full cover by at most $q^{.1185+o(1)}$ such spaces,
would suffice for $C_{\rm off}\le q^{1.1355+o(1)}$. These
are separate sufficient conditions, and neither follows
from the passing counts.

There is a stronger exclusion for short seed certificates.
Freeze any collection of at most $(\log q)^{1.44}$ seed
triples, adjoining all three directions of each. If a
witness uses at most $t_0=\lfloor .50\log q/\log\log q\rfloor$
seeds, the chosen subspan uses $O(\log q/\log\log q)$ pivots.
The raw pivot data on named primes then cost only subpower.
For $n$ frozen seeds, the binomial bound on subsets of size
at most $t_0$ costs $q^{.220+o(1)}$ (if $n<t_0$, all subsets
cost subpower). At common radius $.530$ the prices for one
such span are $.758$ (isolation and extension for $W$),
$.265$ (exact monomial), and $.714$ (exact $D$, gcd and
fixed-pair input fiber). Thus all short witnesses together
cost $q^{.978+o(1)}$ hits. In particular bounded-size
identities, including triangle identities at one complete
input, cannot supply the old fraction unless
$C_{\rm off}\le q^{1.008+o(1)}$. This does not exclude longer
certificates or spaces not described by seed triples.

A positive test is to use radius $1.300$ on the **actual
complement**. For one frozen global $B$ and one erasure
per input, color the endpoint columns by cosets of $[Z/h]$
in the projected quotient by $B$. Each monochromatic
retained ordered edge in the complement is a pure $S$ hit.
An expected count of nonseed monochromatic edges at least
$q^{-.1185-o(1)}C_{\rm off}$ for a distribution of these
choices would suffice. Short seed witnesses hit at most
$q^{1.300/2+.220+o(1)}=q^{.870+o(1)}$ such edges, so they
cannot meet the fraction unless $C_{\rm off}\le q^{.9885+o(1)}$.
An energy bound on all pairs that does not control which
edges survive the complement does not prove the needed
lower bound. The [shared-erasure refinement][shared] lowers
the passing price when the erasure is fixed per input and
reprices this test at larger radius. No admissible census,
economical cover, or unrestricted complement estimate is
supplied here.

Check the intersections, radii, and budgets with
`python3 .godel/alice/check-global-pivot-row-price.py`.

[screen]: denominator-pair-gap-regions.md#after-work-spend-the-full-rank-margin-before-testing-the-second-row
[three]: global-three-ratio.md
[shared]: shared-second-erasure.md
