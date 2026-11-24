# Spend shared second-output erasure in the fixed-input row

The [shared-erasure count][shared] fixes an actual reference
before counting its partners. It no longer pays to name the
shared erasure at that reference, but it does not use erased
prime factors to narrow the partner row. Those factors can
supply part of a determinant crossing at the **fixed-input**
width. This changes the passing-price obstruction to the
[paired capture test][paired], not the available capture lower
bound.

## Statement and codes

Keep the same actual two-label list, cuts, and ordered triples
as in [the shared count][shared]. Thus

$$v=cF_1a=dY+q\alpha=eY_0+q\alpha_0,\qquad
cF_2h=dZ+q\beta,\qquad cF_2k=eZ_0+q\beta_0,$$

and $S=kZ/(hZ_0)$. Prescribe one rational valuation space $B$
of dimension at most $(\log q)^{1.44}$ for the list, and one
set $E_v$ of eligible primes per actual complete input, with
$\prod_{p\in E_v}p\le q^r$. For fixed $0\le r\le 2.110$, in
any subset of the retained ordered triples the number with
$[S]\in B+\mathbb Q^{E_v}$ is at most $q^{H(r)+o(1)}$, where

$$ C=1.055,\qquad H(r)=r/2+\frac{671}{900}(C-r/2). $$

The estimate is uniform in the choices, including choices
using the entire list or its screen. It needs the same $E_v$
in both reference orientations. It does not cover erasures
optimized separately per edge.

**Separate the erased coordinates.** Fix a family of
$q^{o(1)}$ masks $T$ on the eligible primes so that for each
triple and $E_v$ some $T$ contains the support of $hkZZ_0$
outside $E_v$, and is disjoint from $E_v$. In fact it suffices
to accommodate all disjoint prescriptions with total size
$K_0=O(\log q/\log\log q)$, by the eligible floor
$(2.1\log q)^2/(\log\log q)^4$, the polynomial product
heights, and the bound on $E_v$. In a universe of $N$
eligible primes a random binary mask fits any such
prescription with probability at least $2^{-K_0}$. At most
$3^N$ prescriptions exist, so $\lceil 2^{K_0}(N\log 3+1)\rceil$
independent masks give a good family with positive
probability. Here $N=O((\log q)^2)$ by the eligible ceiling.
This chooses the family before the inputs and their erasures.

Fix a mask and take pivot primes $P\subset T$ on which the
projection $B|_T$ is injective. On occupied codes, $[S]|_T$
belongs to $B|_T$, so its $P$-values determine its $T$-values.
Bin dyadically the $P$-parts of $hZ,kZ_0$ at exponents $x,y$,
their full $E_v$-parts at $a_h,a_k$, and the radical of the
support of $[S]$ outside $T$ at $u$. That support lies in
$E_v$, and every prime in it divides $hkZZ_0$. Thus, up to
uniform $o(1)$ bin errors,

$$ 0\le x,y\le 2C,\qquad 0\le u\le r,\qquad u\le a_h+a_k. $$

There are subpower many bins and masks. For a named prime
set of size $O(\log q/\log\log q)$ the bounded-height data
on it cost subpower by stars and bars (and signs), since the
sum of absolute valuations has this same bound. As in the
[pivot count][pivot], a $P$-supported product of bounded
height exponent $w$ costs $.22w$ by Rankin at the stated
prime floor and $|P|\le(\log q)^{1.44}$. For a product on
all eligible primes use the smooth price $w/2$ at the stated
ceiling. Prices in this note are exponents, up to $o(1)$.

**Moving code.** Name the radical outside $T$ at price
$u/2$, and the signed valuations there at subpower cost.
Name the two $P$-products and split each at divisor cost;
this specifies the pivot values of $[S]$. Interpolation
and the outside data give exact $S$, which has subpower
[global actual-triple fibers][exact]. The price is

$$ M=u/2+.22(x+y). $$

There is no sum over the rest of $E_v$ or over inputs in
this code.

**Fix an actual reference.** Counting the reference column
$(c,e)$ by the [moving-input row sieve][pivot] costs
$C-.28y$, since $(keZ_0)_P\ge(kZ_0)_P$. Its actual first
label supplies $v$ and hence the prescribed $E_v$; it also
supplies the actual second row and therefore its pivot
values. With $E_v$ now named, the valuations of $[S]$
outside $T$ cost subpower. As in the moving code, buying
$(hZ)_P$ and its split at $.22x$ then gives exact $S$ and
subpower multiplicity, including at this reference.

Alternatively, buy a filter before enumerating the second
row. Let $U=q^{.665+o(1)}$ be the uniform upper bound for
$h$, and $H_0=q^{.390+o(1)}$ the gap bound. If the part of
$hZ$ on $E_v\cup P$ exceeds $2UH_0$, take a divisor $f$ of
that part crossing strictly above $2UH_0$, taking factors
from $E_v$ first. If the $E_v$-part already exceeds the
threshold, take only a divisor on $E_v$. Otherwise take its
full $E_v$-part and add a first crossing on $P$. The last
prime overshoots by at most the eligible ceiling, including
when factors have multiplicity. The named $E_v$-part costs
subpower; the $P$-multiplier costs at most $.22(C-a_h)_+$.
Split $f=f_h f_Z$ with $f_h\mid h$, $f_Z\mid Z$, at divisor
cost. In particular $f_Z\mid dZ$. The resulting conditions
on the unknown primitive row vector $(h,\beta)$ are

$$ f_h\mid h,\qquad cF_2h-q\beta\equiv0\pmod{f_Z}. $$

Their lattice has index $f_h f_Z$: Substitute $h=f_h t$,
then solve for $\beta$ modulo $f_Z$, using $q\nmid f_Z$.
The index formula does not need coprimality of the two
filters. A nonzero determinant between vectors in the box
would be a multiple of that index but have size at most
$2UH_0$. Primitive vectors with $h>0$ on the same line
coincide; the primitiveness follows from the actual row
(even $(ch,\beta)$ is primitive in the [row sieve][pivot]).
The recovered vector and the **known** $c$ give the full
output $dZ=cF_2h-q\beta$, whose sorted prefix gives $d$.
The reference and actual $v$ therefore give the whole
triple. No unknown factor of the row is charged without
either recovering it or using this prefix rule.

If the $E_v\cup P$-part does not cross, disjointness implies
$x+a_h\le C+o(1)$, so the exact-$S$ code costs at most
$.22(C-a_h)_++o(1)$ at the reference. If it does cross,
both codes are available. Combining the alternatives and
then reversing the orientation gives two more global
prices on the same bin:

$$
F_e=C-.28y+.22\min(x,(C-a_h)_+),\qquad
F_d=C-.28x+.22\min(y,(C-a_k)_+).
$$

Both count actual references first, not hypothetical
factorizations of the erasure. In particular, fixing a
reference of just one orientation would not justify
averaging these prices.

## Optimize before summing

If $a_h,a_k\le C$, the average of the two fixed prices is
at most $1.22C-.11u-.14(x+y)$. Combine this upper bound
with $M$, giving $M$ weight $7/18$ and the other bound
$11/18$. The result is $u/2+(671/900)(C-u/2)$.

If $a_h>C$, use $M$, $C-.28y$, and $C-.28x+.22y$,
respectively, with weights $(196,275,154)/625$. The
combined price is $u/2+(429/625)(C-u/2)$. If $a_k>C$,
swap the roles. The latter bound is no worse since
$u\le 2C$ and $429/625<671/900$; bin endpoints at these
thresholds can be treated with uniform $o(1)$ errors.
The first bound increases with $u$, and $u\le r$. Sum all
bins and masks to obtain $H(r)$.

**Necessary near-cap conditions.** For fixed $r<2C$,
the asymmetric case has a fixed gap below $H(r)$. In a
bin reaching $H(r)-o(1)$, the positive weights in the
first combination force its slack to vanish. In particular,

$$ u=r-o(1),\qquad a_h+a_k=u+o(1),\qquad
x+y=\frac{61}{18}(C-r/2)+o(1),\qquad
.28(x-y)=.22(a_h-a_k)+o(1),\qquad
x+a_h,\ y+a_k\ge C-o(1).
$$

The balance identity equates the two fixed prices after
replacing their local terms by $.22(C-a_h)$ and
$.22(C-a_k)$, respectively. The last inequalities are
where this replacement has vanishing slack. These are
conditions on the mask that encodes the bin, not the old
base pivots. In particular the raw erased product must be
almost fully accounted for by the squarefree erased
support of $S$; repetitions and cancellations contribute
only $q^{o(1)}$ to the difference at saturation. The
symmetric algebraic saddles $a_h=a_k=r/2$ and
$x=y=(61/36)(C-r/2)$ have pivot weights $.68625$ and
$.5379861\ldots$ at the two radii, respectively.
They are not asserted to occur in actual data.

## Decision at the same complement target

Use $1.1354$ as the final target for the same maximizing
screen complement at both radii. A uniform lower capture
fraction $q^{-a-o(1)}$ suffices for $a\le 1.1354-H(r)$.

| Radius | Upper hit exponent $H(r)$ | Sufficient loss exponent $a$ |
|:--|:--|:--|
| $1.300$ | $.95195$ | $.18345$ |
| $1.475$ | $.974213888\ldots$ | $.161186111\ldots$ |

Thus the larger radius now needs a certified gain of
$q^{1603/72000}$, about $q^{.022264}$, to tie the small one
in this ledger (previously $q^{.0105}$). Do not select it
without evidence of such a gain on the same surviving
population. The inherited loss exponent $.1185$ would
already imply complement exponents $1.07045$ and
$1.092713888\ldots$, respectively. Relax the *required
capture*, not the radius by default. At a complement near
the target, even the weaker sufficient fractions still
cannot come solely from the [short-seed certificates][shared]:
Their upper exponents $.870$ and $.9575$ lie below both
new near-target hit requirements.

The next discriminating test is the paired shared-erasure
score on actual retained off-screen edges, with the revised
thresholds and the same frozen $B$. No such census is
supplied here. Without it, one arithmetic alternative is
to test whether the near-squarefree erased product and
pivot-weight conditions above can coexist on the signed
rows at the two radii. The conditions alone give no
occupancy and no unrestricted bound for the complement.
The [audit replay][audit] records which data complete each
counting code and why the review prompt was left unchanged.
No Alpöge input is used.

Run `python3 .godel/alice/check-fixed-input-erasure.py` to
verify the price combinations, symmetric saddle arithmetic,
and capture ledger.

[shared]: shared-second-erasure.md
[paired]: shared-erasure-radius-decision.md#next-worker-one-paired-gate-not-two-censuses
[pivot]: global-pivot-row-price.md#single-rows-with-moving-and-with-fixed-inputs
[exact]: joint-valuation-escape.md#two-recovery-facts
[audit]: fixed-input-audit-decision.md
