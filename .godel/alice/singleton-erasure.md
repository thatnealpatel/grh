# Count shared erasures through singleton signature classes

The [fixed-input erasure bound][fixed] prices the passing
class, not the unrestricted complement of the [widened
screen][screen]. Its sharp bins used the whole fixed-input
row width. In fact, with one erasure per actual input, hits
with a repeated erased signature are paid by **unpunctured
pairs**. The remaining hits cost only a subpower number of
partners per actual reference. This rules out the former
near-cap bins as candidates for saturation at either radius.

## Statement and recovery inputs

Keep one actual constructed two-label list in $g=R=j=1$,
with the same retained ordered triples $(v,d,e)$, $d\ne e$,
as in [the fixed-input count][fixed]. The common input
$v$ fixes $c$. Labels and sorted prefixes are the actual
ones; in particular the first label has at most one row
on $(c,d)$. Write the second row at an actual column as

$$cF_2 h_d=dZ_d+q\beta_d,\qquad R_d=Z_d/h_d,$$

so $S=R_d/R_e$. Fix one rational valuation space $B$ of
dimension at most $(\log q)^{1.44}$ and one eligible prime
set $E_v$ per actual input, with $\prod_{p\in E_v}p\le q^r$.
For fixed $0\le r\le 2.110$, in **any subset** of the
retained triples the number of hits $[S]\in B+\mathbb Q^{E_v}$
is at most $q^{\max(A,J(r))+o(1)}$, where

$$C=1.055,\qquad A=\frac{671}{900}C,\qquad
 J(r)=\frac r2+\frac{11}{18}\left(C-\frac r2\right).$$

The error is uniform in the space, the shared erasures,
and the subset. The proof below never assumes that the
pairs used to charge the hits survive the cuts.

**Allow all actual pairs in the unpunctured bound.** On the
same list, for any one eligible valuation space of the
stated dimension, at most $q^{A+o(1)}$ ordered distinct
actual pairs have their $[S]$ in that space, **before** the
reciprocal, radical, or gap-screen pair cuts. To verify the
scope, use the following three codes. Take pivots $P$ and
bin the weights $x,y$ of $(h_d Z_d)_P,(h_e Z_e)_P$ on that
fixed set. Buying both pivot parts at price $.22(x+y)$
and splitting them gives $[S]|_P$, then exact $S$. The
[exact-$S$ recovery][exact] needs only the primitive
actual rows, the residue and real approximation to $e/d$,
the gap width, and the sorted prefixes and first label.
The recovery uses no pair masks, radical cut, or
second-row escape. Indeed the two signed row equations
give $S\equiv e/d\pmod q$ and $S/(e/d)=1+O(q^{-1.110+o(1)})$
before any cuts. The split in the recovery is reduced by
row primitiveness, and its integer bracket is nonzero by
the distinct deterministic output prefixes. The slope
count uses $H_0^2/F_2\le q^{o(1)}$, not a lower bound on
the bracket beyond nonzero. Thus the recovered data give
$(v,d,e)$ at subpower multiplicity.

The other codes first buy an actual reference, say $(v,e)$,
by the [moving row bound][pivot] at price $C-.28y$. It
supplies $c$, $v$, and $R_e$. If $x\le C$ up to bin error,
buy the partner's pivot part at $.22x$ and decode $S$ as
above. Otherwise a divisor $f$ of $(h_d Z_d)_P$ crossing
$2UH_0$ costs at most $.22C$, where $U=q^{.665+o(1)}$
bounds $h_d$ and $H_0=q^{.390+o(1)}$ bounds $|\beta_d|$.
Use the first prime-factor crossing, or an exact-$S$ code
if the product does not cross. Splitting $f=f_h f_Z$ gives
$f_h\mid h_d$ and $f_Z\mid cF_2h_d-q\beta_d$. These
conditions have index $f$ in the two row coordinates, since
$q$ is a unit modulo $f_Z$. The determinant bound $2UH_0$
and positive primitiveness fix $(h_d,\beta_d)$, so the
actual second output gives $d$ by its prefix. Neither this
local decoder nor the moving row bound uses the pair cuts.
The two reference prices are thus at most
$1.22C-.28y$ and $1.22C-.28x$. Average them, and combine
with the first code using weights $11/18$ for the average
and $7/18$ for the first code. This gives $A$ on each bin.
All these prices use the eligible floor
$(2.1\log q)^2/(\log\log q)^4$ and eligible ceiling
$O((\log q)^2)$ as in the cited bounds.

## Separate and charge repeated signatures

Use the same fixed subpower family of binary masks $T$ as
in the [fixed-input count][fixed]. For each hit, a suitable
mask is disjoint from $E_v$ and contains all primes of
$h_d Z_d h_e Z_e$ outside $E_v$. Indeed the total number
of prescribed coordinates is $O(\log q/\log\log q)$ by the
floor, the bounded product for $E_v$, and the polynomial
row heights. Independent binary masks meet any one such
prescription with probability $q^{-o(1)}$; there are at most
$3^N$ prescriptions on the $N=O((\log q)^2)$ eligible
primes, so a union bound yields a fixed family of size
$q^{o(1)}$.

Fix $T$ and keep the inputs with $T\cap E_v=\varnothing$.
At each such input, consider **all actual columns** whose
raw $h_d Z_d$ is supported on $T\cup E_v$. Group these
columns first by the coset of $[R_d]|_T$ modulo $B|_T$,
then within each coset by their full signed signature
$[R_d]|_{T^c}$. Each coset has at most $L=q^{o(1)}$
signatures, uniformly: The latter coordinates are on the
named $E_v$, and both its cardinality and the sum of
absolute valuations are $O(\log q/\log\log q)$. Signed
stars and bars gives the bound. The price is pointwise at
$v$, with no enumeration of $E_v$ across inputs.

A hit covered by this mask stays in one coset. Any pair of
distinct actual columns *within* one signature class of
that coset has $[S]$ in the fixed zero extension of $B|_T$.
Its dimension is at most $\dim B$. Thus the sum over inputs
and cosets of the ordered within-class counts $m(m-1)$ is
at most $q^{A+o(1)}$, by the unpunctured bound. These are
actual pairs on the same list but may have failed retention
or passed the screen.

Two different signature classes of sizes $m,n$ in one
coset give at most $mn$ ordered pairs in that orientation.
Unless both are singleton,

$$mn\le m(m-1)+n(n-1).$$

If $m,n\ge2$ use $m(m-1)\ge m^2/2$ and the same for $n$;
if $n=1<m$ use $m\le m(m-1)$, and swap as needed. Summing
over ordered blocks costs at most $2L$ copies of the
within-class counts, plus the within-class hits themselves.
Therefore all covered hits with at least one nonsingleton
endpoint class cost $q^{A+o(1)}$, even after summing masks.
This accounts for an unequal pair of class sizes without
charging the diagonals of the singleton classes.

## Price the singleton hits on the same bins

Fix the mask and pivots $P$ for $B|_T$. In each remaining
hit both signature classes are singleton, so any endpoint
has at most $L$ such partners at its actual input. Bin the
raw pivot weights $x,y$ of the two columns, and also the
logarithms $u,t$ to base $q$ of the radicals of the signed
supports of $[S]|_{T^c}$ and $[S]|_P$, respectively. In
bounded dyadic bins $u\le r$ and $t\le x+y$, with uniform
$o(1)$ bin errors.

* **Moving code.** Buy the outside radical at $u/2$ by
  the smooth half-power count and the pivot radical at
  $.22t$ by Rankin. Signed valuations on each named support
  cost subpower by the same factor count. The pivot tuple
  fixes $[S]|_T$ in $B|_T$ and the outside data complete
  exact $S$. Global exact recovery pays for the full triple,
  including $v$. This price is $M=u/2+.22t$.
* **Singleton reference code.** Buy the heavier pivot
  column as an actual reference, costing
  $D=C-.28\max(x,y)$ by the [moving row bound][pivot].
  Use both orientations at constant cost. Its actual
  input and coset have at most $L$ singleton partners with
  this mask; no additional paid partner filter is needed.

On the **same bin**, the minimum is at most

$$\frac7{18}M+\frac{11}{18}D
 =J(r)-\frac7{36}(r-u)
      -\frac{77}{900}\bigl(x+y-t+|x-y|\bigr).$$

The deficits are nonnegative up to bin errors. Sum over
the subpower number of bins and masks and include the
repeated-signature charge. This proves the bound. The
singleton code also gives the cap $C$ without a radius
limit, as long as the prescribed erasures have cardinality
$O(\log q/\log\log q)$ uniformly.

**Near the new cap.** For fixed $J(r)>A$, only singleton
bins can have exponent $J(r)-o(1)$. In such a bin the
identity forces $u=r-o(1)$, $t=x+y-o(1)$, and $x-y=o(1)$.
Both $M$ and $D$ must be at least $J(r)-o(1)$, so

$$x,y=\frac{C-r/2}{.72}+o(1).$$

Thus the **pivot** support consumes its raw product up to
$q^{o(1)}$ repetition and cancellation; essentially all
the allowed erasure weight is used in the outside signed
radical. This does not require that the raw erased product
be near squarefree at the new cap. Every former near-cap
bin on the same mask pivots had
$x+y=(61/18)(C-r/2)+o(1)$, so its heavier column has
pivot weight at least $(61/36)(C-r/2)-o(1)$. Including
the repeated-signature branch, all such bins cost at most
$q^{.86285+o(1)}$ at $r=1.300$ and
$q^{.904363888\ldots+o(1)}$ at $r=1.475$. The former
near-cap region, not just its symmetric saddle, can be
ruled out as a source of near-cap hits at either radius.

## Decision on the common complement

At the same widened-screen complement target $1.1354$:

| Radius | New hit upper exponent | Sufficient capture loss exponent | New near-cap pivot weight per endpoint |
|:--|:--|:--|:--|
| $1.300$ | $.897500$ | $.237900$ | $.562500$ |
| $1.475$ | $.931527777\ldots$ | $.203872222\ldots$ | $.440972222\ldots$ |

These are sufficient losses in a **lower** capture fraction
$q^{-a-o(1)}$ on the same population. To repay the increased
price, the larger radius needs a certified relative gain
of $q^{49/1440-o(1)}$ to tie the bound derived with the
smaller radius, up to subpower errors. The exponent is
$.034027777\ldots$. No such gain follows from these upper
bounds. On the same mask pivots, the new small-radius
pivot bin costs at most $.897500$ at the large radius by
the singleton reference code. The large-radius pivot bin
costs at most $.844027777\ldots$ at the small radius by
the moving code, even allowing that radius's full outside
radical. Both estimates include the repeated-signature
charge. Thus a bin saturating either new price cannot
saturate the other on those pivots. This does not compare bins
from different masks or pivots.

The [inherited short-seed ceiling][seed] $r/2+.220$ still
excludes short seeds alone at the small-radius near-target
cap. At the large-radius cap that ceiling is now above the
required number of hits and no longer excludes short seeds.
This is not evidence that any short seeds achieve the cap.

No admissible widened-screen export was located. On one
actual export, with frozen $B$, score both radii on the
same complement and tag seed certificates separately.
For upper diagnostics one may first audit singleton
signature hits on the full actual list for each fixed
separating mask: Repeated-signature hits cannot supply a
near-target count at either new stated loss. The remaining
premise is a uniform lower capture bound or a direct bound
for the unrestricted survivors. No RH or GRH conclusion
and no Alpöge input is used.

Run `python3 .godel/alice/check-singleton-erasure.py` for
exact coefficient, crossover, and radius checks.

[fixed]: fixed-input-erasure.md
[screen]: denominator-pair-gap-regions.md#after-work-spend-the-full-rank-margin-before-testing-the-second-row
[exact]: joint-valuation-escape.md#two-recovery-facts
[pivot]: global-pivot-row-price.md#single-rows-with-moving-and-with-fixed-inputs
[seed]: shared-second-erasure.md
