# Project one endpoint of a shared-erasure hit

The [input-first count][input] leaves the unrestricted
$1.1354$ widened-screen complement open. It treats the
nonerased valuations of $S$ only through their radical on
the pivots. A fixed subpower family of extra masks makes
some of the remaining **full product height** available
as an actual moving-row divisor. This lowers the large
radius price on a specified height stratum. The price
applies to any subset of that stratum, in particular to the
off-screen triples there. It does not assume a capture
fraction or pointwise occupancy.

## Statement

Use the same single actual two-label list, retained
ordered triples $(v,d,e)$, $d\ne e$, one frozen rational
valuation space $B$ of dimension at most $(\log q)^{1.44}$,
and one eligible erasure $E_v$ per actual $v$ as in the
[input-first count][input]. Write the actual rows as

$$v=cF_1a=dY+q\alpha=eY_0+q\alpha_0,\qquad
 cF_2h=dZ+q\beta,\qquad cF_2k=eZ_0+q\beta_0,$$

and put $S=kZ/(hZ_0)$. In particular the signed second-row
gaps satisfy $|\beta|,|\beta_0|\le H_0=q^{.390+o(1)}$,
and the actual column prefixes $d,e$ and the cofactors
$h,k,Z,Z_0$ are all eligible-prime products by the [list
construction][list]. Let $\mathcal H(S)$ be its reduced
numerator times denominator. On any subset on which
$\mathcal H(S)\ge q^{L-o(1)}$ uniformly, the count of hits
$[S]\in B+\mathbb Q^{E_v}$ has the following upper exponents
(with uniform $o(1)$ errors):

| Height floor $L$ | $r=1.300$ | $r=1.475$ |
|---:|---:|---:|
| $2.430$ | $.897500$ | $.926088$ |
| $2.654$ | $.897500$ | $.9122896$ |

Here $\prod_{p\in E_v}p\le q^r$. The result at $1.300$
uses the inherited estimate without a height condition.
The large-radius prices are also valid for smaller radii
on the indicated strata. The theorem for $L=2.654$ does
not presume that the original retained cuts enforce this
height floor.

## The extra mask names a divisor, not a row

Fix an original separating mask $T$ of the [singleton
count][single], disjoint from $E_v$ at covered inputs and
containing both raw supports outside $E_v$. The original
coset and erased-signature partition stays on $T$. The
hits with at least one nonsingleton class cost
$q^{A+o(1)}$, where $A=(671/900)C$ and $C=1.055$. Among
hits with two singleton classes, an actual endpoint at
its actual $v$ has only $q^{o(1)}$ partners, in either
orientation, on this original mask.

Let $b$ be the larger weight $\log_q$ of the two full
raw $E_v$-parts of $hZ,kZ_0$. The erased part of
$\mathcal H(S)$ has weight at most $2b$. On each outside
prime, give its absolute valuation in $S$ to the two
endpoints in nonnegative integer shares, each bounded by
the corresponding exponent in $hZ$ or $kZ_0$. Such shares
exist since the absolute valuation is at most the sum of
the raw exponents. Choose the endpoint whose share has
larger weight $w$, and record which endpoint it is. Then

$$ w\ge L/2-b-o(1). $$

Choose a second mask $T'\subset T$ whose intersection with
$\operatorname{supp}([S]|_T)$ is **exactly** the support of
this endpoint's share. It may contain other coordinates
where $[S]$ is zero. The two disjoint prescriptions, the
included and excluded nonzero coordinates, total at most
$K_0=O(\log q/\log\log q)$ primes: The raw heights are
polynomial, and the eligible prime floor is
$(2.1\log q)^2/(\log\log q)^4$. A random binary mask meets
any prescription with probability at least $2^{-K_0}$.
There are at most $3^N$ prescriptions for
$N=O((\log q)^2)$ eligible primes, by the eligible ceiling
$O((\log q)^2)$. A union bound, as for $T$, gives one
$q^{o(1)}$-size family, fixed before the inputs and shares;
intersect its masks with $T$. In particular this step does
not enumerate either endpoint's actual support.

For each fixed $T,T'$, choose coordinate pivots $Q$ of
$B|_{T'}$, and extend them to pivots $P$ of $B|_T$.
The coordinate forms on $Q$ are independent on $B|_T$
because the projection to $B|_{T'}$ is onto. All price
comparisons below use this same $P$, fixed after choosing
the two masks. Let $x,y$ be the weights of the full raw
$P$-parts of $hZ,kZ_0$, respectively, and $m=\max(x,y)$.
Let $t,u$ be the signed radical weights of $S$ on $P$
and off $T$, respectively. Thus $t\le x+y$ and $u\le r$.
All weights, including $b,w$, may be put in dyadic bins;
there are $q^{o(1)}$ choices and the errors are $o(1)$.

Every nonzero $Q$-coordinate of $[S]$ is in the share
support and hence in the selected endpoint's raw
$P$-part. Buy its radical at exponent at most $.22m$ by
[restricted Rankin][pivot] on at most $(\log q)^{1.44}$
fixed eligible coordinates. The signed valuations on the
named support cost subpower: Their total multiplicity
and support size are $O(\log q/\log\log q)$. These data
determine $[S]|_{T'}$ by interpolation on $Q$. Its nonzero
support is exactly the share support, so name the shares
and split them into the selected endpoint's two raw
factors at subpower cost, again by the same multiplicity
bound. This gives a divisor $f_0$ of $hZ$ (or $kZ_0$) of
weight $w$. Shared primes between the endpoints are
allowed; only the bounds of each share by the actual raw
exponents are used.

## Global recovery and balance of prices

In the selected orientation write $N=dZ$ and $m_2=ch$.
Extend $f_0$ inside $hN$ to a divisor $f>2V_0H_0$, where
$V_0=q^{1.720+o(1)}$ uniformly bounds $m_2$. This crossing
is available since $N=dZ$ is eligible-smooth of height
$q^{2.500+o(1)}$, not just from the product $hZ$, whose
height exponent equals the determinant-width exponent.
Use no extra factors if $f_0$ already crosses; otherwise
stop at the first crossing. The overshoot is at most one
eligible prime of size $q^{o(1)}$. The additional smooth
multiplier costs $\tfrac12(2C-w)_+$ in the exponent by the
half-power count at the eligible ceiling. Split $f$ as
$f_hf_N$, with $f_h\mid h$ and $f_N\mid N$, at divisor
cost. In $(m_2,\beta)$ the conditions

$$ f_h\mid m_2,\qquad F_2m_2-q\beta\equiv0\pmod{f_N} $$

have exact index $f_hf_N$: Substitute $m_2=f_hj$, and solve
for $\beta$ modulo $f_N$ since $q$ is a unit. No coprimality
of the two filters is used. The determinant of two rows
in the box is bounded by $2V_0H_0<f$, so it vanishes, and
positive ambient-primitive rows are then unique. Actual
row primitiveness gives $(m_2,\beta)=1$ since a common
factor would divide both $F_2m_2$ and $N$. The sorted
prefixes of $F_2m_2$ and $N$ recover $c,d$, after which
the first label on $(c,d)$ recovers $v$. In the other
orientation the same rule on $(c,e)$ applies. The partner
price is subpower on the **original** $T$ partition, not
on the smaller projection. This proves the extra price

$$G=.22m+\tfrac12(2C-w)_+.$$

In the same bin the inherited alternatives are
$M=u/2+.22t$ (exact $S$ and global actual-triple recovery)
and $D=C-.28m$ (buy the pivot-heavier actual endpoint).
If the erased-heavier endpoint's $E_v\cup P$ part exceeds
$2UH_0$, $U=q^{.665+o(1)}$, there is also the inherited
fixed-input price $F=.860+.22(C-b)_+$. Otherwise $b+x_j\le
C+o(1)$ where $x_j$ is the pivot weight of that endpoint.
These are alternative codes, not simultaneous indices.

For the large radius put $p=.22$, $s=.28$, $I_0=.860$, and
set the threshold

$$ H_L=\frac{pC/s+C-L/4+(C+I_0/p)/2}{1+p/s+1/(2p)}. $$

It suffices to consider bins with $M,D\ge H_L-o(1)$,
and $F\ge H_L-o(1)$ when applicable. These satisfy

$$ m\le m_*+o(1),\quad m_*=(C-H_L)/s,\qquad
 t\ge (H_L-r/2)/p-o(1). $$

In the crossing case $H_L>I_0$ and the constraint on $F$
gives $b\le B_1+o(1)$, $B_1=C-(H_L-I_0)/p$. Otherwise
$x_j\ge t-m$ by $t\le x+y$, so
$b\le B_0+o(1)$ for $B_0=C-(H_L-r/2)/p+m_*$. At both
stated floors $B_0<B_1$ and $0<L/2-B_1<2C$. Consequently

$$G\le p m_*+C-L/4+B_1/2+o(1)=H_L+o(1).$$

Sum over masks and bins, and include $A<H_L$. This uses
only the existence of a covered code for each hit, not
that any bin or filtered lattice row is occupied.

## Use on the same screened population

Put $A_h=(h,k)$, $K=(Z,Z_0)$, $B_\beta=(|\beta|,|\beta_0|)$,
and $M_N=(dZ,eZ_0)$, where parentheses denote gcd. By
row primitiveness, $(kZ,hZ_0)=A_hK$. On the second-row
escape

$$ |k\beta-h\beta_0|> q^\eta A_h B_\beta M_N,$$

we have $A_hK\le q^{1.055-\eta+o(1)}$, since $K\mid M_N$
and the numerator is at most $2UH_0$. The total raw
height has exponent $4.220$, so the reduced height floor
is $L=2C+2\eta$. The [normalized second-row test][bracket]
charges the complementary pairs at $q^{\eta/2+o(1)}$
**per actual reference** at its actual $v$. Summing over
at most $q^{1.055+o(1)}$ columns gives $q^{1.135+o(1)}$
for $\eta=.160$, even before intersecting with the widened
screen complement. For $\eta=.272$ the same direct sum
only gives $q^{1.191+o(1)}$ on the unpruned list. Do not
transfer the $2.654$ height floor to triples with no
proven escape or height condition.

Thus an optional $.160$ deletion is affordable for the
original $1.1354$ complement target, with or without the
widened screen. Compare both radii on the **same** remaining
actual triples. A lower capture fraction $q^{-a-o(1)}$
there suffices for that target if $a\le.237900$ at $1.300$
or $a\le.209312$ at $1.475$. The larger radius needs a
certified relative gain of $q^{.028588-o(1)}$ to tie the
smaller upper price at that target. On the common
$L=2.654$ subset the corresponding larger-radius loss is
$.2231104$ and the break-even gain is
$q^{.0147896-o(1)}$. That comparison does not bound the
rest of the complement at the stricter height floor. On
the full population without a height or escape check, the
[input-first price][input] still applies. No lower capture
rate, density estimate, or admissible census is known
from these bounds. Next test either one paired score on
the common $.160$ escape, or count its unrestricted
survivors directly. Do not adopt a larger radius from
these passing prices alone.

Run `python3 .godel/alice/check-projected-erasure.py` for
exact checks of the two floors, thresholds, and budgets.
The [review replay][review] records the crossing premises
and separates that check from capture.

[review]: projected-erasure-review.md
[input]: input-first-erasure.md
[list]: shared-row-labels.md
[single]: singleton-erasure.md
[pivot]: global-pivot-row-price.md#single-rows-with-moving-and-with-fixed-inputs
[bracket]: same-input-second-bracket.md#two-more-deletions-on-the-same-pair-before-summing-over-inputs
