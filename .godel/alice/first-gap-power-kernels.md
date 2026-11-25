# Discard small power-kernel mismatches on the actual rows

The [projected erasure count][screen] prices hits but leaves
open the $1.1354$ widened-screen complement. Here is a direct
pair deletion at that target, independent of either erasure
radius. It does not fix a reference per input, and it does
not require the gaps individually to have small power-free
parts.

Fix one actual constructed two-label list in $g=R=j=1$ as
in the [common-input count][list]. Write the primitive first
rows of an ordered triple as

$$v=cF_1a=dY+q\alpha=eY_0+q\alpha_0,\qquad d\ne e.$$

The signed gaps are nonzero and bounded by $H=q^{.390+o(1)}$.
For a fixed integer $m\ge2$, define

$$
D_m(\alpha,\alpha_0)=
\prod_{p:\,\nu_p(|\alpha|)\not\equiv\nu_p(|\alpha_0|)
                   \pmod m}p.
$$

The primes in this definition are **not** restricted to row
primes. For any $1\le Q\le q^{O(1)}$, the number of actual
ordered triples with $D_m\le Q$, hence also their number in
any subset of off-screen survivors, is at most

$$q^{1.055+.195/(2m-1)+o(1)}Q^{1-1/(2m)}. \tag{1}$$

For $m=2$, $D_2$ here is the squarefree part of
$|\alpha\alpha_0|$, not the normalized second-row bracket.
In particular, all pairs with equal squarefree kernels cost
$q^{1.120+o(1)}$. These choices give affordable deletions:

| $m$ | $\log_q Q$ | Total price exponent |
|---:|---:|---:|
| 2 | $.020$ | $1.135$ |
| 3 | $.049$ | $6809/6000 < 1.135$ |
| 4 | $.059$ | $63531/56000 < 1.135$ |

## First buy the filter, then solve for a power

For one actual $v$, let $n_v(u)$ be the number of its columns
whose first gap has absolute value $u r^m$, where $u$ is
$m$th-power-free and $r$ is a positive integer. Set
$\delta=1/(2m)$. Uniformly in $v,u$, we have

$$n_v(u)\le q^{o(1)}(H/u)^\delta \quad(1\le u\le H),\tag{2}$$

and the count is zero for $u>H$. To prove this, put
$R=(H/u)^{1/m}$. At an actual column, $N=dY$ is a product of
eligible primes in $[X/(\log\log q)^4,X]$, where
$X\sim(2.1\log q)^2$, and $N=q^{2.500+o(1)}$. In particular
$N>R$, so choose a divisor $f\mid N$ strictly crossing $R$,
with $f\le XR$, before enumerating $r$. There are at most
$q^{o(1)}\sqrt R$ possible $f$: The $X$-smooth half-power
Euler product has logarithm $O(\sqrt X/\log X)=o(\log q)$.
For a nonempty filter, $(quv,f)=1$: Primitiveness gives
$(v,N)=1$, and $v=N\pm q u r^m$ then also gives $(qu,N)=1$.
For each sign, $r^m\equiv \pm v/(qu)\pmod f$ has at most
$m^{\omega(f)}=q^{o(1)}$ unit roots. Indeed the primes of $f$
exceed $m$ for large $q$, so the roots modulo a prime are
simple, lift uniquely to every prime power, and combine by
CRT. Each class has at most one positive $r\le R<f$. The
resulting signed gap fixes $N=v-q\alpha$, and its sorted
prefix fixes $d$. At this actual $v$, the column and its
rows are then unique. This proves (2), without counting
arbitrary congruence solutions as columns.

## Sum small common kernels by inputs, large ones by columns

Write $u,u_0$ for the $m$th-power-free parts of the two
absolute gaps, and $D=D_m(\alpha,\alpha_0)$. Off the support
of $D$ their kernels agree, so write $u=g b$, $u_0=g b_0$,
where $g$ is their common part off $D$ and $b,b_0$ are
supported on $D$. Every prime of $D$ occurs in at least one
of $b,b_0$, whence $b b_0\ge D$. At a fixed $D$ there are
at most $m^{2\omega(D)}=q^{o(1)}$ choices of $b,b_0$, since
all kernel exponents are below $m$. The subpower bound is
uniform for arbitrary primes in polynomial-height $D$:
The product of the first $k$ distinct primes is at least
$(k+1)!$.

On the list there are at most $q^{.860+o(1)}$ complete
inputs by enumerating $v/F_1=ca$ at half power. There are
at most $q^{1.055+o(1)}$ actual columns in total: Enumerate
$(c,d)$ at half power, and the first label specifies at
most one first row on each such column. Use these two bounds
in different parts of the sum.

* For $g\le G$, fix an input. At fixed $g,D,b,b_0$, the
  ordered-pair count is at most $n_v(gb)n_v(gb_0)$, bounded
  by $q^{o(1)} H^{2\delta}g^{-2\delta}D^{-\delta}$ by (2).
  Summing and then buying inputs costs at most
  $$q^{.860+o(1)}H^{2\delta}G^{1-2\delta}Q^{1-\delta}.$$
* For $g>G$, fix an **actual column** at its $v$ and let $u$
  be its kernel. The part $D_1$ of $D$ on primes of $u$ is
  a divisor of $\operatorname{rad}(u)$, so there are subpower
  many choices. This names $g=u/u_{\operatorname{supp}D_1}$,
  where the denominator is the full supported part, not
  just $D_1$. Sum over $D_0=D/D_1\le Q$; all its primes
  occur in $b_0$ since they occur in $D$ but not in $u$.
  Thus $b_0\ge D_0$. Each chosen $D_0,D_1$ has subpower many
  $b_0$, and (2) bounds its partner count by
  $q^{o(1)}H^\delta G^{-\delta}D_0^{-\delta}$. Summing now
  over **all** actual references costs at most
  $$q^{1.055+o(1)} H^\delta G^{-\delta}Q^{1-\delta}.$$

Only upper bounds are used in these sums, so repeated gaps
or same-column pairs inadvertently included in the first
sum do not matter. Take
$G=q^{(.195-.390\delta)/(1-\delta)}$ to balance the two
exponents. Using $H=q^{.390+o(1)}$ gives (1). Applying the
second sum to *every* common kernel would cost
$1.055+.390\delta$ before the $Q$ price, already $1.1525$
for squares. Summing small common kernels by inputs is what
makes the square test affordable. Run
`python3 .godel/alice/check-first-gap-power-kernels.py` to
check the split and all six prices with exact rationals.

## Count second-row kernels by a projective filter

In the second row use the same bound $H$ for the nonzero
signed gaps, increasing its subpower factor if necessary.
Define the $m$th-power-free kernels $(u,w)$ by $|\beta|=u r^m$
and $h=w s^m$ for $cF_2h=dZ+q\beta$ at the same $v$.
Define $D$ for two columns
as the product of primes where **either** of these two
kernel coordinates differs. Do not take the residue of
the difference of valuations: A prime could then switch
from the numerator to the denominator without changing
that residue. At fixed $v$, $c$ is known, but $h$ is not.
Instead of paying for $h$, use the projective congruence.

Put $U=q^{.665+o(1)}$ for the cofactor bound, and set
$R=(H/u)^{1/m}$ and $S=(U/w)^{1/m}$ for an occurring
kernel. Buy a smooth divisor $f\mid N=dZ$ strictly
crossing $RS$, available since $N=q^{2.500+o(1)}$ whereas
$RS\le(HU)^{1/m}$. Its enumeration costs
$q^{o(1)}\sqrt{RS}$. By $(cF_2 h,N)=1$, the second gap
and all quantities in the congruence below are units
modulo $f$. For each sign,

$$ (r/s)^m \equiv \pm cF_2 w/(qu)\pmod f. $$

There are again subpower many roots. Two pairs $(r,s)$
in the same root class have determinant divisible by
$f$ and of absolute value less than $RS$ (both products
are positive and at most $RS$). Since $(h,\beta)=1$, the
pairs $(r,s)$ are primitive. Thus the sign and root fix
$(r,s)$, then $h,\beta$, the product $dZ$, and the column
at $v$ by the sorted prefix of $dZ$. The pointwise
bound is $q^{o(1)}(HU/(uw))^\delta$.

The same balanced price as in (1), but with a slightly
larger $Q$ charge, is available for these second kernels:

$$\#\{\text{actual ordered triples with }D\le Q\}
 \le q^{1.055+.195/(2m-1)+o(1)}Q^{1-1/(4m)}. \tag{3}$$

To see this, fix $D$ and the full parts of the four
kernels supported on $D$. At fixed $D$ these cost
$m^{4\omega(D)}=q^{o(1)}$ choices. Write the common gap
and cofactor parts outside $D$ as $g$ and $l$.
The product of the four supported parts is at least $D$.
By choosing the orientation (a factor of two for the
ordered count), the partner's two supported parts have
product at least $\sqrt D$. At each actual reference
input, the pointwise bound just proved counts at most

$$q^{o(1)}(HU/(gl))^\delta D^{-\delta/2}$$

partners at these kernels. Do not sum over all possible
inputs for the reference. Instead buy $c$ at exponent
$.5275$, and bin $l$ in $L\le l<2L$. Since $l$ is eligible
smooth, this bin costs $q^{o(1)}\sqrt L$; after fixing $l$
and the supported cofactor part, $h=w s^m$ has at most
$q^{o(1)}(U/L)^\delta$ choices since $s$ also is eligible
smooth. Both counts use the half-power Euler bound.

At fixed $c,h$, the reference has fixed second product
$cF_2h$. Its gap $\beta$ identifies $dZ=cF_2h-q\beta$,
whose sorted prefix is $d$. The list's first label then
identifies the first row at $(c,d)$ and thus the actual
reference input for the partner bound. There are two
ways to pay for the reference:

* For $g\le G$, additionally fix $g$ and use the bound
  $q^{o(1)}(H/g)^\delta$ on the reference gaps, by exactly
  the power-filter proof of (2) with $v$ replaced by
  $cF_2h$, and using the now known gap kernel (at least
  $g$). Buying $c,l,h$, the reference gaps, and the
  partners, then summing over $g\le G$ in each $L$ bin,
  costs at most
  $$q^{.5275+o(1)}H^{2\delta}U^{2\delta}
       L^{1/2-2\delta}G^{1-2\delta}D^{-\delta/2}.$$
* For $g>G$, do not guess $g$. At fixed $c,h$, buy any
  $f\mid dZ$ crossing $2H$ at cost $q^{o(1)}\sqrt H$.
  The signed gap is unique modulo $f$ in $[-H,H]$.
  This counts actual references, each supplying its own
  $g>G$ and input. All crossings here are available
  from $dZ=q^{2.500+o(1)}$. The total in the $L$ bin is
  at most
  $$q^{.5275+o(1)}H^{1/2+\delta}U^{2\delta}
       L^{1/2-2\delta}G^{-\delta}D^{-\delta/2}.$$

Since $m\ge2$, $L^{1/2-2\delta}\le U^{1/2-2\delta}$;
there are only logarithmically many bins. Buying $c$
and the net factor $U^{1/2}$ costs exponent $.860$.
The large-$g$ branch pays an additional $H^{1/2}$, so
the two exponents balance at the same $G$ as in (1).
Finally sum $D^{-\delta/2}$ over $D\le Q$. In
particular **square** kernels already afford a second-row
cut. Using only the projective multiplicity and the total
column bound at equal kernels would cost exponent
$1.055+(.390+.665)/(2m)$, or $1.31875$ for squares,
even at $Q=1$.

| $m$ | $\log_q Q$ | Total second-row price exponent |
|---:|---:|---:|
| 2 | $.017$ | $9079/8000 < 1.135$ |
| 3 | $.044$ | $3403/3000 < 1.135$ |
| 4 | $.055$ | $25411/22400 < 1.135$ |

## Remaining decision

The union of the three first-gap and three second-row
cuts costs $q^{1.135+o(1)}$ in actual triples.
They may be discarded after the normalized second-row
cut and the widened screen, with no change to the
$1.1354$ target. This removes specified arithmetic
classes, not a certified fraction of that population. No
comparison of hit rates at radii $1.300$ and $1.475$ follows.
For a future hit-rate comparison, either leave these cuts
out of both populations or use the same deletion at both
radii. The direct count still needs a bound on the
large-mismatch survivors. At fixed $(d,e)$, a concrete
next test is to count distinct reduced ratios $S=kZ/(hZ_0)$
realized on the residual of the [gap-plane sieve][planes].
Exact $S$ already [recovers triples][exact] at subpower
cost there, so a bound on the number of occupied ratios,
summed over denominator pairs, suffices. Across the at
most $q^{1.055+o(1)}$ potential ordered pairs, the target
average is $q^{.0804+o(1)}$ (use a strict saving for a
power margin). In the outer gap prisms, test the second
rows on the low projected-index nonvertical planes;
triples outside those prisms still require a separate
bound. The kernel argument gives local multiplicity at a
prescribed kernel, not a count of occupied ratios or an
independent density to multiply into either gap-plane
price.

[screen]: projected-erasure.md
[list]: same-input-second-bracket.md
[planes]: denominator-pair-gap-regions.md
[exact]: joint-valuation-escape.md
