# Price punctured global relations among three common-input ratios

Fix one actual constructed ordered two-label list in $g=R=j=1$ and
count ordered distinct-denominator triples, including their complete
input $v$. Use the notation and successive-row freshness of the
[double ratio](global-double-ratio.md):

$$v=cF_1a=dY+q\alpha=eY_0+q\alpha_0,\qquad
cF_2h=dZ+q\beta,\qquad cF_2k=eZ_0+q\beta_0.$$

Use the reciprocal full-support masks of that note, including the
opposite denominator and both opposite rows: The full supported part
of $dY$ on the other column's support is $<q^{.118+o(1)}$, and
symmetrically for $eY_0$. Also require
$\operatorname{rad}(aZhY),\operatorname{rad}(aZ_0kY_0)>q^{3.960-o(1)}$,
as in the original-list [private cuts](private-output-radicals.md).
The original column charge times the partner allowance is $q^{1.134+o(1)}$
for this radical cut, and the reciprocal masks are a linear charge
$q^{.136+o(1)}I$ when summed over all actual references. We make no
further deletions for the count below. All heights and costs allow
uniform $q^{o(1)}$ factors.

Put $D=d/e$, $z=Y/Y_0$, $S=kZ/(hZ_0)$, and set

$$W=Dz=\frac{dY}{eY_0},\qquad V=DS=\frac{kdZ}{heZ_0}.$$

For a positive rational $R$, $[R]$ denotes its signed prime valuation
vector, and $h(R)$ is its reduced numerator times denominator. If $P$
is a prime set, $R_P$ keeps the full valuations at $P$. Prescribe **one**
rational linear space $B$ on the eligible prime coordinates, of
dimension at most $(\log q)^{1.44}$, for the whole ordered list. The
relation test is that some $(i,j,k')\in\mathbb Q^3\setminus\{0\}$ gives
$i[D]+j[z]+k'[S]$ agreeing with an element of $B$ off a prime set of
squarefree product at most $q^r$. Both the coefficients and erased set
may vary with the triple. For the indicated ranges of $r$, the total
passing triple exponents are at most:

| Coefficient type | Exponent | A radius and its price |
|:--|:--|:--|
| $j\ne0$ ($0\le r\le .796$) | $.91188+.28r$ | $.796$: $1.13476$ |
| $j=0$, $k'\ne0$ ($0\le r\le .636$) | $.9574752+.28r$ | $.636$: $1.1355552$ |
| $j=k'=0$ ($0\le r\le .980$) | $.86128+.28r$ | $.980$: $1.13568$ |

These bounds are global across moving denominators and do not assume
ordinary double-ratio multiplicity. At the common radius $.530$ the
union costs $q^{1.1058752+o(1)}$. In particular a dictionary of at most
$q^{.030+o(1)}$ spaces at that radius, or one space meeting at least a
$q^{-.030-o(1)}$ fraction of the actual residual triples, would suffice
for a bound $q^{1.1358752+o(1)}$ on that residual. Neither assertion of
occupancy is assumed in proving the passing prices.

## Recovery for the new labels

The row equations imply $W,V\equiv1\pmod q$ and
$W,V=1+O(q^{-1.110+o(1)})$. For $W$ subtract the first rows;
for $V$ compare $k$ times the second row at $d$ against $h$ times the
second row at $e$. The raw reduced-coordinate bounds for these ratios
are $q^{2.500+o(1)}$ and $q^{3.165+o(1)}$, respectively. Thus for any two
candidates the inter-label determinant divided by $q$ is integral and
has absolute value at most $Q_W=q^{2.890+o(1)}$ for $W$ and
$Q_V=q^{4.220+o(1)}$ for $V$. The bounds are uniform over the list;
choose the actual upper bounds including the subpower factors.

**Exact $W$.** Write $W=N/M$ in lowest terms and
$g=\gcd(dY,eY_0)$. Then $gN=dY$, $gM=eY_0$,
$E=(N-M)/q\in\mathbb Z\setminus\{0\}$, and
$gE=\alpha_0-\alpha$. Indeed $W=1$ would give the same product two
distinct deterministic prefixes. The positive $g\le2H/|E|$ and the
signed $\alpha$ satisfy $Ng+q\alpha\equiv0\pmod{F_1}$ and
$(g,\alpha)=1$ by first-row primitiveness and $q\nmid g$.
In a dyadic bin $J\le g<2J$, distinct primitive slopes $\alpha/g$ have
spacing at least $F_1/(4J^2)$ and lie in an interval of length $2H/J$.
Thus each bin costs $O(1+HJ/F_1)=q^{o(1)}$, since $H^2/F_1=q^{o(1)}$
or smaller. The two products recover their deterministic prefixes, and
$v=gN+q\alpha$. The fixed list and the sorted prefix of $v$ specify the
actual rows uniquely. This gives subpower many triples per $W$.

**Exact $V$.** Set $h=Ar$, $k=As$, where $A=(h,k)$, and
$dZ=T u$, $eZ_0=T w$, where $T=(dZ,eZ_0)$. Then
$V=su/(rw)$ is reduced: $(r,s)=(u,w)=1$ and
$(r,u)=(s,w)=1$ by the two row primitiveness conditions. Each exact
fraction gives divisor-many splits. For a split write
$E=(su-rw)/q$. If $E=0$, then the reduced positive fractions
$dZ/h$ and $eZ_0/k$ agree, and their equal numerators would have the
same deterministic prefix. Thus $E\ne0$. After swapping columns if
necessary for the count, $r\ge s$ and

$$TE=r\beta_0-s\beta,\quad T\le2rH/|E|,\quad
Tu+q\beta\equiv0\pmod{F_2r},\quad (T,\beta)=1.$$

For this split the primitive slopes $\beta/T$ in a bin
$J\le T<2J$ are spaced by at least $F_2r/(4J^2)$ and lie in an
interval of length $2H/J$. The count is $O(1+HJ/(F_2r))=q^{o(1)}$,
using $J\le2rH$ and $H^2/F_2\le q^{o(1)}$. The products $Tu,Tw$
recover $d,e$ by sorted prefixes. Recover $cA=(Tu+q\beta)/(F_2r)$,
split $c$ at divisor cost, and use the actual label $F_1$ on $(c,d)$
to recover $v$. In particular no second congruence index besides
$F_2r$ was used. The exact $V$ fiber is subpower.

**Exact $D^iS^{k'}$ for specified integers $i,k'$ with $k'\ne0$.**
If $i=0$, use exact $S$ recovery from the
[two-ratio count](joint-valuation-escape.md); if $i=k'$, take the
unique positive root and use $V$. Otherwise let $Q$ be the support of
the exact monomial. On an occupied fiber it is a subset of the union
of the supports of $D,S$ and has $O(\log q/\log\log q)$ primes.
Enumerate $D_Q,S_Q$ at subpower cost by their joint bounded total
multiplicity. With $(i_0,k_0)$ the primitive coefficient pair, the
integer kernel on each off-$Q$ coordinate gives
$D=D_Q\theta^{k_0}$ and $S=S_Q\theta^{-i_0}$ for a positive rational
$\theta$. Here $h(\theta)\le h(D)\le q^{2.110+o(1)}$, since
$|k_0|\ge1$. Write $V=C\theta^{n}$ with known $C=D_QS_Q$ and
$n=k_0-i_0\ne0$. The case $\theta=1$ is immediate. Otherwise the
height bounds on both $D$ and $S$ give $|n|=O(\log q)$.
The congruence $C\theta^n\equiv1\pmod q$ gives at most $|n|$ residues,
including when $n<0$ by inversion. The real estimate for $V$ confines
$\log\theta$ to an interval of length $q^{-1.110+o(1)}/|n|$.
For distinct reduced fractions $A_l/B_l$ in a single residue with
product height at most $M_0$, their cross determinant has magnitude
at least $q$, and also equals
$2\sqrt{A_1B_1 A_2B_2}\sinh(|\log(\theta_1/\theta_2)|/2)$ in
absolute value. With $M_0=q^{2.110+o(1)}$ this gives log spacing at
least $2\operatorname{arsinh}(q/(2M_0))$, hence subpower many
$\theta$ in the interval. Recover exact $S$ and use its global fiber
bound. This argument is uniform even if the original monomial or
unreduced coefficients have no polynomial height bound.

## Counting codes

Write $s_*=.22$. On a prescribed set of at most
$(\log q)^{1.44}+O(\log q/\log\log q)$ eligible primes, signed parts
of product height at most $X_0$ cost $X_0^{s_*}q^{o(1)}$ for
polynomially bounded $X_0$. For clarity, this bound applies to **any**
integer supported on these primes, even if it cancels out of a ratio.
At $\sigma=.22+1/\sqrt{\log\log q}$, Rankin majorizes the signed count
by $X_0^\sigma\prod_{p\in P}(1+p^{-\sigma})/(1-p^{-\sigma})$.
The prime floor $(2.1\log q)^2/(\log\log q)^4$ gives
$\sum_{p\in P}p^{-\sigma}=o(\log q)$ uniformly. On all eligible primes
the price is $X_0^{1/2}q^{o(1)}$, including signed splits, by the
[smooth count](ordinary-outside-product.md). In particular an erased
set costs $q^{r/2+o(1)}$ if fully enumerated. It suffices to erase
eligible coordinates. On $O(\log q/\log\log q)$ specified primes,
all valuations of a bounded-height tuple of raw factors cost
$q^{o(1)}$ once the primes are known, by stars and bars on the joint
total multiplicity. Use dyadic height bins throughout.

**Signed filters.** If reduced fractions with the same residue share
numerator divisor $A_0$ and denominator divisor $B_0$, then $A_0B_0$
divides their cross determinant and is coprime to $q$. Thus if the
divided determinant is bounded by $Q_0$, a shared signed filter with
$A_0B_0>Q_0$ forces equality. From any known signed filter extend
within the actual reduced factors until crossing $Q_0$, paying only
for the extra smooth product and its split, with overshoot at most
one eligible prime. If there is no crossing, enumerate the entire
remainder, specifying the exact label instead. Likewise if the full
$P$-part of a label is already above $Q_0$, enumerate just a signed
$P$-divisor first crossing $Q_0$ at $Q_0^{s_*}q^{o(1)}$ cost.
None of these enumerations requires the determinant to be smooth.

**The branch $j\ne0$.** Each of $Y,Y_0$ has radical weight at least
$1.445-(4.220-3.960)=1.185-o(1)$, where weights are base-$q$ logs
of distinct-prime products. At an endpoint, drop the boundary prime
of its own denominator, the primes in its own second row's $hZ$
(or $kZ_0$), and all primes in the opposite column's support. The
first loss is $o(1)$ by sorted prefixes; the second is at most $.115$
by actual successive-row freshness, and the third at most $.118$ by
the full reciprocal mask. The two surviving sets are disjoint,
contain no primes of $d,e,h,k,Z,Z_0$, and carry just one signed
first-output valuation per coordinate. After erasure their total
weight is at least $u=1.904-r-o(1)$. Select signed primes from these
sets up to weight $u$ with subpower rounding.

Use the binary mask family of the [local isolation proof](three-local-directions.md):
It has subpower size and contains a mask including the selected
primes and excluding all other raw primes and the erased set. The
required and forbidden sets are disjoint and each has
$O(\log q/\log\log q)$ primes. The family is fixed, not indexed by
enumerating the selected support. On an occupied mask the restriction
of $[W]$ is that of $[z]$, and the other two directions vanish there.
Dividing the projected relation by $j$ places this signed restriction
in the projection of $B$. On independently chosen pivots for that
projection, enumerate its radical at price $s_*u$, then all signs and
valuations on the resulting support at subpower cost. Interpolation
recovers the signed selected support as part of $[W]$. Use at least
its squarefree signed filter of height $q^{u+o(1)}$, and extend to
$Q_W$ by the preceding filter proof, then recover $W$. The price is
$s_*u+(2.890-u)/2=.91188+.28r$. Neither the full erased support nor
an unrestricted family of subspaces was enumerated in this branch.

**The branch $j=0$, $k'\ne0$.** Let $P$ be independent pivot rows
of $B$. Bin $h(V_P)=q^{t+o(1)}$. Write $D_P=a/b$, $S_P=f/g$ in
lowest terms, and put $J_P=(a,g)(b,f)$ (the cancellation product).
Since $(d,h)=(e,k)=1$, its factors divide $(d,Z_0)$ and $(e,Z)$,
respectively. Both are at most $q^{.118+o(1)}$ by the reciprocal
full-support masks. Thus $J_P\le q^{.236+o(1)}$. The numerator and
denominator of $V_P$ are $af/J_P$ and $bg/J_P$. **Enumerate $V_P$
and $J_P$ before the two pivot parts.** Given them, split the
reinstated numerator and denominator at divisor cost to recover
$a,b,f,g$. This pays exponent $s_*(t+.236)$, not the price on two
uncancelled parts with product height $h(V_P)J_P^2$.

Choose the erased set at cost $q^{r/2+o(1)}$ and extend $B$ by its
coordinate vectors to $B'$. The rows $P$ remain independent on
$B'$; complete them deterministically to pivots $P'$. Record the
actual $D,S$ valuations on the added $O(\log q/\log\log q)$ rows at
subpower cost. Let $T$ be the inverse of pivot restriction on $B'$.
The two correction vectors $T([D]|_{P'}),T([S]|_{P'})$ are now known.
Subtract each from its full vector. The residual two-column matrix
has rank at most one, since it has a kernel vector with second
coefficient nonzero. Record a nonzero spanning row index and the
two raw valuations there, or flag rank zero. This costs subpower
and determines the actual row (subtract the known corrections).
Every occupied code specifies the whole kernel, so choose one
deterministic integer vector $(i_1,k_1)$ in it with $k_1\ne0$.
The exact valuation of $D^{i_1}S^{k_1}$ is
$T(i_1[D]|_{P'}+k_1[S]|_{P'})$ and thus known. Uniform recovery
shows that the total price in the bin is at most
$s_*(t+.236)+r/2$.

A second price does not choose the erased set or use the relation.
For $h(V_P)\le Q_V$ enumerate its exact $P$-part and use signed
extension to the inter-$V$ bound $Q_V$, or the exact terminal label.
The price is $s_*t+(4.220-t)/2=2.110-.28t$. Above $Q_V$ the signed
$P$-divisor price is $.9284$. With $t$ below the cutoff, the
minimum of the two lines is at most their convex combination with
weights $.56,.44$ on the first and second prices. This is
$.22(4.220)+.56(.22(.236)+r/2)=.9574752+.28r$, which also bounds
the above-cutoff cost. The squared cancellation loss in product
height would apply to a height inequality for $V_P$, but not to
this exact factor-and-split code.

**The pure denominator branch.** Write $G=(d,e)$, bin it at
$q^{g_0+o(1)}$, and note $0\le g_0\le.118+o(1)$ by the masks.
For a recovered exact $D$, choosing $G$ costs exponent $g_0/2$
and fixes the ordered pair $d,e$. At fixed $d,e$ count *all* inputs
at cost $q^{.390+o(1)}$: The first-output ratio $z$ has inter-label
divided determinant at most $q^{.780+o(1)}$ at that fixed pair,
by the [fixed-pair count](same-input-second-bracket.md). Use the
signed filter proof with no pivots and then exact $z$ recovery.
This avoids a full-gap-box volume factor depending on $G$.

For $h(D_P)=q^{u+o(1)}$ on the base pivots of $B$, enumerate its
full part and either the erased set and added pivot data (here
$[D]\in B'$), or the full outside part using $h(D)=de/G^2$.
The two prices before $G$ and inputs are
$.22u+r/2$ and $(2.110-2g_0)/2-.28u$. Their minimum is at most
$.22(2.110-2g_0)+.28r$ by the same convex combination. Adding the
fixed-pair fiber and $G$ costs $.8542+.06g_0+.28r\le .86128+.28r$.
Only the first price uses erasure enumeration. All three branches
sum only over subpowerly many bins, flags, or masks apart from the
charged products, and no union over coefficients is needed.

## Consequence and remaining test

The common-radius bound applies to any subset of the retained list,
including the complement of the maximizing
[gap screen](denominator-pair-gap-regions.md). If the complement is
over budget, one can select successive triples adjoining their three
vectors to the current span. While the span dimension is at most
$(\log q)^{1.44}$, the union of the three relation tests costs at most
$q^{1.13568+o(1)}$ even at the larger type-dependent radii in the
table. A choice outside preserves independence of three new
directions, including modulo arbitrary erased sets up to the common
radius. This does not exhaust the eligible prime universe or prove
coverage. The new occupancy target at radius $.530$ is to exhibit,
in **one** global space, a $q^{-.030-o(1)}$ fraction of the actual
maximizing-screen complement with any punctured relation. For a span
sampled from that complement, the generators alone certify only a
subpower number of hits. Count additional hits with the simultaneous
lifts before inferring a fraction bound; neither the three passing
prices nor the selection argument provides one. Check the exponent
comparisons with `python3 .godel/alice/check-global-three-ratio.py`.
