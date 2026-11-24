# Price reference disks on the cubic jet residual

Use the [good-axis LCM test](jet-axis-lcm.md) in a fixed occupied
$(v,h,f,C)$ cubic fiber, with the same joint $(h,f)$ rule and the
same small-bad-part hypothesis. Fix one actual point $Q_0=(i_0,j_0)$
in this fiber and one support $S$ of $O(\log q)$ primes. For example,
include the prime supports of the reference outputs. This is a local
support chosen **after** fixing the filter, not a replacement for the
support prescribed per input in the joint cofactor rule. The price
below is uniform in $Q_0$ and $S$.

## The modulus at a fixed reference

Write $n_x=A-qi$, $n_y=B-qj$, $l=d/f$, and let $M$ be the good-axis
LCM. For $Q\ne Q_0$ put

$$D=\gcd(|i-i_0|,|j-j_0|)_{S_{\rm sm}},\qquad
 S_{\rm sm}=\{p\in S:p\ne q,\ \nabla C(i_0,j_0,1)\not\equiv0\pmod p
                    \text{ in the two affine coordinates}\}.$$

A prime of $D$ is marked if $Q_0\equiv(A/q,B/q)\pmod p$. Enlarge the
supported axis base and keep its separate row factor as follows:

$$K=\prod_{\substack{p\mid D\\p\,\mathrm{marked}}}
       p^{\min(v_p(n_x),v_p(n_y))},\qquad
 B_0=\operatorname{lcm}(M_S,K),\qquad B=\operatorname{lcm}(B_0,D).$$

For $p\mid B_0$, mark it if $Q\equiv(A/q,B/q)\pmod p$, whether or
not it divides $D$. Put $v_p(J)=(v_p(B_0)-v_p(l))_+$ at marked
primes of $B_0$, and zero elsewhere. This can recover some marked
base even when both axis tests exclude $p$: The nonsingularity
condition for $D$ is only at the reference, not on a full axis
fiber. It does **not** give any row factor from excess depth in $D$.

At $p^k\parallel B_0$ with a good axis, use the corresponding
labeled axis and root from the LCM proof: The full good-axis
valuation is at least the minimum defining $K$. If $p$ occurs only
through $K$,
the marked center is nonsingular modulo $p$ and is in the same
residue disk as the candidates. Choose a projection whose other
partial derivative is a unit, and center its parameter $t$ at
$P/q$. By the implicit series on this disk both displacements
have valuation at least $v_p(t)$, with equality on the chosen
coordinate. Thus $v_p(t)=\min(v_p(n_x),v_p(n_y))$; this also holds
on a marked good-axis disk. The normalized row has factor
$(t/l)^r$ as before. At $p\mid D$ with $p\nmid B_0$, use the smooth
reference disk and its free coordinate, centered at $Q_0$.
Such a prime is unmarked, since otherwise $p\mid K$. For any
unmarked disk used here $p\nmid l$, so normalization contributes
only a unit. If $p\mid D,B_0$, use the **same** coordinate already
chosen for $B_0$; congruence in both coordinates places candidates
and the reference on the same root class. The series used for the
base and row factors remains valid.

Partition by the indicated supported moduli, row factor, and axis
and root labels. At a prime of $B_0$ the candidate parameters are
all zero modulo $p^{v_p(B_0)}$ in the axis or marked-center
parameter. At a prime of $D$ all the parameters agree with the
reference parameter modulo $p^{v_p(D)}$. These give the maximum,
not the sum, of the two depths for every inter-candidate parameter
difference. The wedge divisor is therefore $B^V J^{ra}$, where
$V=\binom a2$, by the same alternating-polynomial argument as in
the [LCM proof](jet-axis-lcm.md#local-divisibility-with-the-jet-normalization).
The reference need not be one of the wedge rows. A disjoint
outside axis modulus $G\mid M_{\bar S}$ gives its separate factor
$G^V J_Q(G)^{ra}$.

The extra common Vandermonde modulus this argument credits beyond
$B_0$ is $D/(D,B_0)$, not $D$. Nor should $D$ be capped by the prime
powers in the reference outputs: Those outputs only prescribe
support, and two displacements of the same valuation can agree to
higher depth. At a shared prime, the parameter-difference depth
equals the minimum of the two coordinate-difference depths: In a
smooth disk, the other coordinate is an integral power series in
the selected coordinate, so its difference is divisible by the
parameter difference. In that same parameter, if the full base depth
is $k$ and the
reference has a different valuation from the candidate, then
$v_p(t-t_0)\le k$ and no increment occurs. If both have depth $k$,
the increment is the valuation of the difference of their unit
parts. For example, at any odd prime with a marked smooth disk,
parameters $p^k$ and $2p^k$ have the same depth $k\ge1$ and no
increment. This local example works even if one grants a marked
surplus in the row factor. It is not a pair of actual smooth
columns. Equal branch and depth alone cannot justify extra
credit; whether actual columns impose unit agreement remains open.

## A uniform price at the actual reference radius

Bin $\max(1,|i-i_0|,|j-j_0|)$ dyadically, with upper endpoint $R$.
Use radius $R$ centered at $Q_0$ when $R<N$ and the original square
otherwise. Put $\lambda=\max(0,\log_q(N/R))$. Translation keeps
$l$ unchanged and changes the primitive center to
$[A-qi_0:B-qj_0:q]$. Its scaled length is at most
$q^{2.110+\lambda+o(1)}$. If $H_R$ is the norm of the translated
component at the smaller radius, then

$$H_R\gg (R/N)^3 H.$$

Indeed undo the translation at scale $N$ (a bounded operator on
cubic coefficients since $Q_0$ is in the original box) and undo
the scaling $R/N$, of inverse operator norm at most $(N/R)^3$.
The curve stays primitive under integral translation. This gives,
with $S_{m,r},L_{m,r},b$ the quotient exponents, a reduction of
$(2S_{m,r}-L_{m,r}-3b)\lambda$ in the exponent of the full-rank
obstruction, over and above the local modulus. Neither $J$ nor
$l$ is rescaled. At $(m,r)=(10000,1200)$ set

$$Z=2S_{m,r}-L_{m,r}-3b=138734399,
\qquad \kappa=Z/b=2.81605006\ldots.$$

The following sufficient screen costs $q^{.01035+o(1)}$ columns
in this fiber. Let $\tau=.0207$, let $T$ be the quotient norm
threshold after the ordinary crossing, and keep $V_2=V/b$ and
$V_1=ra/b$. Suppose there exists $G_0\mid M_{\bar S}$ with
$\operatorname{rad}(G_0)\le q^\tau$ such that, with fixed positive
slack,

$$w+\kappa\lambda+
 V_2\log_q\!\left(B\frac{G_0}{\operatorname{rad}(G_0)}\right)
 +V_1\log_q\!\left(JJ_Q(G_0)\right)>T. \tag{1}$$

Here $w=\log_q(H/N^3)$ is from the original square. Extend the seed
by unused outside primes of $M$ until crossing $q^\tau$ in the
outside radical, at subpower overshoot. The new divisor $G$ gives
$B^V G^V J^{ra}J_Q(G)^{ra}$ in the normalized wedge, and (1)
contradicts full rank by the quotient determinant estimate. If the
radical never crosses, take $G=M_{\bar S}$. Then $BG\ge M\ge
q^{.7198-o(1)}$ by the small-bad-part fallback, sufficient even at
$w=\lambda=0$ without row credit. The outside radical costs
$q^{\tau/2+o(1)}$ by the eligible-prime half-power estimate at
cutoff at most $(\log q)^{2+o(1)}$. Given this radical, enumerate
the exponent vectors of the final moduli and row factors on it
and $S$ at subpower cost. The branch labels, radius bins, and
pointwise divisor recovery are subpower, too. Rank loss gives at
most $3m$ points per class. The seed need not be enumerated
separately. The anchor's own point costs divisor-many columns.

At $w=0$, if there is just the ordinary purchased copy and no
base or row credit, the normalized difference and radius must
supply

$$\log_q D+(Z/V)\lambda>.02269924\ldots.$$

Thus the full-width difference modulus alone needs that exponent;
radius alone would work at $R\le q^{.0669}$. If two purchased
copies and one marked surplus are supplied at exponent $\tau$,
the deficit in the same units is $.00027418\ldots$. At shared
primes use $D/(D,B_0)$ for the extra modulus after accounting for
$B_0$. In the two-copy case a shrink of exponent $.00082$ suffices
without further divisibility. The [arithmetic check](check-jet-reference.py)
checks these margins. Neither concentration at that radius nor
this difference modulus is forced.

A grid at side comparable to $R$ allows one actual anchor per
occupied cell, using $O_C(1+N/R)$ anchors rather than $(N/R)^2$.
Each grid line meets $C$ in at most three points, so at most
$O(1+N/R)$ cells meet $C$ on their boundary. Any remaining cell
meeting $C$ contains a compact real component with a coordinate
extremum. Such cells cost $O(1)$ by Bézout applied to $C$ and its
second-coordinate partial derivative, which is nonzero and has
lower degree. But paying for a $q^\lambda$ anchor bound by
reducing the crossing by $2\lambda$ loses $2V\lambda$, more than
the radius saves in this bound. If the budget reduction exhausts
the crossing, this payment is unavailable in the first place.
This comparison assumes no additional credit from the anchors;
it does not rule out fewer occupied cells or other divisibility.

## Counting objects, not partners of the anchor

With one prescribed support per complete input for the existing
joint cofactor and first-divisor rule, use one anchor at each
occupied cubic fiber (only boundedly many components per filter).
The pointwise estimate sums to $q^{.13795+o(1)}$ passing columns
per input. Ordered triples with **both** columns passing in this
family cost $q^{.860+2(.13795)+o(1)}=q^{1.1359+o(1)}$, also on the
complement of the maximizing region. There is no sum over
alternative anchors in this object count.

In fact the anchor generally cannot be interpreted as a partner
in the retained triples. Both denominators in this fiber are
multiples of the same $f\ge q^{.2552}$, but the
[reciprocal row deletions](same-input-second-bracket.md#two-more-deletions-on-the-same-pair-before-summing-over-inputs)
require retained pairs to have gcd at most $q^{.118+o(1)}$.
The auxiliary comparison is internal to a filter, whereas the
retained pair uses different filters. Neither testing all anchors
at the same price nor imposing the retained-pair separation on
the internal comparison is justified.

**Decision.** Use (1) as a uniform fixed-anchor deletion, not as
an occupancy bound on the whole cubic. At full width it reduces
the missing input to concentration of unit parts (or independent
base or row credit), and a close archimedean cluster can trade
against that concentration at the displayed rate. Next test the
far, low-credit candidates without assuming a reference hit:
One would need a uniform bound on that residual or a proof that
one actual anchor catches enough of it after accounting for the
remaining size. This does not treat unrestricted cofactors or the
full denominator-pair complement.
