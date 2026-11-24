# Price reducible reductions and split infinity on cubic filters

Use the [prescribed-product jets](prescribed-product-jets.md). At
fixed actual $(v,h,f)$, the points $Q=(i,j,1)$ lie in a box of width
$2N$, where $N=q^{.1348+o(1)}$. A primitive absolutely irreducible
cubic $C$ is a component of the confining curve. Here are two
independent tests with bounded point occupancy per such cubic. The
first does not use smoothness, the marked point, or coefficient
height. The second excludes a low-norm through-point cubic when
its binary cubic at infinity splits into distinct rational factors.

## A degree-four determinant for reducible reduction

Suppose $C\bmod q$ is geometrically reducible. Then $C$ contains at
most 15 distinct integral points in this box. More generally one may
prescribe a squarefree modulus $D=q^{O(1)}$ such that every reduction
at $p\mid D$ is geometrically reducible. If $D^4/N^{29}$ tends to
infinity, the bound is $12\,O(1)^{\omega(D)}=q^{o(1)}$. The modulus
is common to the points, not chosen or enumerated separately for each
point. For $D=q$ the strict exponent inequality is
$29(.1348)=3.9092<4$.

Let $V_j$ denote homogeneous ternary forms of degree $j$. Over
$\mathbb Q$ work in $V_4/CV_1$, of dimension $15-3=12$. Choose a
monomial order after dehomogenizing that puts higher affine degree
first. The leading affine monomial of $C$ has degree three since $C$
is not divisible by $Z$. Delete its three multiples by $1,X,Y$
from the affine monomials of degree at most four. These are the only
possible leading monomials of a nonzero element of $CV_1$, so the
remaining 12 monomials form a rational quotient basis. Their sum of
affine degrees is $40-(3+4+4)=29$. Every 12-row evaluation determinant
of this basis has absolute value at most $12!N^{29}$.

At a prime $p\mid D$ (in particular $p=q$ in the first assertion),
partition the points by a geometric component of their reduction,
ignoring multiplicity. For each component defined over $\mathbb F_p$
choose a defining polynomial $G$ over that field. Any point on a
component not defined over $\mathbb F_p$ also lies on a distinct
Frobenius conjugate. Use a separate label for each such intersection
point over $\mathbb F_p$, assigning ties in any fixed order. There
are at most three geometric components, each of degree at most two,
and only boundedly many intersection points by Bézout. A class for
the modulus $D$ fixes one label per prime. At $q$ alone one can
instead use exactly the geometric component labels: Each non-rational
component has at most one $\mathbb F_q$-point since it has a distinct
conjugate of the same degree and both must be lines. Reduction is
injective on the box since $2N<q$ for large $q$.

Here is the integral step. At $p$, reduction of multiplication by
$C$ on $V_1$ is injective, since $C$ is primitive and $\mathbb F_p$
polynomial multiplication has no zero divisors. Thus $CV_1$ over
$\mathbb Z_p$ is a free direct summand of $V_4$: Extend a basis of its
reduction and lift the added columns to get a basis with unit
determinant. Consequently one can choose *any* basis modulo $p$ of
$V_4/(CV_1)$, lift its representatives, and use them as an integral
local quotient basis. Evaluation on the actual points kills $CV_1$.
Any 12-column evaluation determinant from integral forms, including
the archimedean monomials, therefore inherits the divisibility of
the determinant in this local basis by an integral transition
matrix. That matrix need not have unit determinant. In particular
an archimedean leading coefficient divisible by $p$ is harmless.

* On a conic label, the image of $G V_2$ in the quotient modulo $p$
  has dimension $6-3=3$ since it contains $CV_1$. The image of $G^2$
  is nonzero: Otherwise $G$ would divide the linear factor of
  $C\bmod p$ times a linear form, which is impossible for a
  geometrically irreducible conic. Extend this class by two other
  classes from $G V_2$, then complete the basis. Lift the first
  class as the square of the *same integral lift* of $G$, and the
  next two as its products with lifted quadratics. Their evaluation
  columns contribute $p^2,p,p$, respectively. No lifting of a
  factorization of $C$ is required.
* On a line label the image of $G V_3$ has dimension $10-3=7$.
  Lift seven classes as multiples of a lift of $G$ and complete the
  basis. The determinant is divisible by $p^7$. A repeated line
  poses no problem.
* On a point label all rows are equal modulo $p$. Subtracting the
  first row from the other 11 gives $p^{11}$ directly.

Each determinant on a class is thus a multiple of $D^4$. Comparison
with the archimedean bound forces rank less than 12, including when
there are fewer than 12 rows. A nonzero rational combination of the
12 basis forms vanishes at every point in the class and is not a
multiple of $C$. Bézout bounds the class by 12 points. For $q$ alone, a rational line label is cheaper: Any three rows
$(1,i,j)$ have determinant divisible by $q$ and bounded by $6N^2<q$
for large $q$. The points on the label therefore lie on a rational
line and cost at most three by Bézout. Non-rational lines cost at
most one by injectivity. Thus a conic plus a line costs at most
$12+3=15$, and any union of lines costs at most nine. For $D$ there
are $O(1)^{\omega(D)}$ classes. This proof does not supply a
modulus with the required reductions on the complementary family.

## Use a simple rational infinity direction to find a short line

Write $P=[A:B:q]$, $P-qQ=l(Y,Z,0)$, and $W=H/N^3\ge1$ as in the
[quotient determinant](jet-quotient-determinant.md). In an occupied
filter, $R=\max(|A|,|B|)=q^{2.2448+o(1)}$. Indeed, $A-qi=lY$ has
that size by $l=q^{.7998+o(1)}$ and the actual output
$Y=y_1=q^{1.445+o(1)}$ from [row freshness](shared-row-labels.md),
while $qi$ is negligible. The coefficients of each affine layer
$H_j$ of $C$ are $O(N^{3-j}W)$.

There is **no integral line through $P$** with nonzero coefficient
vector of size at most $q^{.7998-\epsilon}$ for any fixed
$\epsilon>0$ and all sufficiently large $q$. Indeed, this size is
$o(c/f)$, where $c/f=q^{.7998+o(1)}$. In fact the
line equation $U A+V B+Jq=0$ gives
$c(Ux_1+Vx_2)=q(U\alpha_f+V\beta_f-Jf)$. As $q\nmid c$ and the
centered residues have size $O(f)$, $Ux_1+Vx_2$ is a multiple of
$q$ of size $o(q)$. Its vanishing for a nonzero pair $(U,V)$ needs
an entry of size at least $q^{1.330-o(1)}$ by row freshness,
impossible. The case $U=V=0$ would give $J=0$.

Suppose $H_3=\ell Q_2$, where $\ell$ is primitive integral linear
and does not divide $Q_2$. Put $u=\|\ell\|_\infty$, so $u\ll W$ and
$\|Q_2\|_\infty\ll W/u$ by fixed-degree norm multiplicativity up
to constants. Write $a_0=(A,B)/R$. Fix a sufficiently small absolute
constant $\gamma>0$ and call this direction real-close if
$|\ell(a_0)|\le\gamma/W$. Call it modular if $q\mid\ell(A,B)$.
For $W\le q^{.035}$ there are two tests, according to how this
particular rational direction is used.

**Both real-close and modular.** The sup-norm-one kernel vector of
$\ell$ nearest $a_0$ is within $O(|\ell(a_0)|/u)$, by projecting
along a coordinate of size $u$ and normalizing. At this kernel
vector $|Q_2|\ge 1/u^2$ by simplicity and integrality. Its change
is $O(W|\ell(a_0)|/u^2)$, so $|Q_2(a_0)|\gg 1/u^2$.
By $C(P)=0$ and the layer bounds,
$|H_3(a_0)|\ll NWq/R$. Therefore $|\ell(A,B)|\ll qNWu^2$.
The line $\ell(X,Y)-[\ell(A,B)/q]Z=0$ through $P$ is integral by
modularity. Its coefficient vector is $O(NW^3)=o(c/f)$, which is
impossible. This part alone works for $W\le q^{.192}$, since
$.1348+3(.192)<.7998$.

**Neither real-close nor modular.** Such a direction cannot occur
in an occupied filter at $W\le q^{.035}$. The following short-line
argument was proposed by RuoHamn. After exchanging coordinates,
write $s=X/Z$ and $t=u_1X/Z+u_2Y/Z$ with $|u_2|=u$. Substitute
$(X/Z,Y/Z)=(s,(t-u_1s)/u_2)$ and multiply by $u_2^2$ to get an
integral polynomial

$$t(as^2+bst+ct^2)+ds^2+est+ft^2+g_0s+h_0t+k_0.$$

Here $a\ne0$ by simplicity; within this display and the next
calculation $c,f$ denote polynomial coefficients, not column
and filter data. The sizes of $(a,b,c)$ are $O(Wu,W,W/u)$,
those of $(d,e,f)$ are $O(NWu^2,NWu,NW)$, and those of
$(g_0,h_0,k_0)$ are $O(N^2Wu^2,N^2Wu,N^3Wu^2)$, entrywise.
They follow by expanding each homogeneous layer with the inverse
linear substitution. Set $r=d/a$ and $x=t+r$. The polynomial is
exactly

$$x U_*(s,x)+g s+k,\qquad
 g=g_0-er+br^2,\quad k=k_0-h_0r+fr^2-cr^3.$$

Here

$$U_*=as^2+bsx+cx^2+(e-2br)s+(f-3cr)x+h_0-2fr+3cr^2.$$

The coefficient of each degree-$j$ term in $U_*$ has denominator
dividing $a^{2-j}$. Directly,
$|a^2g|\ll N^2W^3u^4$ and $|a^3k|\ll N^3W^4u^5$.

At $P$ we have $|t|\gg R/(qW)$ and $|r|\ll NWu^2=o(R/(qW))$,
so $|x|\gg R/(qW)$ and $|s/x|\ll W$. Also $0<|a|\ll W^2<q$
for large $q$, and $v_q(x)=-1$, so $s/x$ and $1/x$ are
$q$-integral. The value $U=U_*(s(P),x(P))=-g s(P)/x(P)-k/x(P)$ is $q$-integral. As
$a^2 q^2 U\in\mathbb Z$ by the coefficient denominators and
$s,t\in q^{-1}\mathbb Z$, we obtain $a^2U\in\mathbb Z$. The
archimedean bounds give

$$|a^2U|\ll N^2W^4u^4+N^3W^4u^5/|x|\ll N^2W^4u^4,$$

using $|x|\gg Nu$. Freeze this value of $U$; then
$U t+g s+(U r+k)=0$ is a line through $P$. It is nontrivial:
$U=g=0$ would give $k=0$ and make the cubic divisible by $x$.
After multiplying by $a^3$ it has integral coefficients in the
original coordinates, bounded by $O(N^2W^5u^6)$ for the leading
pair and $O(N^3W^5u^6)$ for the constant. The bounds follow from
$|a|\ll Wu$ and $|d|\ll NWu^2$. They are $O(N^3W^{11})$ in total,
with exponent at most $.4044+11(.035)=.7894<.7998$, contradicting
the no-short-line bound.

**Consequences.** If $H_3$ is split with three distinct rational
directions, the filter has no actual point at $W\le q^{.035}$.
Indeed, factor $H_3$ into primitive integral linears times integer
content. The product of the norms is $O(W)$ by fixed-degree norm
comparison. At most one factor is real-close: Inverting the two
rows of any pair, using their nonzero integer determinant and
norms $O(W)$, would otherwise give $\|a_0\|_\infty\ll\gamma$.
At most one is modular, since the pair determinants are nonzero
integers of size $O(W)<q$, and $(A,B)$ is nonzero modulo $q$.
Thus a third direction is unused at both places, which the second
test excludes even if the two used directions coincide. For a
rational line times an irreducible quadratic, the two tests also
exclude the cases in which the rational direction is used at both
places or neither. The cases in which it is used at exactly one
place are not covered by this dichotomy.

**A modular simple rational direction cannot be a flex.** This
subscreen works at $W\le q^{.192}$. Keep the coordinates and shift
above, and now assume the direction is modular. The simple infinity
point is $[1:0:0]$ in $(s,t)$ coordinates, with tangent $x=0$;
restriction to the tangent after homogenizing is $Z^2(gs+kZ)$.
Thus a flex gives $g=0$. At $P$ we have $x\in a^{-1}\mathbb Z$,
$v_q(s)=-1$ since $q\nmid AB$, and $a$ is still a $q$-unit. The
term $as^2$ of $U_*$ has valuation $-2$ and all other terms have
valuation at least $-1$. Consequently $xU_*=-k$ at a flex forces
$q^2\mid ax$ as $k$ is $q$-integral. But

$$|ax|\ll W^3R/q+NW^3\le q^{1.8208+o(1)}=o(q^2).$$

So $x=0$ at $P$, hence $k=0$, and then $x$ is a factor of $C$,
impossible. No real-close condition is needed.

A repeated binary direction cannot be modular on a smooth cubic in
the residual range $W\le q^{.192}$. A repeated factor is rational
since its multiplicity is at least two in a cubic. At its primitive
kernel vector $w$, smoothness at $[w:0]$ forces $H_2(w)\ne0$, as
the binary derivatives vanish there. If $w$ is modular, reducing
$C(P)/q$ modulo $q$ gives $H_2(A,B)=0$ modulo $q$ because the
repeated factor gives $q^2\mid H_3(A,B)$. But
$0<|H_2(w)|\ll NW^2<q$, a contradiction. Thus a triple direction
is impossible. For a double direction the simple direction is
modular, and the first test applies if it is real-close. The
case of a real branch tending to the double direction escapes:
In the short-line formula the simple direction is not unused, so
$v_q(x)=-1$ no longer holds, and the flex argument only helps if
$g=0$. Repeated real directions are not priced in general.

## Why the same determinant gives no uniform $q$-factor on the complement

Suppose $C$ is smooth over $\mathbb Q$, $W\le q^{.192}$, and
$\overline C$ is geometrically irreducible. The marked point
$\overline P$ is smooth on $\overline C$. If $H_3$ is squarefree, its
nonzero binary discriminant is $O(W^4)<q$, so every infinity root
remains simple modulo $q$. In the repeated case, the preceding
argument shows that $\overline P$ is at the other, simple direction:
The determinant of the two primitive directions is nonzero and
$O(W)<q$, so they remain distinct. Simplicity at infinity implies
smoothness there, even if $\overline C$ is singular elsewhere.

Use the [marked quotient](jet-quotient-determinant.md), with $r\ge1$
and $m-3\ge r-1$. If a set in the box has more than $3m$ distinct
points, **some maximal minor of the normalized quotient evaluation
matrix is a $q$-unit**. To see this, take primitive coordinates for
$P$ and extend its vector to an integral unimodular basis. In those
coordinates the lattice $K_{m,r}$ has a monomial basis, consisting
of monomials of order at least $r$ at $[0:0:1]$. Thus $K_{m,r}$
reduces onto the entire marked space over $\mathbb F_q$. The reduced
multiples in that space are precisely
$\overline C\,\overline K_{m-3,r-1}$: Vanishing orders add, and the
order of $\overline C$ at $\overline P$ is one. These multiples are
all reductions of the characteristic-zero marked multiples. The
quotient lattice is free by saturation, as in the marked quotient
proof, so this identifies its reduction with the quotient of the
reduced marked space by those multiples.

The points remain distinct modulo $q$ since $2N<q$. The row factors
$l^{-r}$ are units at $q$. If a nonzero quotient class were in the
kernel of all the reduced evaluations, it would give a form of
degree $m$ not divisible by $\overline C$ meeting that irreducible
cubic in more than $3m$ points, contradicting Bézout. The evaluations
therefore have full rank modulo $q$. This rules out a $q$-factor
common to all maximal minors on a large class, not an argument
that prices individual residue classes by other means.

The short-line argument above uses a line through the **actual**
$P$. Merely knowing $q\mid UA+VB$ gives $q\mid Ux_1+Vx_2$ but
not the size bound $|Ux_1+Vx_2|<q$ from a short line equation.
Thus one cannot use that argument to bound the fibers of
projection from $\overline P$ modulo $q$.

## Price and remaining question

Each point costs only divisor-many actual columns. At one prescribed
support per input, use the joint $(h,f)$ enumeration of exponent
$.1276$ from the jet proof. The bounded-occupancy reduction test
costs $q^{.1276+o(1)}$ columns per input; the split-infinity test
eliminates its occupied filters outright. Triples with **both**
columns in the bounded-occupancy family therefore cost
$q^{1.1152+o(1)}$, including $.860$ for the inputs, also after
restriction to the complement of the maximizing region. If each
actual reference instead supplies the support and only its
candidate passes, the sum is $q^{.1276+o(1)} I'$ over the $I'$
references, not the stated both-passing triple bound. Neither
result pays for unrestricted outside-support cofactors.

Next test: On the irreducible reduction, seek structure in the
simultaneous output factorizations, not an additional common
$q$-factor on the whole marked quotient. The infinity test does
not bound occupancy at arbitrary norm and splitting type. The full
maximizing-region complement is still open.
