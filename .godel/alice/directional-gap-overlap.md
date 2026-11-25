# Remove the known overlap from masked gap normals

The [effective-normal count][normals] leaves an interior
survivor only if the reduced normal $a'=a/(a,F)$ overlaps
the relative mask determinant $D/G$. The relevant distinction
is not whether the mask is large. Its primes may be known
from data already charged in the proof, or they may be new.
On new primes, a large common gap scale does not suffice:
The mask must align with a direction of the normal.

Fix the forms and the support per ordered denominator pair on
the same retained list as in [the screen][screen]. Use the
notation of [the effective-normal count][normals], in
particular $a>0$, $h=(a,F)$, $a'=a/h$, $g$ the positive
normal-image generator on $\Lambda_0$, $\lambda=de/g$,
and $I=[P\cap\Lambda_0:L]$. Let $S_*$ be any one pool of
$O(\log q/\log\log q)$ primes fixed across the list (possibly
empty), without a union bound over pools, and set

$$T=\operatorname{supp}(F\lambda)\cup S_*.$$

For an interior mask, write $x,y,x-y$ for the nonzero gaps
and their difference at an actual triple. For each $p\in
S\setminus T$ that divides $a'$, let $r$ and $r+\delta$ be
the smallest and largest valuations among $x,y,x-y$. If
$\delta>0$, the maximum is unique. Set $B_p=c,b,b+c$ when
it occurs at $x,y,x-y$, respectively, and define

$$K_{\rm dir}=\prod_{p\in S\setminus T,\ p\mid a',\ \delta>0}
 p^{\min(v_p(a'),\delta,v_p(B_p))}.$$

Use $v_p(0)=\infty$. The formula is constant on a named
mask group and plane where it matters: Every prime in this
product is prime to $G$, as shown below, so the three full
masked parts specify the three valuations there.
Write $I_T$ for the full part of $I$ on $T$, and let
$Q=[U:W+M]$, where $U$ is the unmasked gap projection,
$W$ the unmasked plane projection, and $M$ the mask lattice.

**Count.** Interior survivors with

$$\frac{Q_{T^c}}{I_{T^c}^2}\le q^{.011} I_T^2 G^{3/2}$$

cost at most $q^{1.13525+o(1)}$ in total. A sufficient gate
is $K_{\rm dir}\le q^{.011} I_T^2 G^{3/2}$. In particular,
all interior survivors with $Q_{T^c}/I_{T^c}^2\le1$
cost $q^{1.1325+o(1)}$. This holds if there is no new
directional overlap, including for any choice of support
inside $S_*\cup\operatorname{supp}(Fde)$, even if the part
on $de$ depends on the denominator pair. This is an
interior count, not a claim that these supports add hits.

## Pay the known primes once

The [effective-normal count][normals] extends as follows.
Allow each named piece to choose any $k\mid a'$ supported on
$T$. For fixed $\kappa\ge0$, pieces with
$a'/(kI^2)\le q^\kappa$ cost $q^{1.055+\kappa/4+o(1)}$.
The prime support of $\lambda F$ has size
$O(\log q/\log\log q)$ since these integers have polynomial
height. After buying **exact** $\lambda$ in its bin
$[J,2J)$ for $q^{o(1)}\sqrt J$, enumerate $k$ at subpower
cost: If $m_T=|T|$ and $L=O(\log q)$ bounds the sum of
exponents in a polynomial-height $k$, there are at most
$\binom{L+m_T}{m_T}=q^{o(1)}$ choices. There is just one
payment for $\lambda$, moved to before the normal box.

The cheap branch $R_L\le100 E G q^{\kappa/2}$ is unchanged
and does not enumerate any $k$ or $\lambda$ globally.
In the expensive branch keep the $R_0\in[R,2R)$ and
$I\in[I_0,2I_0)$ bins, and buy $h\mid F$ by divisors. Use
$n=a'/k\in(X/2,X]$ and transformed coordinates $(n,b,c)$.
The box has radii $(X,Y,Y)$ for $Y=VH/(JR)$. Write
$F'=F/h$ and $N'=qkn+F'(b+c)$. It is the same nonzero $N/h$
as before, and $F'>100a'\ge100n$. The old $A,B$ satisfy
$A\mid c$, $B\mid b$, $(A,B)=1$, $(a',AB)=1$, and
$AB\ge de/(\lambda G)$. In particular $(k,ABF')=1$,
using also $(a',F')=1$.

Take $f\mid AB$ first crossing $4Y\sqrt X$. The reservoir
bound is unchanged with $n$ in place of $a'$: The ratio of
the cutoff to $AB$ is at most
$16\sqrt2 E G q^{\kappa/2}/R_L<1$ since
$\sqrt X<\sqrt2 I q^{\kappa/2}$. The cutoff is greater
than one because $Y\ge Va/H$ and $X\ge1$. All primes of
$AB$ are eligible, and at most one eligible prime is needed
for the overshoot. The number of choices, including the
split $f=f_A f_B$, is $q^{o(1)}(1+\sqrt{4Y\sqrt X})$.
With $f_B\mid b$, $f_A\mid c$, $f\mid N'$, the congruence
lattice still has index $f^2$ since $(qk,f)=1$. Its box
has rank at most two by the same determinant comparison.

The new normal is primitive, so rank one fixes it, hence
$g\mid N'\ne0$ costs subpower. In rank two, fix independent
box vectors $v_1,v_2$ given the charged data
$(h,\lambda,k)$, bins, and split filter. On this filter the
forms $(N'/f,c/f_A,b/f_B)$ are integral. On the actual
normal, $A/f_A$ divides both $N'/f$ and $c/f_A$, since
$A f_B\mid g$ and $A\mid c$; similarly $B/f_B$ divides
$N'/f$ and $b/f_B$. The primitive actual normal extends
to a basis of the filter lattice in the spanned plane.
Changing from that basis to $v_1,v_2$ shows that $A/f_A$
and $B/f_B$ divide the respective fixed minors. For
example, if the first minor vanishes, then

$$qk\det(n,c)+F'\det(b,c)=0.$$

Since $f\mid\det(b,c)$ and $(qk,F'f)=1$, this forces
$F'f\mid\det(n,c)$. Here $f>4Y\sqrt X$ and $F'>100n>50X$,
so $2XY<F'f$, giving zero for both coordinate determinants.
The $c$ column on the span is nonzero: An actual normal with
$c=0$ would give $B\mid qa'$ with $B>1$, impossible by
coprimality. Hence the vanishings contradict independence.
The other minor works with $b,c$ and $A,B$ interchanged.
Once $AB$ is bought, get $G\mid\lambda$, $(g,G)\mid G$, and
$g=AB(g,G)$ by divisors, and recover the ordered pair by
$de=g\lambda$.

Charge only the named pieces on each recovered pair, at
$q^{o(1)}\sqrt{R/I_0}$ each. The total is still bounded by

$$q^{o(1)}\left(\sqrt{JR/I_0}+
 \sqrt{VH}\,(X/I_0^2)^{1/4}\right),$$

now with $X/I_0^2<8q^\kappa$. In particular the enumeration
of possible $k$ is not an enumeration of all divisors of
all possible gap masks before a denominator pair is known.

## Compute the new-prime index

Let $U$ be the unmasked gap projection, $W$ the projection
of the unmasked plane lattice, and $M$ the masked gap
lattice. Thus $I=[W:W\cap M]$. For $p\mid a'$ and $p\mid de$,
$(a',AB)=1$ gives $v_p(g)\le v_p(G)$, so $p\mid\lambda$.
Consequently a prime $p\notin T$ dividing $a'$ is prime to
$deF$. Locally at such a prime $U=\mathbb Z_p^2$ and $W$ is
exactly $bx+cy=0\bmod p^\alpha$, for $\alpha=v_p(a')>0$.
One of $b,c$ is a unit by primitivity.

Take $p\in S\setminus T$ dividing $a'$. Two of the
valuations of $x,y,x-y$ equal their minimum $r$. Thus the
mask at $p$ is $p^r$ times the lattice with one directional
condition $\ell=0\bmod p^\delta$ on the divided gaps,
for $\ell=x,y,x-y$ according to the largest valuation.
When $\delta=0$ choose any direction. Its determinant
exponent is $2r+\delta$. The normal form on a primitive
vector along the line $\ell=0$ is (up to sign) $B_p$.
Complete that vector to a unimodular basis with a vector
on which $\ell$ is one. The image of $M$ under the normal
form is generated by the values on these vectors scaled
by $p^r,p^{r+\delta}$, respectively. Because the normal
form is primitive at $p$, the image ideal has valuation
$r+\min(\delta,v_p(B_p))$. Put $s_p=\min(\delta,v_p(B_p))$ (zero when $\delta=0$).
Then the projection index and mask index have exponents

$$j=v_p(Q)=\min(\alpha,r+s_p),\qquad i=v_p(I)=2r+\delta-j.$$

In particular $i\ge r$ and $j-2i\le\min(\alpha,s_p)-r$.
This cancels the common gap scale in $Q/I^2$: Only the
excess directional divisibility can increase the ratio.
Off $T$, primes not dividing $a'$ have $j=0$, because
$Q\mid[U:W]=(\lambda/G)a$. Primes dividing $a'$ but not
in $S\cup T$ have $i=j=0$, since they are prime to $G$.
Multiplying yields $Q_{T^c}/I_{T^c}^2\le K_{\rm dir}$.

For comparison, on a denominator prime dividing $a'$,
a mask can contribute overlap even at zero local index
cost. To see the exact index, interchange the denominators if
needed so $u=v_p(d)\ge v=v_p(e)$ and put $z=(x-y)/G$.
Locally the unmasked plane imposes

$$N x-FcG z=0\pmod {p^{u+\alpha}},\qquad N=qa+F(b+c).$$

An actual $x$ is a unit at $p$ since $(x,d)=1$. If $c$ were
a nonunit, reducing the equation modulo $p$ would force
$b$ to be a nonunit too, contradicting primitivity. Thus $c$ is a unit
and occupation implies $p^v\mid N$. The plane condition
becomes $z\equiv\tau x\pmod{p^{u+\alpha-v}}$ for a fixed
$\tau$. For $v>0$ the two gaps are units, so only $z$ can
carry a mask condition. For $v=0$ only one of $z,y$ can
carry it, since $x$ is a unit. In the latter $y$ case,
use $y=x-Gz$ with $G$ a unit to get the same form of
congruence on $y$. Denote the masked coordinate by $\phi$
and its mask exponent by $t$. Writing $L_p=u+\alpha-v$,
occupation forces its plane slope to be zero modulo
$p^{\min(t,L_p)}$ and the mask index exponent is
$\max(0,t-L_p)$. This explains why it is useful to pay
these primes from already bought $\lambda$ rather than
assert that $I$ absorbs their overlap.

## Deduction and next test

Since $C/D=(\lambda/G)a/Q$ and $Q\mid(\lambda/G)a$,
choose $k=(a')_T$, so $Q_T\mid h(\lambda/G) k$.
For every interior survivor $C/D<q^{.310}/G^{3/2}$. Hence

$$\frac{a'}{k I^2}<
 q^{.310}\frac{Q}{h(\lambda/G) k I^2G^{3/2}}
 \le q^{.310}\frac{Q_{T^c}/I_{T^c}^2}{I_T^2G^{3/2}}.$$

This proves both counts using $\kappa=.321$ and $.310$,
respectively. They can be combined with the old passing
and interior charges at no increase to exponent $1.13525$.
No reciprocal deletion, coverage gain, or exterior price
is asserted here.

On a prime off $deF$, the primitive normals
$(p^t,1,p^t)$, $(p^t,p^t,1)$, and $(p^t,1,-1)$ show that
the masks $x=0$, $y=0$, and $x-y=0$ modulo $p^t$ can each
have $I$-exponent zero and directional exponent $t$.
These are local congruence examples, not examples of
expensive planes or retained-list triples. The formulas
alone do not bound the aligned factor for arbitrary new
primes. For this box test, an early purchase of an unknown
aligned factor of size $U$ gives no saving at its trivial
$U$ price. In a fixed size bin, dividing $a'$ by the factor
reduces the first radius by $U$, and the directional
congruences on $(b,c)$ supply index $U$. The determinant
crossing for $f$ falls by a factor $U$, giving at most an
$U^{1/2}$ saving in the half-power price. Even a half-power
purchase of the aligned factor just breaks even in this test.
To use this route on the remaining supported interior,
recover aligned factors from other already charged data,
or count their occupation by the actual smooth lifts.
For a known-pool support, the interior price is settled;
address the outside screen separately. The [priced handoff][exterior]
gives the second-row test and its target at each denominator-gcd
scale. Compare additional certified hits on the same retained
list if an admissible export becomes available.

Run `python3 .godel/alice/check-directional-gap-overlap.py`
for the finite local-index and exact exponent checks.

[normals]: effective-gap-normals.md
[screen]: denominator-pair-gap-regions.md
[exterior]: exterior-count-handoff.md#next-useful-test-on-the-same-retained-list
