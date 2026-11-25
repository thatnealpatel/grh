# Count small effective normals on masked gap planes

The [widened gap screen][screen] prices the passing triples,
not its complement. A survivor inside the outer width has a
nonvertical gap plane of small projected covolume relative
to its mask. On the subfamily below, the first rows alone
already pay for these survivors. This does not use reciprocal
retention to delete any triples or assume a hit-rate gain.

## Statement

Fix one actual ordered two-label list in $g=R=j=1$. Use
$F=F_1=q^{.780+o(1)}$, $V=q^{1.720+o(1)}$, and
$H=q^{.390+o(1)}$. Write a triple as $(m,x,y)$ at an ordered
denominator pair $(d,e)$, so that

$$Fm=dY_1+qx=eY_2+qy,\quad 0<m\le V,\quad |x|,|y|\le H.$$

Here $q$ is prime, $(q,F)=1$, $(qF,de)=1$, $d,e$ are
$q^{1.055+o(1)}$, and $d,e,m$ are eligible-smooth. The eligible
prime cutoff is $O((\log q)^2)$. Smooth integers up to a
polynomial bound $U\ge1$ number at most $q^{o(1)}\sqrt U$,
by the [half-power bound][smooth]. We use $(m,x)=1$ and at
most one actual triple at fixed $(d,e,m)$. Write $G=(d,e)$.
The number of ordered pairs with $G\asymp K$ is at most
$q^{1.055+o(1)}/\sqrt K$, by buying the smooth gcd and its
two smooth quotients.

For each pair, name at most $q^{o(1)}$ pieces. A piece is
a nonvertical plane $P$ through zero with primitive normal
$(a,b,c)$ of polynomial height, oriented by $a>0$, and a
full-rank sublattice $L$ of polynomial index $I$ in
$P\cap\Lambda_0$. Here $\Lambda_0$ is the unmasked congruence
lattice $Fm\equiv qx\pmod d$, $Fm\equiv qy\pmod e$. Count
only actual triples in the named lattices. Put

$$h=(a,F),\qquad a'=a/h,\qquad \Xi=a'/I^2.$$

**Claim.** For each fixed $\kappa\ge0$, the total count on
pieces with $\Xi\le q^\kappa$ is at most
$q^{1.055+\kappa/4+o(1)}$. Neither $I$ nor the plane has to
be uniform over pairs. The proof adapts the [two-minor
recovery][minors] for coprime visible splits to noncoprime
denominators, and charges the smaller occupancy on $L$.

## Local price and cheap pieces

Let $g>0$ generate the image of the normal on $\Lambda_0$,
and put $\lambda=de/g$. The index of $\Lambda_0$ in
$\mathbb Z^3$ is $de$, by varying $x,y$ independently at
fixed $m$. Primitivity of the normal gives the index identity
$[P\cap\mathbb Z^3:P\cap\Lambda_0]=\lambda$, by the exact
sequence of the kernel and image. In particular $g\mid de$.
The gap projection of $P\cap\Lambda_0$ has covolume
$\lambda a$, since $a\mid bx+cy$ has index $a$ in the gap
coordinates. Thus $C=I\lambda a$ is the projected covolume
for $L$. Define

$$R_0=\frac{VH^2}{\lambda\|(Va,Hb,Hc)\|_2},
\qquad R_L=R_0/I.$$

After scaling by $(1/V,1/H,1/H)$, the plane lattice $L$
has covolume $1/R_L$: For the primitive integral plane the
unscaled covolume is the length of its normal, and scaling
the area vector applies the inverse transpose times the
scaling determinant.

An occupied piece costs $q^{o(1)}(1+\sqrt{R_L})$ actual
triples. If the image of the $m$ coordinate is $j_0\mathbb Z$,
then $j_0>0$ on an occupied piece. Enumerate the smooth
$m/j_0\le4\max(1,R_L)$, recovering $m$. Otherwise buy a
smooth divisor $f$ of $m/j_0$ strictly crossing that cutoff,
with overshoot at most one eligible prime. Divisibility of
the **divided** coordinate has index $f$ in $L$, so the
scaled covolume of the filtered lattice is $f/R_L>4$.
Two box vectors have mutual area at most $3$ after scaling.
Thus the points in any one filter lie on a line through
zero, with at most one having $m>0$ and $(m,x)=1$. This
uses primitivity on the actual triples, not a claim that
all lattice points are primitive.

Take $E=q^{o(1)}$ uniform and at least
$\max(1,VH/(de),H^2/F)$ for all pairs. If
$R_L\le 100 E G q^{\kappa/2}$, the local price and the
pair count in a gcd bin give $q^{1.055+\kappa/4+o(1)}$,
including the subpower number of named pieces per pair.
In fact this cheap bound holds without imposing any
condition on $\Xi$.

## Expensive pieces: Force rank loss in a normal box

Set $N=qa+F(b+c)$. Evaluation on $(q,F,F),(0,d,0),(0,0,e)$
gives $g\mid N,bd,ce$. If a prime has larger valuation in
$g$ than in both $d$ and $e$, it divides $b,c$, and then
$a$ since it is prime to $q$. Thus $g\mid\operatorname{lcm}(d,e)$
and $G\mid\lambda$. Write

$$A=g/(g,e),\qquad B=g/(g,d),\qquad
AB=g/(g,G).$$

The last equality and $(A,B)=1$ follow prime by prime.
We have $A\mid c$, $B\mid b$, $A\ge d/\lambda$, and
$B\ge e/\lambda$. Also $(a,AB)=1$: A prime of $A$ divides
$c$ and $N$, so if it divides $a$, it divides $b$ since
it is prime to $F$. Interchange sides for a prime of $B$.

The size constraint $\lambda R_0 a\le H^2$ now gives
$\lambda\le H^2$ and $A,B>1$. If $N=0$ then $F\mid a$,
forcing $R_0\le H^2/F$, contrary to the expensive cutoff.
Buy $h\mid F$ at divisor cost before setting $F'=F/h$.
The transformed normal $(a',b,c)$ is primitive, and
$N'=qa'+F'(b+c)=N/h\ne0$ is divisible by $g$, since
$(h,g)=1$. Also

$$F'\ge (F/H^2)\lambda R_0 a'>100a'.$$

Bin $\lambda\in[J,2J)$, $R_0\in[R,2R)$, $a'\in(X/2,X]$,
and $I\in[I_0,2I_0)$. The transformed normal lies in the
box of radii $(X,Y,Y)$ with $Y=VH/(JR)$. Set $D_*=4Y\sqrt X$.
Here $D_*>1$ in an occupied bin, since $Y\ge Va/H$.
Choose a divisor $f$ of $AB$ first crossing $D_*$: Indeed
$AB\ge de/(\lambda G)$, and

$$\frac{D_*}{AB}
\le 16\frac{VH}{de}\frac{G\sqrt X}{R_0}
\le 16\sqrt2\, E\frac{G q^{\kappa/2}}{R_L}<1.$$

The second inequality uses $\sqrt X<\sqrt2 I q^{\kappa/2}$.
All prime factors of $AB$ are eligible since $AB\mid g\mid de$.
The overshoot is at most one eligible prime. Split $f=f_Af_B$
with $f_A\mid A$, $f_B\mid B$. Counting the smooth product
and splitting at divisor cost names at most
$q^{o(1)}(1+\sqrt{D_*})$ filters.

The normal box in the filter lattice

$$L_f=\{(a',b,c)\in\mathbb Z^3:
 f_B\mid b,\ f_A\mid c,\ f\mid qa'+F'(b+c)\}$$

has rank at most two. The index is $f^2$: The coordinate
conditions cost $f$, then the last condition costs another
$f$ by varying $a'$ since $(q,f)=1$. A nonzero determinant
of three box vectors would be a multiple of $f^2$, but has
absolute value at most $6XY^2<f^2$.

## Recover ordered denominator pairs before charging pieces

Rank zero is unoccupied. Rank one fixes the primitive
positive-$a'$ normal, so $g\mid N'\ne0$ costs subpower.
In rank two fix any two independent box vectors $v_1,v_2$
once for this bin, $h$, and filter. On $L_f$ the forms
$k=N'/f$, $\gamma=c/f_A$, and $\beta=b/f_B$ are integral.
On an actual transformed normal $n'$, the quantities
$h_A=A/f_A$ and $h_B=B/f_B$ divide $(k,\gamma)(n')$ and
$(k,\beta)(n')$, respectively, in both coordinates.
The primitive $n'$ extends to a basis of $L_f$ intersected
with the span: Its coefficients in any integral basis have
gcd one, since otherwise it would be divisible in
$\mathbb Z^3$. By changing from that basis to $v_1,v_2$,
we obtain

$$h_A\mid\det(k,\gamma)(v_1,v_2),\qquad
h_B\mid\det(k,\beta)(v_1,v_2).$$

The minors are fixed and of polynomial height. Neither
vanishes in an occupied filter. In fact if the first
vanishes, then, on $v_1,v_2$,
$q\det(a',c)+F'\det(b,c)=0$. Since $f\mid\det(b,c)$ and
$(q,F'f)=1$, this forces $F'f\mid\det(a',c)$. But
$|\det(a',c)|\le2XY<F'f$, using $F'>50X$ and
$f>4Y\sqrt X$. Both coordinate determinants vanish.
An actual normal with $c=0$ would give $B\mid qa'$ from
$B\mid b,N'$, contradicting $B>1$ and $(a',B)=1$. So
the $c$ column on the span is nonzero, and the vanishings
would make all coordinate columns proportional, against
independence. Interchanging $b,c$ and $A,B$ treats the
second minor.

Thus $AB=f h_A h_B$ is recovered at divisor cost. Enumerate
the smooth $\lambda$ in its bin at $q^{o(1)}\sqrt J$ cost.
In rank two, enumerate $G\mid\lambda$ and $\delta\mid G$
at divisor cost to recover $g=AB\delta$, using
$\delta=(g,G)$. In either rank, recover $(d,e)$ from
$de=g\lambda$ at divisor cost. There is no extra smooth
$G$ enumeration. For each recovered pair charge only the
$q^{o(1)}$ **named pieces**, not every normal in the box.
The local occupancy is $q^{o(1)}\sqrt{R/I_0}$ in this
expensive branch. Consequently the total per bin is at
most

$$q^{o(1)}\left(\sqrt{JR/I_0}
  +\sqrt{VH}\,(X/I_0^2)^{1/4}\right).$$

Here $JR\le H^2$, and $X/I_0^2<8q^\kappa$ in an occupied
bin. All heights and bin endpoints are polynomial, so the
sum of bins and the $h$ enumeration are subpower. As
$\sqrt{VH}=q^{1.055+o(1)}$, this proves the claim.

## Apply to the widened-screen complement, inside its prism

Fix the forms $u,w$ and support $S$ per pair on the
inherited retained population in [the screen][screen].
The named-piece theorem itself did not need the inherited
$G$ cap. Neither this application nor the theorem pays
for the earlier reciprocal deletions on the original list.
Write $s=|x|_S$, $t=|y|_S$,
$l=G(|x-y|/G)_S$, and $D=stl/(s,t,l)$. A piece is the
nonvertical plane of the outer prism for the mask and
$|u|$ bin, with $L$ the **whole** masked lattice on the
plane. The plane comes from two independent vectors at
polynomial height. There are subpower many pieces per
pair: Given $|S|=O(\log q/\log\log q)$, distributing
$O(\log q)$ exponents on $S$ costs $q^{o(1)}$ by the
binomial bound, and there are logarithmically many bins.
The unmasked gap projection has index $G$ in $\mathbb Z^2$,
and the mask lattice is inside it with relative index
$D/G$. Intersecting with the unmasked plane projection
shows $1\le I\le D/G$. In particular $I=1$ for $S$ empty.

For an interior survivor the screen gives
$C/D<T_1/T_0=q^{.310}/G^{3/2}$. Since $C=I\lambda a$,

$$\Xi=\frac{C}{h\lambda I^3}
 < q^{.310}\frac{D/G}{h(\lambda/G) I^3 G^{3/2}}.$$

* With empty support $D=G$, all interior survivors cost
  $q^{1.1325+o(1)}$, using $\kappa=.310$.
* For any fixed support choice, the sufficient gate
  $D/G\le q^{.011}h(\lambda/G) I^3 G^{3/2}$
  costs $q^{1.13525+o(1)}$, using $\kappa=.321$. This
  includes the simpler $D/G\le q^{.011}G^{3/2}$.
* One can also discard all pieces with $\Xi\le q^{.321}$
  or $R_L\le100 E G q^{.1605}$, regardless of that gate,
  at the same exponent. Any remaining interior piece has
  both strict reverse inequalities. Then
  $H^2\ge\lambda R_0a=\lambda R_L h I^3\Xi$ implies
  $h(\lambda/G) I^3 G^2<q^{.2985+o(1)}$.

There is also a necessary arithmetic overlap in that
residual. In the unmasked gap lattice of index $G$, write
$W$ for the unmasked plane projection and $M$ for the mask
lattice. Since $[W:W\cap M]=I$, the index of $W+M$ is
$(D/G)/I$, which divides both $D/G$ and $(\lambda/G)a$.
It follows that

$$D/G\le I h(\lambda/G)(a',D/G),\qquad
\Xi<q^{.310}\frac{(a',D/G)}{I^2G^{3/2}}.$$

In particular the remaining interior requires
$(a',D/G)>q^{.011} I^2 G^{3/2}$. Large masks with little
common part with the reduced normal do not obstruct this
count. This is an index constraint, not a count of the
pieces with large overlap.

Run `python3 .godel/alice/check-effective-gap-normals.py`
to replay the thresholds and finite CRT index tests. The
exact-rational test also gives an exponent tuple satisfying
the necessary residual inequalities. Those inequalities
alone do not contradict each other; this does not provide
an admissible plane or an actual triple.

## Remaining decision at target $1.1354$

First-row counting suffices for the interior subfamily
above. The entire empty-support interior, including the
passing set, is paid, but its outer cutoff is only
$|\det(u,w)|q^{.470}\sqrt G$. A prescribed nonempty support
can enlarge that cutoff by $D/G$ at a triple. With the forms
held fixed, one can **keep** the empty-support charge and add
the supported passing and certified interior charges; the
union still costs $q^{1.13525+o(1)}$. Thus a supported
choice need not replace the empty choice or sacrifice any
of its charged triples. No actual added coverage follows.

For a coverage comparison, keep the same actual retained
list and fixed forms. Among the empty-support outside
triples, count how many pass the supported screen or move
inside onto a piece with certified price. The remaining
triples, both supported outside and uncertified supported
interior, still need a count. The [directional-index
extension][directional] removes all known-prime overlap at
no extra power of $q$ and identifies the remaining alignment
at new primes. Exact second-output ratio recovery on any
unpriced population still needs a census of occupied ratios.
There is no radius comparison here.
The [fixed-plane replay][fixed-plane] rules out a uniform
price on arbitrary unmasked planes, not on the retained
named pieces above.

[directional]: directional-gap-overlap.md
[fixed-plane]: fixed-plane-price-decision.md
[minors]: normal-factor-minors.md
[screen]: denominator-pair-gap-regions.md
[smooth]: shared-complement-count.md
