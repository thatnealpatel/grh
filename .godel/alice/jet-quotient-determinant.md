# Price jet components with a quotient determinant

Use the actual common-input filters of the
[prescribed-product jet proof](prescribed-product-jets.md), and retain
the previously proved [component tests](through-point-components.md).
At fixed $v,h,f$, the affine points $Q=(i,j)$ of interest are in a box
of radius $N=q^{.1348+o(1)}$. The marked point is $P=[A:B:q]$ with
$q\nmid AB$ and $|A|,|B|\le q^{2.2448+o(1)}$. Each actual point has
$l=d/f=q^{.7998+o(1)}$, coprime to $q$, with $l\mid A-qi,B-qj$. The
number of columns over a point is subpower by divisor recovery. The
price of jointly enumerating $(h,f)$, under the prescribed-support
cofactor condition, is still $.1276$ in the exponent.

We prove further occupancy bounds on absolutely irreducible
through-$P$ components of polynomial height. The new feature is to
keep the weighted size of the component in the determinant. This also
works in a rectangle obtained by fixing actual divisibility data.

## The full-rank obstruction

Use a box $|I|\le N_x, |J|\le N_y$, with positive widths at least 1.
Let $K_{m,r}$ denote the integer homogeneous forms of degree $m$
vanishing to order $\ge r$ at the primitive point $P$. Its metric
is Euclidean after substitution $(X,Y,Z)\mapsto(N_xX,N_yY,Z)$.
Put $C$ for the primitive integral component of degree $D$, of
multiplicity $e\ge1$ at $P$, and $H$ for its norm in this metric.
Choose fixed $m,r$ such that $r\ge e$ and $m-D\ge r-e$. Put

$$
B_C=C K_{m-D,r-e}\subset K_{m,r},\quad
b=\binom{m-D+2}{2}-\binom{r-e+1}{2},\quad
a=\binom{m+2}{2}-\binom{r+1}{2}-b.
$$

We use $a>0$. For a set of points on $C$ with $l\ge L_*$ and
$l\mid A-qI,B-qJ$, $(q,l)=1$, use the evaluation functionals
$E_Q(F)=F(I,J,1)/l^r$. These are integral on $K_{m,r}$ by Taylor
expansion, and annihilate $B_C$. Gauss's lemma and additivity of
vanishing order show that $B_C$ is saturated there: An integral form
rationally divisible by $C$ has integral quotient, with the needed
vanishing order. If the evaluations have rank less than $a$, some
nonzero rational form in $K_{m,r}\otimes\mathbb Q$ outside the span of
$B_C$ vanishes on the set. It is not divisible by $C$, so there are at
most $Dm$ distinct points by Bézout.

Otherwise take a nonzero wedge of $a$ evaluations. Its norm is
$\ll_{m,r} L_*^{-ra}$, by the bounds on the box and Hadamard's
inequality. The generator of the top wedge of the integral
annihilator of $B_C$ in $K_{m,r}^*$ has norm
$\det B_C/\det K_{m,r}$. Indeed project onto the orthogonal complement
of $B_C$ in the span of $K_{m,r}$: A basis of $B_C$ extends to a basis
of $K_{m,r}$, and the remaining projected basis has covolume
$\det K_{m,r}/\det B_C$. Its dual is the annihilator. A generator
is primitive in the exterior power of $K_{m,r}^*$ by that same
integral basis extension. Multiplication by $C$ has least singular
value at least $c_{m,D}H$ in the scaled coefficient spaces. After
scaling, multiplication is ordinary polynomial multiplication;
compactness of the unit coefficient spheres and absence of zero
divisors give the uniform positive constant. Hence
$\det B_C\gg_{m,D} H^b\det K_{m-D,r-e}$.

Here is the extra divisibility when one fixes a good divisor $g\mid l$
and one local tangent-root class at each prime dividing $g$. Write
$C$ at $(A/q,B/q)$ in homogeneous affine layers $H_d(x,y)$ starting
at $d=e$. Make a bounded unimodular change of directions so that
$H_e(0,1)\ne0$. Exclude $q$ and the primes where that coefficient is
not a unit or the multiplicities of the geometric roots of
$H_e(1,T)$ are not preserved. Indeed factor the tangent polynomial
into rational squarefree factors of specified multiplicities, clear
$q$ and any other denominators, and exclude primes in the leading
coefficients, discriminants, pairwise resultants, and scalar.
These are fixed nonzero integers of polynomial height: The tangent
polynomial has polynomial height, and primitive factors have
polynomial height by the fixed-degree coefficient product bound.
Write $\mu$ for the maximum geometric tangent multiplicity in
characteristic zero. The shear is only for this local step; the
archimedean metric is unchanged.

At $p^k\parallel g$ the two displacements are in $l\mathbb Z_p$.
The unit $y^e$ coefficient would give a unique lowest-valuation
term if $v_p(x)>v_p(y)$. The displacement is nonzero, so $x\ne0$
and $u=y/x\in\mathbb Z_p$. It satisfies

$$Q_0(x,u)=0,\qquad Q_0(x,U)=\sum_{d=e}^D x^{d-e} H_d(1,U).$$

Fix the root $u\bmod p$ of $H_e(1,U)$ at this prime. Its multiplicity
$t$ is at most $\mu$. Over $\mathbb Z_p[[x]]$, $Q_0$ has a monic factor
$G(x,U)$ of $U$-degree $t$ reducing to $(U-u)^t$ modulo $(p,x)$,
with complementary factor a unit at the chosen points. For detail,
factor at $x=0$ by coprime Hensel lifting (the leading coefficient
there is a unit). If the factors there are $G_0,R_0$, at the $x^n$
step solve $A R_0\equiv E\pmod{G_0}$ for the error coefficient $E$
with $\deg A<t$. Multiplication by $R_0$ on
$\mathbb Z_p[U]/(G_0)$ is invertible modulo $p$, hence invertible.
Use the other correction $(E-A R_0)/G_0$. For $M=\deg_U Q_0$, that
correction has degree at most $M-t$, so the factors have bounded
$U$-degree even when the degree drops at $x=0$. Evaluate the formal
series at $x\in p\mathbb Z_p$; the complementary factor reduces to
a nonzero value at the chosen root, so $G(x,u)=0$.

Writing $F_d$ for the Taylor layers of $F$, reduce each $F_d(1,U)$
modulo the monic $G$. The evaluations then have the common expansion

$$
E_Q(F)=\sum_{n\ge0,\ 0\le j<t} c_{n,j}(F)
             (x/l)^r x^n u^j,
$$

where $c_{n,j}$ are integral $p$-adic linear functionals on
$K_{m,r}$. This follows by reducing
$\sum_{d\ge r}x^{d-r}F_d(1,U)$; the layers below $r$ vanish.
Each multiplier has valuation at least $kn$, without any condition
on how the rest of $l$ varies. In the wedge of $a$ evaluations
nonzero terms require distinct pairs $(n,j)$. Truncate the series
and pass to the $p$-adic limit to obtain the divisor $p^{kV}$ in
every wedge coordinate, where

$$a=\mu s+t',\quad 0\le t'<\mu,\qquad V=\mu\binom{s}{2}+st'.$$

This uses the $a$ smallest weights with $\mu$ slots per level, a
lower bound since $t\le\mu$. Branch choices cost at most
$e^{\omega(g)}=q^{o(1)}$ classes, not a power cost at each prime power.
Combining at all primes, the primitive wedge calculation proves
that full rank requires

$$
 g^V L_*^{ra} H^b\ll_{m,r,D}\frac{\det K_{m,r}}
                                      {\det K_{m-D,r-e}}. \tag{1}
$$

The case $g=1$ is unconditional on the local tangent cone; no local
step or tangent-root partition is needed. The gain at a repeated
tangent is *within* a root class, not across different roots.

The covolume calculation of the jet proof works verbatim with
the diagonal matrix $\operatorname{diag}(1/N_x,1/N_y,1)$. In the
ratio on the right of (1) it gives, up to fixed constants,

$$
(N_xN_y)^S\|(A/N_x,B/N_y,q)\|^{L},\qquad
S=\binom{m+2}{3}-\binom{r+1}{3}-\binom{m-D+2}{3}+\binom{r-e+1}{3},
$$

$$L=\binom{r+1}{2}(m-r+1)-\binom{r-e+1}{2}(m-r-D+e+1).$$

Indeed the determinant of the coefficient scaling contributes the
sum of each coordinate's degrees, and its inverse on the integral
annihilator contributes the opposite sum for the lower jet layers.
The length factor in that calculation is the scaled center's
Euclidean length. Here $L\ge0$ for the uses below (in particular for
all sufficiently large $m$ at the indicated $r/m$).

## Price more uncompressed components

In the original square put $W=H/N^D\ge1$: The nonzero top affine
layer has an integral coefficient of absolute value at least 1.
The center has scaled height at most $q^{2.110+o(1)}$. To cross at
$g\ge q^{.0207}$, first enumerate the full bad-supported part of $l$
at subpower cost. If it exceeds $2N$ it fixes the point, and otherwise
there is enough good part to cross. Count the first-crossing
divisors by the same smooth half-power estimate as in the jet proof
(the eligible-prime cutoff for that estimate is at most
$(\log q)^{2+o(1)}$). The overshoot is subpower. Thus this crossing
with (1) costs $q^{.01035+o(1)}$ per original filter whenever it
bounds the rank. The fixed-support enumeration here and below is
the Rankin argument of the jet proof on $O(\log q)$ primes, not a
smoothness density heuristic.

For $r/m=\rho=1/4$, the coefficient of $m^2$ in the exponent of the
right side of (1) minus its left, using $W\ge1$, is

$$
\Phi_{\tau}(D,e,\mu)=.1348(D-e\rho^2)
+2.110\big[e\rho(1-\rho)+(D-e)\rho^2/2\big]
-.7998\rho(D-e\rho)-\frac{\tau(D-e\rho)^2}{2\mu}
-.1348D(1-\rho^2)/2.
$$

Here $a=(D-e\rho)m+O(1)$, $b=(1-\rho^2)m^2/2+O(m)$,
and $\tau=0$ or $.0207$. Strict negativity permits a sufficiently
large fixed $m$ divisible by 4. In the table, $e:\mu_0$ means that
all $\mu\le\mu_0$ at this $e$ pass. Entries list only $e\le D-2$;
$e=D-1$ already forces geometric genus zero by the plane genus
formula. The tests use the exact displayed decimals.

| $D$ | $\Phi_0<0$ (no crossing) | $\Phi_{.0207}<0$ |
|---:|:---|:---|
| 3 | none | none |
| 4 | none | 1:1 |
| 5 | none | 1:1 |
| 6 | 1:1 | 1:1 |
| 7 | 1:1 | 1:1, 2:1 |
| 8 | 1:1 | 1:1, 2:2 |
| 9 | 1:1 | 1:1, 2:2, 3:1 |
| 10 | 1:1 | 1:1, 2:2, 3:1 |
| 11 | 1:1 | 1:1, 2:2, 3:2, 4:1 |
| 12 | 1:1, 2:2 | 1:1, 2:2, 3:3, 4:1, 5:1 |

For example, the crossing margins at $(D,e,\mu)=(4,1,1)$,
$(8,2,2)$, $(11,3,2)$, and $(12,3,3)$ are respectively
$-7647/320000$, $-7647/160000$, $-74463/640000$, and
$-22941/320000$. Keep the earlier ordinary-point bound at $D\ge7$
for entries it covers but this table does not.

For a smooth cubic use $(m,r)=(10000,1200)$, $e=\mu=1$.
Now $(a,b,S,L)=(28800,49265601,149265601,12000000)$. Write

$$
 U=S/b=149265601/49265601,\quad V_1=ra/b=11520000/16421867,
 \quad V_2=\binom a2/b=138235200/16421867,
$$

$$
 T=.2696U+2.110 L/b-.7998 V_1-.0207 V_2-3(.1348)
   =23533757663/123164002500 < .192.
$$

Thus in the original square $W\ge q^{.192}$ prices the cubic by
(1) with the $.0207$ crossing. This is an occupancy bound, not a
lower bound for $W$ on a cubic that occurs.

## Compress a smooth cubic on fixed bad parts

Only $W<q^{.192}$ needs the following tests. Both axis polynomials
of the [previous cubic test](through-point-components.md#one-paid-test-on-a-smooth-plane-cubic)
are nonconstant and squarefree in this range. To see this, write
$C=H_3(X,Y)+ZH_2(X,Y)+Z^2H_1(X,Y)+Z^3H_0$. This is the expansion by
affine degree, not the Taylor layers at $P$. The first two binary
forms have coefficient sizes $O(W)$ and $O(NW)$. If $H_3$ is
squarefree, its nonzero binary discriminant has size $O(W^4)<q$,
and the binary cubic $C(A V,U,qV)$ reduces to the squarefree form
$H_3(A V,U)$, since $A$ is a unit. The same works using $B$.

Otherwise the repeated line $aX+bY$ is rational: A repeated root
with a distinct Galois conjugate would use degree at least four.
Take $(a,b)$ primitive. If its multiplicity is $j\ge2$, fixed-degree
coefficient product bounds and Gauss's lemma give
$\max(|a|,|b|)^j\ll W$. Smoothness at $[-b:a:0]$ forces
$H_2(-b,a)\ne0$, since both binary first derivatives there vanish.
Its size is $O(NW^{1+2/j})<q$. The scalar of the top factorization
is a unit modulo $q$, and any other top line remains distinct
modulo $q$ by the bound $O(W^2)<q$ on the nonzero determinant of
its coefficients with $(a,b)$. A triple top line is impossible:
$C(A,B,q)=0$ first forces $aA+bB\equiv0\pmod q$, and then its
$ZH_2$ term has valuation one, while the other terms have
valuation at least two. Thus $j=2$.

For the vertical restriction, if $b\ne0$ it is a unit modulo $q$.
The doubled top root is at $U_0=-aA/b$ in the chart $V=1$. After
substitution $U=U_0+T$, the constant term of $C(A,U,q)$ has
valuation one, and its mod-$q$ reduction has a root of multiplicity
two at $T=0$. Coprime Hensel lifting factors off a monic quadratic
reducing to $T^2$, with complementary factor of degree at most one
and a unit at $0$. Use the same error correction as above, now
modulo successive powers of $q$ rather than $x$, starting from
$T^2$ and the complementary reduction. This permits a degree drop
in the complementary reduction. The quadratic's constant term
has valuation one, so it is Eisenstein and separable. Its roots
are integral and reduce to 0, so neither is a root of the
complement. Homogenizing the complement to degree one gives the
remaining simple root, possibly at infinity. If
$b=0$, the doubled direction reduces to $V=0$. The restricted
binary cubic has a factor $V$ over $\mathbb Q$, with the other
factor nonzero there by $H_2(0,1)\ne0$. That quadratic reduces to
two distinct roots, since exactly one copy of the doubled factor
has been removed. Thus the restriction is squarefree in either
case. The horizontal proof exchanges the coordinates. A squarefree
binary cubic dehomogenized in $V=1$ has degree at least two, and
rescaling its affine variable as in the previous test preserves
squarefreeness.

Let $S_x,S_y$ be the corresponding vertical and horizontal bad
supports, from leading coefficient, discriminant, and $q$. Put
$b_x=(A-qi)_{S_x}$ and $b_y=(B-qj)_{S_y}$ for the **full** supported
parts of the unnormalized outputs. These parts cost subpower to
enumerate separately or jointly for the fixed curve. If either
chosen part exceeds $2N$, it fixes its coordinate and there are
at most three points by Bézout with the coordinate line.

For a single-axis test fix $b_x=b$, and also fix $d_0=l_{S_x}\mid b$
at subpower cost. For the joint test fix $b_x,b_y$, and fix
$d_0=l_{S_x\cup S_y}\mid\operatorname{lcm}(b_x,b_y)$ at subpower
cost. In each case use $l'=l/d_0$. For the single-axis test choose
compression factors $(B_x,B_y)=(b,d_0)$, and for the joint test use
$(B_x,B_y)=(b_x,b_y)$. Fix the centered residues $i_0,j_0$ of the
coordinates modulo $B_x,B_y$ by the congruences to $A/q,B/q$. Write
$i=i_0+B_x I$, $j=j_0+B_y J$. The compressed box has widths
$N_x\asymp N/B_x$, $N_y\asymp N/B_y$ (increase by a bounded factor
and clip at 1). Its marked point is primitive with coordinates
$((A-qi_0)/B_x,(B-qj_0)/B_y,q)$, since both first coordinates
are integral and units modulo $q$. The scaled height bound is
still $q^{2.110+o(1)}$. The divisibilities by $l'$ persist after
compression because $l'$ is prime to $B_x B_y$.

The transformed cubic is $C(i_0Z+B_xX,j_0Z+B_yY,Z)$; divide by its
positive coefficient content $c$. Its weighted norm is comparable
to $N^3W/c$: Once the metrics are scaled, the affine translation
and dilation have bounded operator norms and inverses in degree
three. The compressed cubic is again smooth, through the marked
point, primitive, and of polynomial height. For its determinant
crossing choose good primes of the compressed curve at that point
as in (1). Enumerate the full new bad part of $l'$ at subpower
cost. If that part exceeds twice the larger compressed width it
fixes both coordinates, and otherwise there is enough good part
for the crossing: Here $d_0\le2N$ in the single-axis test and
$d_0<q^{.073}$ in the joint anisotropic case below, so $l'$ is
still at least $q^{.665-o(1)}$. This additional bad-part split
costs no fixed power.

Set $w=\log_q W$, $\gamma=\log_q c$, $\lambda=\log_q d_0$, and
$\beta_x=\log_q B_x$, $\beta_y=\log_q B_y$. Substituting the
compressed widths, $L_*=q^{.7998-\lambda-o(1)}$, and the compressed
cubic norm in (1), full rank is impossible if the following exceeds
$T$ by a fixed positive constant:

$$w-\gamma+U(\beta_x+\beta_y)-V_1\lambda. \tag{2}$$

The asymmetric content bounds are important: An undifferentiated
bound on $c$ by a cubic power of the larger compression can lose
the entire gain.

* **One large bad part.** Use the single-axis compression with
  $\beta=\log_q b$, so $\beta_x=\beta$ and $\beta_y=\lambda\le\beta$.
  According as $[0:1]$ has multiplicity 0, 1, or 2 in $H_3$, the
  coefficient of $Y^3$, $XY^2$, or $Y^2Z$ in the transformed cubic
  gives respectively
  $$c\ll d_0^3 W,\qquad c\ll b d_0^2 W,\qquad c\ll d_0^2 N W.$$
  For multiplicity 2 the top layer has $Y$-degree at most one,
  so it makes no contribution to $Y^2Z$, and smoothness gives
  $H_2(0,1)\ne0$. Multiplicity 3 has already been excluded. Since
  $U-V_1-3<0<U-V_1-2$, the respective lower bounds in (2) are
  $(2U-V_1-3)\beta$, $(U-1)\beta$, and $U\beta-.1348$, up to
  $o(1)$. With $\beta\ge.108$, all exceed $T$; the smallest
  margin is $16544707/12316400250>.0013$. Likewise for the other
  axis, interchanging $X,Y$.
* **Two moderately large bad parts.** Suppose $b_x,b_y\ge q^{.080}$.
  If $d_0\ge q^{.073}$, compress both axes by $d_0$ instead,
  fixing their centered residues; if $d_0>2N$ there is just one
  point. Otherwise the width exponent is at most $.0618$ and
  $l'\ge q^{.665-o(1)}$. The usual smooth-point determinant in
  the compressed square crosses with $.0207$ since
  $3(.0207)>.0618$. As above, enumerate its residual bad part first,
  and stop when it already fixes the point. If $d_0<q^{.073}$ use
  the joint anisotropic compression. For any nonzero monomial
  $X^jY^{3-j}$ of $H_3$, $c\ll W B_x^j B_y^{3-j}$. Since $U>3$,
  (2) is at least $(2U-3)\min(\beta_x,\beta_y)-V_1\lambda-o(1)$.
  At $\min(\beta_x,\beta_y)=.080$ and $\lambda=.073$ the
  margin over $T$ is $305922137/123164002500>.0024$.

Thus either one bad part at least $q^{.108}$, or both at least
$q^{.080}$, costs $q^{.01035+o(1)}$ per original filter. The
compressed center and curve were held fixed when counting the
first-crossing divisors; a varying bad part is not treated as one
common compressed curve.

## What this removes, and what it does not

Run `python3 .godel/alice/check-jet-cubic-price.py` from the repository
root to reproduce the finite cubic constants, five margins, joint
isotropic fallback, and total budget in exact arithmetic. This is
an arithmetic baseline, not a check of either determinant estimate.
See [the handoff decision](jet-price-handoff-decision.md) for the
remaining modulus test.

The new tests cost at most $.1276+.01035=.13795<1121/8125$ in
column exponent at a fixed actual input, under the same joint
cofactor and first-divisor rule. Add them to the earlier tests
at that price. With one prescribed support per input, ordered
triples with both columns priced still cost
$q^{.860+2(1121/8125)+o(1)}$. With all references, the one-sided
price is still $q^{1121/8125+o(1)}I'$ rather than a stand-alone
triple bound.

For a smooth cubic left over, $W<q^{.192}$, both axis fibers are
squarefree, both bad parts are below $q^{.108}$, and one is below
$q^{.080}$. Neither good part passes an applicable preassigned
supported-credit test. The next useful cubic question is whether
the simultaneous smooth lifts force an additional bound **within**
that small-bad, low-credit class; no lower bound on either bad
part is proved here. The unpriced multiplicities in the table,
and the large outside-support cofactor family, also remain open.
