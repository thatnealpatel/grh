# Pay all exceptional visible splits at exponent 1.1345

On one unchanged actual ordered two-label list in the scope of the
[global double ratio](global-double-ratio.md), all retained triples on
exceptional visible splits cost $q^{1.1345+o(1)}$. This replaces the
$1.1355$ exceptional charge, which was too large for the $1.1354$
triple budget. It does not count ordinary triples or prove occupancy of
the common-input second rows. The proof buys a smaller filter by using
degree eight for confinement and degree twelve for the norm of any
low-degree component with many represented normals.

## Existing inputs and the smaller filter

Use the [two-minor notation](normal-factor-minors.md). Write $F=F_1$,
$Q=Q_0$, $V=q^{1.720+o(1)}$, $H=q^{.390+o(1)}$. A visible split
consists of coprime eligible-smooth $P,Q\ge q^{1.212-o(1)}$ prime to
$Fq$. The lattice is $Fm\equiv q\alpha\pmod P$,
$Fm\equiv q\alpha_0\pmod Q$ in the $(V,H,H)$ box. Actual triples give
primitive vectors, and the complete input $v=Fm$ and the two resulting
outputs recover their ordered prefixes. Exceptional splits have box
rank two, primitive oriented normal $(a,b,c_0)$ with $a>0$, image
index $g$, $\lambda=PQ/g$, and
$0<|\ell|=|(qa+F(b+c_0))/g|\le q^{.020+o(1)}$. Here

$$R_0=\frac{VH^2}{\lambda\|(aV,bH,c_0H)\|_2}>q^{.446}.$$

At fixed split there are at most $q^{o(1)}\sqrt{R_0}$ actual triples
by the divided $m$-projection sieve of the global double ratio proof.
In dyadic bins $R\le R_0<2R$, $J\le\lambda<2J$ put $T=RJ=q^\sigma$,
$r=\log_q R$, $j=\log_q J$, $X=H^2/T$, and $Y=VH/T$. Fix $s=(F,a)$
at divisor cost. The primitive transformed normal $(a',b,c_0)$, with
$a'=a/s$ and $F'=F/s\ge q^{.760-o(1)}$ (since $s\mid\ell$), lies in
the $(X,Y,Y)$ box and satisfies $(a',g)=1$. Put $A=(P,g)$, $B=(Q,g)$.
Then $AB=g$, $A\mid c_0$, $B\mid b$, and each of $A,B$ is at least
$q^{1.212-j-o(1)}$.

Set $\tau=.159$. If $\sigma\ge .462$, use the existing two-minor
bound $q^{1.055+o(1)}X^{1/4}$, which is at most $q^{1.1345+o(1)}$.
For $.446-o(1)\le\sigma\le .462$ choose divisors $f_A\mid A$ and
$f_B\mid B$ at the first crossings of $\sqrt{Yq^\tau}$ on each side.
Here $j\le .016+o(1)$, each side is at least $q^{1.196-o(1)}$, and the
crossing threshold is at most $q^{.9115+o(1)}$. The eligible prime
ceiling is $O((\log q)^2)$, so the overshoots are subpower. With
$d=f_Af_B=Yq^{\tau+o(1)}$, let

$$L_d=\{(a',b,c_0)\in\mathbb Z^3:
 f_B\mid b,\ f_A\mid c_0,\ d\mid qa'+F'(b+c_0)\}.$$

Its index is $d^2$ by solving the last congruence in $a'$ using
$(q,d)=1$. The relative determinant parameter is
$XY^2/d^2=q^{\psi+o(1)}$ for $\psi=.780-2\tau-\sigma=.462-\sigma$.
In integral coordinates

$$w=(K,C,B_0)=((qa'+F'(b+c_0))/d,c_0/f_A,b/f_B)$$

write $h_A=A/f_A$, $h_B=B/f_B$. On actual normals $h_A\mid K,C$ and
$h_B\mid K,B_0$. Each is at least $q^{.28-o(1)}$ by the above upper
bound on the factors and the lower bound on $A,B$. Also

$$h_Ah_B=PQ/(\lambda d)\ge q^{.314+r-\tau-o(1)}
\ge q^{.760-\tau-o(1)}.$$

Reduction modulo primes of $h_A$ shows $(h_A,B_0)=1$: If such a prime
divides $B_0$, then it divides both $b,c_0$ and $g$, so the normal
identity gives $p\mid a'$, a contradiction. Likewise $(h_B,C)=1$.

If the represented normals span at most a plane, the two-minor
argument gives divisor-many $g$ using two independent representatives
in the rank-two case; ambient lattice points outside their plane do
not matter. The required inequality $dF'>2XY$ follows from
$d/Y=q^{\tau+o(1)}$, $F'\ge q^{.760-o(1)}$, and
$X\le q^{.334+o(1)}$. A primitive line supplies one oriented normal,
whose nonzero $qa'+F'(b+c_0)$ gives $g$ at divisor cost. Below assume
three independent represented normals in the filter.

## Degree eight excludes large components

Set $E_A=[0:0:1]$, $E_B=[0:1:0]$ in $w$ coordinates. Put
$u=.780-\tau$, $v_0=(2.110-\tau-\sigma)/2$. The three coordinate
bounds have exponents $(u,v_0,v_0)$. The shear

$$K'=K-F'(f_A C+f_B B_0)/d=qa'/d$$

has bound $q^{u-1.110+o(1)}$ on actual normals and belongs to
$q\mathbb Z_{(q)}$. The two shear coefficients have size at most
$q^{u-v_0+o(1)}$.

Suppose 37 degree-eight evaluation rows of actual normals are
independent modulo the two coordinate evaluation rows. Complete
these 39 rows by six evaluation rows on the grid of combinations
with coefficients $0,\ldots,8$ of three independent actual $w$.
Successive interpolation under this invertible linear substitution
shows that the grid spans the full evaluation dual. These six rows
are not represented rows, but their coordinate and shear bounds
hold up to a fixed constant, including the $q$-divisibility of $K'$.

In the resulting square determinant $\Delta$ of size 45, expand
on the two unsheared coordinate rows. This deletes the pure powers
$B_0^8,C^8$. Every other monomial at an actual row has the divisor
$h_Ah_B$: It either contains $K$ or contains both $C$ and $B_0$.
Thus the product of the 37 actual row divisors divides $\Delta$.
No omitted-factor divisibility is used on the six grid rows.

Separately, shear the full monomial basis, a determinant-one column
operation over $\mathbb Q$ and over $\mathbb Z_{(q)}$. In each
monomial column use unthinned weight $q^{u\deg K'+v_0(8-\deg K')}$.
Each variable's total degree over the columns is 120. For a coordinate
row the bound improves by $q^{-8v_0+o(1)}$ relative to each column's
weight: The two unchanged coordinates have size at most one and
$K'$ has size at most $q^{u-v_0+o(1)}$. On every other row the entry
improves by $q^{-1.110\deg K'+o(1)}$ and has the $q$-adic factor
$q^{\deg K'}$. In a determinant term the coordinate rows use distinct
columns of combined $K'$-degree at most $8+7=15$. Hence $q^{120-15}$
divides $\Delta$, coprime to the product of actual row divisors. After
dividing by both integer divisors, the absolute determinant has
exponent at most

$$\psi\,120+2.110(15)-(2.110-\tau-\sigma)8-(.760-\tau)37+o(1).$$

At $\sigma=.446$ this is $-.707+o(1)$, and the affine part decreases
with slope $-112$. This contradicts a nonzero determinant. Thus the
actual and coordinate evaluation rows have rank at most 38, and their
null forms have dimension at least seven.

Choose one nonzero null form with polynomial-height integer
coefficients using fixed-size minors. Its irreducible rational factors
also have polynomial height by the fixed-degree factor bound in the
[sextic proof](cheap-filter-sextic.md). Any factor of degree $e\ge6$
has a space of multiples of dimension at most six in degree eight,
so another null form is not divisible by it. The two have at most
$8e$ common projective points on that factor by Bézout; rational
irreducibility suffices since a shared geometric factor would bring
all its conjugates. A factor missing $E_A$ has nonzero evaluation
there divisible by $h_A$ for every represented point on it, by
reduction modulo $h_A$ and the unit $B_0$. Thus $h_A$ is determined up
to divisor cost. Enlarging $f_A$ by this factor multiplies the lattice
index by $h_A^2$, which exceeds $6XY^2/d^2=q^{\psi+o(1)}$. Three
independent vectors in the box would have determinant divisible by the
new index but smaller in magnitude. Rank at most two is payable by
the same minors, with the enlarged filter. The argument at $E_B$ is
symmetric. The line through both points is $K=0$, absent from the
actual set since $\ell\ne0$.

## Norm bound for degrees two through five

Work in the real scaled coordinates $\xi=(a'/X,b/Y,c_0/Y)$ and the
scaled lattice $\Gamma=\operatorname{diag}(1/X,1/Y,1/Y)L_d$ of
covolume $\delta=d^2/(XY^2)$. Let $G$ be an irreducible rational
component of degree $2\le e\le5$ through both coordinate points,
normalized primitive integral in a basis of $\Gamma$. The changes
between that basis and the $w$ coordinates are rational. All norms
below are real coefficient norms in the $\xi$ monomials.

The lattice of degree-twelve forms integral in the $\Gamma$ basis
has covolume $\delta^{-364}$: The determinant of monomial
substitution is the determinant of linear substitution raised to
the sum $\binom{14}{3}=364$ of each variable's degrees. Evaluate on
a maximal independent set of degree-twelve evaluation rows of actual
points on $G$, using their bounded representatives in $\Gamma$.
The evaluation map has bounded real Jacobian on the orthogonal
complement of its kernel, by the bounded box and fixed degree. Its
image lattice is full rank in the integer output space and has
covolume at least one. Thus the kernel lattice has covolume
$O(\delta^{-364})$: Extend a basis of the kernel lattice by lifts
of an image basis, and compute their perpendicular volume using
the evaluation Jacobian. Its dimension is at least
$\binom{14-e}{2}\ge36$, by multiples of $G$. Minkowski supplies a
nonzero integral form $D$ vanishing on all actual points on $G$
with $\|D\|_\xi\le q^{(91/9)\psi+o(1)}$.

If there are more than $12e$ projective points, Bézout forces
$D=GU$, with $U$ integral in the lattice basis by Gauss's lemma.
To bound $\|U\|_\xi$ from below, evaluate on the grid of bounded
integer combinations (coefficients $0,\ldots,12$) of three independent
actual normals anywhere in this filter. Interpolation gives a nonzero
evaluation, which is an integer and hence has absolute value at least
one. The grid lies in a fixed bounded region in $\xi$ coordinates.
Thus $\|U\|_\xi\gg1$, and fixed-degree norm comparison
$\|GU\|_\xi\gg\|G\|_\xi\|U\|_\xi$ (compactness on unit spheres and
no zero divisors) gives $\|G\|_\xi\le q^{(91/9)\psi+o(1)}$.

Restrict $G$ to the line $K=0$. An integral basis of the corresponding
plane lattice in unscaled coordinates is

$$v_1=(0,d,-d),\qquad v_2=(F',b_2,c_2),\quad b_2+c_2=-q,$$

where $f_B\mid b_2$, $f_A\mid c_2$, and $|b_2|\le d$ by CRT.
Indeed, $K=0$ forces $F'\mid a'$, after which subtracting a multiple
of $v_2$ leaves a multiple of $v_1$. The scaled norms are at most
$q^{\tau+o(1)}$ and $q^{\sigma+o(1)}$, respectively, since
$F'/X\le q^{\sigma+o(1)}$ and $(q+d)/Y\ll q^{\tau+o(1)}$.
The restricted integral binary form in this basis is nonzero by
irreducibility. It has the two primitive integral linear factors

$$-f_B x_1+(c_2/f_A)x_2,\qquad f_A x_1+(b_2/f_B)x_2,$$

which vanish at the two coordinate points on this line. Primitivity
follows by reduction modulo the respective opposite filter (the
numerators reduce to $-q$), and their coefficient determinant is $q$.
Their product times a nonzero *integral* binary form gives the
restriction, by Gauss's lemma. If the residual form first has a
nonzero coefficient at $x_2$-degree $i\le e-2$, the corresponding
first nonzero coefficient in the restriction is a nonzero integer
multiple of $-d$. Its magnitude is at least $d$ but has exponent
at most

$$ (91/9)\psi+(e-i)\tau+i\sigma+o(1)
\le (91/9)\psi+2\tau+3\sigma+o(1).$$

At $\sigma=.446$ the last affine bound is $409/225$, below the
exponent $1.823$ of $d$ by $47/9000$. The gap grows with slope $55/9$
in $\sigma$. This contradicts the many-points hypothesis, so each
such component has at most $12e$ represented projective points.

## Sum and pass the rest back to the actual rows

There are only boundedly many factors. Across all layers of a filter,
each fixed projective point fixes one primitive oriented normal, and
its nonzero normal evaluation gives divisor-many $g$. Together with
the minor recovery cases this gives $q^{o(1)}$ distinct represented
$g$ per filter. No auxiliary equation or interpolation basis is
charged separately. The ordered filters cost $q^{o(1)}\sqrt{Yq^\tau}$
by counting the eligible-smooth product at half power and splitting
it by divisors. For each $g$ enumerate $\lambda<2J$ at half power,
and then $P,Q$ by divisors of $g\lambda$. Pay $q^{o(1)}\sqrt R$
actual triples per split. The product, including the subpower bin
sums, is $q^{1.055+\tau/2+o(1)}$. The
[exact arithmetic check](check-exceptional-visible-filters.py) checks
the endpoint comparisons, not the lattice or component arguments.

For the $1.1354$ parent, no more repricing of exceptional visible
splits is necessary. On the same unpruned list with reciprocal cuts,
the [two-ratio radical count](two-ratio-radical.md) also already pays
for $r(L)\le3.320$ off any one prescribed eligible pool in its scope.
The ordinary complement still needs actual common-input occupancy:
In a hidden-factor bin $J_0\asymp q^t$ with
$\mu=\min(t/2,.223)$, an upper bound $q^{1.1354-\mu+o(1)}$ on its
occupied labels suffices, including the multiplicity and subpower
sum over bins. The label bound is not necessary; the original
[denominator-pair budget](exterior-count-handoff.md) is an alternative.
Use both successful second rows at the same $c$ in the next count.
Neither the smaller exceptional filter nor the one-pool radical bound
gives a hit rate, a cover, or a saving on this remaining union.
