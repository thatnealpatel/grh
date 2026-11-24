---
evidence_revision: 6e777c9fccca8071842f8dbf9ac0940932090ab8
outcome: established
---

# Test an optimal rational triangular palette

**Proposition:** For each integer $q\ge2$, let $G=(\mathbb Z/q\mathbb Z)^*$,
$d=|G|$, and let $k$ be the number of Galois orbits on $\widehat G$,
equivalently the number of its cyclic subgroups, including the trivial
one. The least number of rational masks $w_i:G\to\mathbb Q$ such that
$$h\longmapsto\left(\sum_\chi b_{i,\chi}h_\chi\right)_i,\qquad
 b_{i,\chi}=d^{-1}\sum_g w_i(g)\overline{\chi(g)},$$
is injective on arbitrary nonnegative integer order vectors at one
location is $k$. This lower bound is only for the simultaneous
pointwise code, not for actual divisors subject to global constraints,
bounded orders or heights, or more general sampling.

An attaining palette can have $0<w_i(g)<1$ and
$\sum_g(1-w_i(g))\le3r/4$, with
$r=(10^6\lceil\log(2q)\rceil)^{-1}$. For the triangular kernel
$h_\triangle=\mathbf1_{[0,\log2]}*\mathbf1_{[0,\log2]}$, let
$$H_i(X)=\overline w_i X-\sum_{p\nmid q}(\log p)w_i(p\bmod q)
  h_\triangle(\log(p/X)),\qquad K(s)=((2^s-1)/s)^2.$$
On joint GRH for the primitive inducers modulo $q$, including zeta,
each $H_i(X)>\sqrt X/25$ for every real $X\ge2$. Let $P$ be any known
real polynomial of degree $D\ge1$ with positive leading coefficient.
At each prime $p$ with $P(p)\ge2$ observe only row $i$ indexed by the
rank of $p$ among all rational primes modulo $k$. Receive one indexed
real or an erasure. For any known $\kappa>0$, allow at most
$O(N^{1-\kappa})$ arbitrary corruptions and erasures combined across
all rows per late $[N,2N)$, with uniform good errors
$o(\sqrt{P(p)})$ and unknown bad set. Joint GRH is equivalent to
$O(N^{1-s})$ reported raw negatives per such block for some $s>0$.
The same scalar stream determines each named primitive inducer's
exact nontrivial zero divisor, including shared and central orders.
Neither readout presupposes data from an older stream, and neither
finite-work recovery nor stability is claimed.

**Source and payoff:** The evidence revision closes
`shared-triangular-sign-and-labelled-divisors.md` for a single fixed
irrational mask. Its character-expansion and residual-median sources
are `6596fa6e00f481978d7f2792eec2b3dde99a8a29` and
`6169a926323525cf7f02428e73cee7d63e68d694`. This is a proposed new
observable testing whether irrationality is needed in any mask of a
single reported stream, not whether the old stream supplies these data.

**Discriminating test:** Restrict to orbit-constant rational order
vectors for the lower bound and convert a kernel vector to two
nonnegative integer vectors. Test the baseline-only principal row and
one row per nontrivial orbit: Shift a cyclotomic normal element by a
negative rational without losing independence, scale its conjugates,
and verify rational Fourier inversion, sign bounds, and exact recovery
on shared zeros using cyclotomic coordinate arithmetic. Include $q=2$
and a modulus with a nonreal orbit and multiple cyclic subgroups of the
same order. Check the pinned discrepancy and numerical floor, the
weights on prime squares, and negative or absent real residues.
Require a visible pole in some row beyond each subedge, then check
Landau, half-moment propagation, cyclic color mass, and the entire bad
budget. Run residual medians on each row's own sample positions, take
the union with zero for missing coefficients, and check the terminal
biased line average and same-label reflection.

## Adjudication

The minimum is $k$. In the stream it suffices that *some* row see a
zero beyond each proposed subedge. The row need not see the other
zeros, and its readings need not coincide in time with any other row's.

**Necessity.** In $F=\mathbb Q(\zeta_d)$, rationality of $w_i$ gives
$\sigma_a b_{i,\chi}=b_{i,\chi^a}$. The subspace of rational vectors
constant on each orbit has dimension $k$. Each output on it is fixed
by every $\sigma_a$, hence rational. Fewer than $k$ outputs therefore
kill a nonzero rational vector there. Clear denominators; its positive
and negative parts are distinct admissible vectors with equal outputs.
For a character of order $n\mid d$, reduction of units modulo $d$ onto
units modulo $n$ is surjective: Lift at the prime powers of $n$ and use
one at the other prime powers of $d$, by CRT. The stabilizer is exactly
the kernel of reduction. Thus the orbit consists of all generators of
that cyclic subgroup, with the trivial subgroup contributing one orbit.

**A rational inverse Fourier construction.** Put $\beta=1-r/(2d)$.
Every row has principal coefficient $\beta$; the baseline has no
others. In a row for a nontrivial orbit, fix a representative $\psi$
of order $n$. In $E=\mathbb Q(\zeta_n)$ choose a normal element $x$:
The normal basis theorem guarantees one, and clearing denominators
preserves normality. Enumerate integer power-basis coordinates by sup
norm with lexicographic ties until the conjugate matrix has full rank.
Adding $t\in\mathbb Q$ to all conjugates is a common column shift:
By multilinearity two shifted columns give zero, so the new determinant
is affine in $t$ and nonzero at zero. With $B$ the sum of absolute
coordinates of $x$, both $-B-1$ and $-B-2$ give strictly negative real
parts at every embedding; at least one keeps full rank. Choose the first
such $t$. Scale $x+t$ by $r/(4d[E:\mathbb Q](B+|t|))$ to obtain $v$.
Assign $b_{i,\psi^a}=\sigma_a v$ and leave other nonprincipal entries
zero. These choices, including a fixed enumeration of orbit generators,
use no zero data.

Now $w_i(g)=\sum_\chi b_{i,\chi}\chi(g)$ is fixed by the Galois group
of $F$ since it permutes the summands. Fourier orthogonality returns
the specified coefficients. Each rational weight lies within $r/(4d)$
of $\beta$, hence strictly between zero and one; the mean is $\beta$,
so the total deficit is exactly $r/2$. Divide the baseline output by
$\beta$ to get the principal order. After subtracting the baseline
output from each other row, the conjugate-basis coordinates are the
individual orders in that orbit. This works on differences, without
bounds or conjugacy restrictions on the inputs. For $q=2$ only the
baseline is needed. In particular the only commonly invisible vector
is zero.

**Row expansion and floor.** Use the target's lines 77–131 and the
expansion pin, lines 69–123. Complete the triangle with $w_i(p^j)$.
Fourier inversion gives character Mangoldt sums; replacing by primitive
inducers costs $O_q(1)$ (bounded exponents per omitted base). In each
primitive integral the quadratic decay of $K$ kills the selected
horizontal sides with log derivative $O_q(\log^2(2+|t|))$; the side
at $-1/2$ costs $O_q(X^{-1/2})$. The pole cancels the mean since
$K(1)=1$. The zero terms enter with plus sign in the deficit. Adding
back squares via the fixed-class prime number theorem uses $w_i(g^2)$
and $\int_1^2 h_\triangle(2\log u)\,du=K(1/2)/2$; powers of order at
least three cost $O_q(X^{1/3}\log^2(2X))$. Thus for each fixed row,
$$H_i(X)=\sum_z c_i(z)X^z+C_i\sqrt X+o_q(\sqrt X),\quad
c_i(z)=K(z)\sum_\chi b_{i,\chi}m_\chi(z),\quad
C_i=\frac{K(1/2)}{2d}\sum_g w_i(g^2).$$
The unit-height zero count $O_q(\log(2+|t|))$ and quadratic decay
give $\sum_z|c_i(z)|(1+|z|)^v<\infty$ for $0\le v<1$. Real weights
pair conjugate points with conjugate coefficients. Since $|2^z|>1$
in the open strip, division by $K(z)$ loses no location.

For the *uniform* conditional bound use the onset pin, lines 206–276,
not the fixed-$q$ remainder. Write $Y=\sqrt X$, $L=\log(2q)$, $P_g$
for the prime sum in class $g$, and $P_{\rm bad}$ for the prime sum on
bases dividing $q$. The exact deficit is
$$H_{\rm all}+P_{\rm bad}-\sum_g(1-w_i(g))(X/d-P_g).$$
In the class filter $\overline{\chi(g)}/d$ the absolute weights sum
to one. The pole gives $X/d$; the pinned zero and omitted-base costs
remain $108YL+10+3\log q$. The filter selects $p^j\equiv g$; removing
proper powers costs at most $2\log 2\,\vartheta(2Y)<4Y$ (at most two
powers per base in the open support). Thus $|X/d-P_g|<200YL$ for
every class. Dropping $P_{\rm bad}\ge0$ and charging the looser deficit
$3r/4$ costs at most $0.00015Y$. Subtracting this from the three pinned
floors for $H_{\rm all}/Y$ gives $7113/80000$, $4119/100000$, and
$228428303/5241600000$. The least exceeds $1/25$ by $119/100000$.
There is no large-$q$ or large-$X$ qualification.

**Signs before decoding.** On joint GRH only bad entries can be negative
eventually. Otherwise same-label reflection gives $\theta=\sup\Re z>1/2$.
At a real zero $z>1/2$ the zeta order vanishes (positivity of eta in
$(0,1)$), the sum in each row is real, and every selected nonprincipal
coefficient has strictly negative real part. As $K(z)>0$, the residue
is absent or negative. For any $1/2<u<\theta$, choose a zero to its
right, then a row $i$ with $c_i(z)\ne0$ by injectivity. Suppose there
were a nonnegative tail $H_i(X)+X^u$ from $A\ge2$. Its Mellin integral
on $\Re s>\theta$ continues to $\Re s>u$ by the normally convergent
pole sum $\sum_z c_i(z)A^{z-s}/(s-z)$ off its poles and a holomorphic
remainder. In particular the chosen pole survives. A real convergence
abscissa above $u$ cannot be a pole: Its negative residue contradicts
nonnegativity from the right. Nor can it be regular: A Taylor disk
centered just to its right would reach a point left of it; summing the
nonnegative logarithmic moments there by monotone convergence gives a
finite integral. An abscissa at or below $u$ makes the integral itself
holomorphic at the chosen pole. Thus $H_i(Y)<-Y^u$ arbitrarily late.

Given a proposed saving $s>0$, take $0<e<\min(s,\kappa,1/20)$ and
$1/2<b<u<\theta$ with $u>\theta-e/(2D)$. Use the row just selected
for this $u$. On $[T,T+T^{1-e}]$ with $P(T)=Y$ on the increasing
tail, the log-image width is $O(T^{-e})$. The bound
$|e^{tz}-1|\ll(t(1+|z|))^{1/2}$ for $0\le t\le1$ and the half-moment
give variation $O(Y^{\theta-e/(2D)}+\sqrt Y)=o(Y^u)$, bounding the
remainders separately. Throughout the interval this row is below
$-P(x)^b$, dominating the noise. The all-interval prime count at length
$x^{9/10}$ (target, lines 185–189) packs into this interval with only
$O(T^{9/10})$ uncovered, giving $m\gg T^{1-e}/\log T$ primes. Their
full-sequence ranks are consecutive, so at least $\lfloor m/k\rfloor$
read this very row, independently of erasures. One dyadic block with
$N\asymp T$ contains at least half of these. Even after subtracting
its *whole* bad budget, the ratio to $N^{1-s}$ tends to infinity along
the excursions. This uses neither a topmost zero nor simultaneous data.

**Recover the visible residues separately.** In the median pin, lines
65–149, take $e=\min(\kappa/2,1/20)$ and $h_0=e/(2D)$. Split each late
dyadic block $[M,2M)$ into $\lfloor M^e\rfloor$ equal cells. The same
packing and cyclic count give $\gg M^{1-e}/(k\log M)$ primes of *each*
color per cell, eventually more than twice the entire block budget.
Thus each row has a strict good majority among its nonerasures. At
$a=1$ start with all terms; at subsequent stages subtract every already
exposed term with $\Re z>a$ from that row at each nonerased sample's
own argument. This is an absolutely convergent real sum. Take a fresh
lower median $m_{i,a}$ of that row's residuals on each image cell
(zero if empty). For $S_{i,a}(X)=\sum_{\Re z\le a}c_i(z)X^z$, its
variation across log-width $O(X^{-e/D})$ is $O(X^{a-h_0})$ by the
half-moment. The square term varies by $o(\sqrt X)$, so the majority
puts the median within $O(X^{a-h_0})+o(\sqrt X)$ of
$S_{i,a}(X)+C_i\sqrt X$ throughout the cell.

The median's Mellin germ on $\Re s>a$ determines its continuation to
$\Re s>\max(1/2,a-h_0)$: Integrate $S_{i,a}$ as the pole sum above;
the discrepancy integral is holomorphic there, with a finite prefix
contributing an entire term. Exactly the *nonzero* coefficients in the
exposed strip appear as residues. Reset $a$ to its lower edge, which is
included at the next stage. After at most $\lceil D/e\rceil$ stages,
$a=1/2$. Then $m_{i,a}/\sqrt X-C_i$ is the absolutely summable line
series plus $o(1)$ by domination on the strictly left terms. Its mean
against $X^{-it}\,dX/(X\log(R/A))$ on $[A,R]$ tends to
$c_i(1/2+it)$, zero if absent: Each unmatched exponential averages to
zero, and the known bias was removed even at $t=0$. Union the visible
locations across rows, assign zero in absent rows, divide by $K(z)$,
and invert the pointwise code. The functional equation followed by
conjugation gives the same named order at $1-\bar z$, filling the left
half. This determines the divisors from the infinite stream; it is not
a finite or noise-stable algorithm.

**Independent arithmetic check.** For $q=16$, write the units as
$(-1)^a5^b$, giving dual $C_2\times C_4$. The six orbits consist of
four singletons and two pairs. In integer units $1/S$, $S=32d/r$, use
principal numerator $S-16$, nontrivial singleton numerator $-1$, and
pair numerators $-1\pm i$ in their respective rows. Exact Fourier
inversion gave rational masks of deficit $r/2$ and the stated square
means. Decoding returned all $3^8=6561$ inputs with coordinates in
$\{0,1,2\}$, as well as orders $10^{70}+j^2$ indexed from zero. The
baseline alone gave the analogous round trips at $q=2$. In every case
dropping a row produced a collision. These finite checks exercise the
construction; the dimension and basis arguments give the sharp result.
