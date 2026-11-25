---
evidence_revision: 12ba4a031a429d27a8de06d9b1338a28f53ce187
outcome: established
---

# Test the single-scalar coefficient separation exponent

**Proposition:** Fix $q\ge2$, $G=(\mathbb Z/q\mathbb Z)^*$,
$d=|G|$, and let $a$ count the complex-conjugation classes of
characters, including the principal label $1$. For a real mask
$w:G\to(0,1)$ set $b_\chi=d^{-1}\sum_g w(g)\overline{\chi(g)}$.
Let $\Delta_M(w)$ be the minimum of
$|\sum_\chi b_\chi(h_\chi-h'_\chi)|$ for distinct words in
$\{0,\ldots,M\}^d$, with collisions counted as zero. For every
integer $M\ge1$ the optimal gap is $\asymp_q(M+1)^{-(a-1)}$,
even for rational masks chosen separately for each $M$. A
single real algebraic mask, independent of $M$, attains the
lower bound simultaneously. Both lower constructions can have
mean $\beta=1-r/(2d)$, $r=(10^6\lceil\log(2q)\rceil)^{-1}$,
$|w(g)-\beta|\le r/(4d)$, total deficit $r/2$, and strictly
negative nonprincipal coefficient real parts.

Use this fixed algebraic mask in the pinned triangular prime
deficit, with transform $K(s)=((2^s-1)/s)^2$. Let $P$ be a
known real polynomial of degree $D\ge1$ with positive leading
coefficient. At eligible primes $p$ with $P(p)\ge2$ receive
indexed values or erasures, with $O(N^{1-\kappa})$ arbitrary
bad entries and erasures combined per late dyadic block for
known $\kappa>0$. For any prescribed $T\ge1$ put
$M=\lceil100\log(4q(T+2))\rceil$. A good limsup normalized
absolute error at most $c_q/[(1+T^2)(M+1)^{a-1}]$ for an
explicit positive $c_q$ suffices for exact named line orders
within the closed band, including shared and central orders,
and all named off-line orders at all heights. The joint GRH
floor is $H_w(X)>\sqrt X/25$ for all $X\ge2$, and joint GRH is
equivalent to a positive power saving per late dyadic block
in raw reported negatives (not counting erasures). The
rational masks give the band readout but are not asserted to
make all out-of-band zeros visible.

**Source and payoff:** The pinned denominator landing uses a
finite-box norm gap in its line selector. The coefficient-field
landing `b9d8bfccb6e44666d56d3f64c9e8ba4cd9f8c24a` and
positive-noise landing `7e7144a3b79704b7233c880832296e381f49a701`
provide analytic consumers. None claims this separation
optimum. Here $a$ is not the absolute Galois orbit count. The
upper obstruction concerns only pointwise box separation, not
actual zero configurations, statistical streams, or an optimal
noise tolerance. No optimum denominator or field degree is
claimed for these attaining masks. No positive all-height line
radius, finite-time recovery, or stability is claimed.

**Discriminating test:** Pack the $(M+1)^a$ conjugation-constant
words on the real axis. For attainment use $\alpha=2^{1/a}$
and assign real parts $-\varepsilon\alpha^j$ to nonprincipal
conjugation classes in slots $j=1,\ldots,a-1$, with principal
$\beta$. Give pair number $\ell$ opposite imaginary parts
$\pm\varepsilon\alpha^{\ell-1}$. Check Fourier inversion,
strict slack, independence of the real class sums and of the
imaginary pair differences, and the norm of either nonzero
component in $\mathbb Q(\alpha)$ after clearing denominators.
Exercise $q=2$, an all-real nontrivial group, and $q=11$ at
small $M$ in exact power coordinates or rigorous intervals.
Round on a rational mesh divisible by the mean denominator,
adjust the last weight, and test gap and sign retention. Check
the multiplication by $K$, the order cap, known square bias,
the median strip and limsup selector hypotheses, and the
visible-pole Landau argument for both raw sign directions.

## Adjudication

Write $B=M+1$ and $V(h)=\sum_\chi b_\chi h_\chi$. The exponent is
sharp for the full complex distance at a single point. It counts
conjugation classes, not classes under all cyclotomic automorphisms.

**Upper bound.** On the $B^a$ words constant on conjugation classes,
$V$ is real since $b_{\bar\chi}=\overline{b_\chi}$. Its values lie
in $[-dM,dM]$ since $|b_\chi|\le1$. A collision gives gap zero;
otherwise two consecutive outputs are at distance at most
$2dM/(B^a-1)\le 2d/B^{a-1}$. This applies separately to every
mask, even one chosen after $M$. At a common ordinate multiplying by
$K$ scales this distance by $|K|$. The midpoint is indistinguishable
at half that distance for the two coefficient words. Neither their
occurrence as orders nor indistinguishable prime streams follows.

**Lower bound, one fixed mask.** Take $R=1/r$, $A=32d^2R$,
$\varepsilon=1/A$, and $\alpha=2^{1/a}$. Set $b_1=\beta$. On
nonprincipal class $C_j$, $1\le j<a$, assign real part
$-\alpha^j/A$; give the two members of pair $\ell$ imaginary parts
$\pm\alpha^{\ell-1}/A$, and real characters imaginary part zero.
The indices $j$ distinguish all classes and $\ell$ numbers only pairs,
starting at one. Character orthogonality recovers these coefficients
from $w(g)=\sum_\chi b_\chi\chi(g)$, which is real by pairing and
algebraic since character values are roots of unity. The mean is
$\beta$. The nonprincipal moduli sum to at most $4(d-1)/A\le r/(8d)$,
so the inverse weights lie strictly between zero and one, with room
inside the required margin. Their total deficit is $r/2$.

For an integer difference $v$, put $s_j=\sum_{\chi\in C_j}v_\chi$
and let $u_\ell$ be the oriented difference on pair $\ell$. Then
$$
 A\Re V(v)=A\beta v_1-\sum_{j=1}^{a-1}s_j\alpha^j,
 \qquad A\Im V(v)=\sum_\ell u_\ell\alpha^{\ell-1}.
$$
Here $A\beta=A-16d$ is a positive integer. Eisenstein at two gives
the power basis through degree $a-1$ over $\mathbb Q$. Vanishing of
both components forces $v_1=0$, all class sums zero, and all pair
differences zero, hence $v=0$, with no order bound. If $v\ne0$ and
$|v_\chi|\le M$, choose either nonzero component $x$ of $V(v)$.
Then $Ax$ is an algebraic integer in the degree-$a$ field
$\mathbb Q(\alpha)$. Each basis power has modulus less than two at
every embedding. Since $\sum_j|s_j|\le(d-1)M$ and
$\sum_\ell|u_\ell|\le(d-1)M$, every conjugate of $Ax$ has modulus
at most $AM$: Even for the real component $\beta+2(d-1)/A<1$.
Its nonzero norm has absolute value at least one, so
$$
 |V(v)|\ge |x|\ge A^{-1}(AM)^{-(a-1)}\ge L_M,
 \qquad L_M=A^{-a}B^{-(a-1)}.
$$
The two components need not be independent of each other. The norm is
not taken in the field of the inverse weights. For $a=1$ there is just
the principal character and the gap is $\beta$.

**Rational approximation.** Take the least multiple $Q$ of the
denominator of $\beta$ at least
$\max(2d^2A^a B^a,2dA,8d^2R)$. Round the first $d-1$ inverse weights
to the mesh $1/Q$ within $1/Q$ and choose the last to restore the sum
$d\beta$ exactly. This last weight is on the mesh too. No weight or
Fourier coefficient changes by more than $d/Q$, so the sign margin
is at least $1/(2A)$ on nonprincipal real parts and the weights are
within $r/(4d)$ of their mean. The change in $V(v)$ is at most
$d^2M/Q\le L_M/2$, proving gap at least $L_M/2$. For $q=2$ the last
weight is simply $\beta$. This $Q=O_q(B^a)$ is sufficient only.
At $q=11$ the two singleton characters and the four conjugate pairs
give $a-1=5$; the two singletons and the orbits of orders five and
ten give $k-1=3$ in the minimum-denominator theorem. That theorem
only requires injectivity, not this spacing. Neither result gives a
simultaneous optimum for the two resources.

**Independent bounded check.** At $M=1,2$ use integer endpoints in
units $1/S$, $S=10^{100}$. Enclose $\alpha^j$ by the integer $a$th
root of $2^j S^a$ rounded down and up, divided by $S$. Sort intervals
for the real component with digits $0\le s_j\le |C_j|M$ and principal
digit $0,\ldots,M$; separately sort the imaginary component with
digits $-M\le u_\ell\le M$. Every nonempty adjacent-gap test (lower
endpoint minus preceding upper endpoint) gave at least $L_M$. At
$q=2,8,11$, the respective (real, imaginary) list sizes at $M=2$
were $(3,1),(81,1),(5625,625)$. At $q=8$ use the two character bits;
at $q=11$ use exponent at generator $2$, pairing $j$ with $10-j$
for $j=1,2,3,4$, then using the singleton $5$. For the inverse row
use $\cos(\pi/5)=(1+\sqrt5)/4$, $\cos(2\pi/5)=(\sqrt5-1)/4$,
symmetry, and the signed square root for the sine, enclosing square
roots by outward integer square roots on the same mesh. Rounding
interval midpoints to the $1/Q$ mesh except for the sum-restoring
entry verified the entry error bounds, mean, weight margin, and
$d^2M/Q\le L_M/2$ in all six cases. These checks exercise both the
empty and the nontrivial imaginary code. The proof for unbounded $M$
is the component norm estimate, not extrapolation from the checks.

**Transfer to the prime samples.** The evidence revision, lines
146–212, uses an order cap, a lower gap at a common ordinate, and
a separate procedure for learning grouped residues. For its in-band
selector only the spacing input changes. For this row the triangular deficit of evidence lines
27–33 has the expansion at `6596fa6e`, lines 69–123:
$$
 H_w(X)=\sum_z c(z)X^z+C\sqrt X+o(\sqrt X),\qquad
 c(z)=K(z)V(m(z)),\qquad C=\frac{K(1/2)}{2d}\sum_g w(g^2).
$$
Indeed, $K(1)=1$ cancels the mean pole and completing the prime sum
uses $w(p^j)$ on powers, which explains the square bias. The grouped
coefficients satisfy $\sum |c(z)|(1+|z|)^{1/2}<\infty$. These inputs
hold for bounded real rows (`b9d8bfcc`, lines 160–179). The same row
also meets the all-scale sign hypotheses there, lines 181–189. On
joint GRH, $|X/d-P_g|<200\sqrt X\log(2q)$ for the class prime sum;
charging this against the nonnegative deficits costs at most
$\sqrt X/10000$. The omitted-base prime sum has favorable sign. The
least of the three ordinary floors at `6e777c9f`, lines 97–103, less
this loss is $1031/25000>1/25$ in units of $\sqrt X$. This uses the
pinned onset certificate down to $X=2$, not a new grid computation.

For the stated $M$ and $T$, take
$$
 c_q=\min\{1/100,(\sqrt2-1)^2/(8A^a)\},\qquad
 \eta_T=\frac{c_q}{(1+T^2)B^{a-1}}.
$$
The positive Hadamard difference at `7e7144a3`, lines 80–113, bounds
each named in-band order by $M$: At $z=\sigma+it$ its contribution
per order is $1/(2-\sigma)+1/(1+\sigma)\ge4/3$, and the entire sum
is less than $9+\log(4q(T+2))$. On the line,
$|K(1/2+it)|\ge(\sqrt2-1)^2/(1/4+T^2)$. Thus even for the rounded
row every pair of candidate coefficients there is at least $4\eta_T$
apart, including pairs with the absent word.

For clarity, at each cut $u$, start with the original nonerasures and
subtract the exposed modes at their own $P(p)$. With
$e=\min(\kappa/2,1/20)$, each of the $\lfloor N^e\rfloor$ cells in a
late dyadic block contains $\gg N^{1-e}/\log N$ primes: Pack the
all-interval prime bound at length $x^{9/10}$ from Guth and Maynard,
[Count of primes in short intervals](https://arxiv.org/abs/2405.20552).
This exceeds twice the combined bad and erasure budget. The image
log-width is $O(X^{-e/D})$ on the increasing tail. The half-moment
bounds the change of the residual series across a cell by
$O(X^{u-e/(2D)})$, using $|\exp(vz)-1|\ll(v|z|)^{1/2}$ for log-width
$0\le v\le1$. The residual median differs from that series plus bias
by at most this variation and $(\eta_T+o(1))\sqrt X$. Consequently
the Mellin discrepancy is holomorphic on
$\Re s>\max(1/2,u-e/(2D))$. In the strip exposed from $u$ down to
but excluding that lower cut the poles and residues are exact: Only
the residual series contributes poles, with residues $c(z)$, and
continuation of the data germ is unique. Repeat from $u=1$ to
$u=1/2$, resetting the median rather than accumulating its errors
(`7e7144a3`, lines 138–182).

Since $K(z)\ne0$ in the open strip and the fixed code is injective on
all integer words, every right-half zero is visible and division by
$K(z)$ determines its named orders by the known countable inverse.
Same-label reflection $z\mapsto1-\bar z$ gives the strictly left
orders. For the rounded row only grouped residues are needed for
subtraction; the capped inverse names the off-line orders in band.
At the final cut divide by $\sqrt X$ and subtract $C$ (essential at
$t=0$). Strictly left modes vanish by domination. In the logarithmic
mean twisted by $X^{-it}$, unmatched line modes tend to zero and the
matched coefficient survives by absolute summability. The averaged
error has limsup modulus at most $\eta_T$, not necessarily a limit.
For each $|t|\le T$ the true word has limsup distance at most $\eta_T$
to these means; all rivals have liminf distance at least $3\eta_T$.
This names shared and central orders and detects absence without an
ordinate list (`7e7144a3`, lines 184–205).

**Raw negatives.** On joint GRH the floor and $\eta_T\le1/100$ leave
only bad reports negative eventually. Conversely any failure of joint
GRH gives a visible pole right of $1/2$ for the fixed row. At a real
point there the zeta order is zero, conjugate orders agree, and all
nonprincipal real parts are negative. Thus every real pole there has
negative residue ($K>0$). Write $\theta$ for the supremum of visible
real parts. For $1/2<u<\theta$ there are arbitrarily late
$H_w(Y)<-Y^u$: Otherwise the nonnegative tail of $H_w(X)+X^u$ has a
Mellin integral continuing meromorphically into $\Re s>u$ by the
expansion, with a pole there. An abscissa of convergence above $u$
cannot be regular by Landau's theorem, nor a negative-residue pole
by positivity from the right. An abscissa at or below $u$ contradicts
the visible pole. For any proposed saving $s>0$, choose
$0<e'<\min(s,\kappa,1/20)$ and $u$ as above with
$u>\theta-e'/(2D)$. For $P(x)=Y$ the variation over prime arguments
$P(p)$, $x\le p\le x+x^{1-e'}$, is
$O(Y^{\theta-e'/(2D)}+\sqrt Y)=o(Y^u)$ by the half-moment. Good errors
are also $o(Y^u)$. Prime packing then gives one late dyadic block
with $\gg N^{1-e'}/\log N$ such indices, before removing its whole
bad budget. The remaining raw negatives beat $O(N^{1-s})$ along the
excursions. This is the visible-edge argument of evidence lines
214–248; it requires neither a rightmost zero nor a band condition
on the fixed row's witness.

The gap optimum is for the universal pointwise box. The band radius
is sufficient for the infinite stream, not necessary. The mask can
stay fixed as $T$ varies; its guaranteed line radius cannot be read
as a positive all-height guarantee. No optimal degree or denominator
for attaining this gap is proved, and no finite-data, finite-work, or
continuation-stability guarantee follows.
