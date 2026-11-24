---
evidence_revision: 836fa5e3174e0cb576774ac3660784748549cf1e
outcome: established
---

# Test the sharp coefficient-field palette

**Proposition:** Fix $q\ge2$, $G=(\mathbb Z/q\mathbb Z)^*$,
$d=|G|$, and a specified embedded number field $K\subset\mathbb R$.
Put $F=\mathbb Q(\zeta_d)$, $E=KF$, $J=\operatorname{Gal}(E/K)$,
and $m=[K:\mathbb Q]$. Let $n_J$ count the $J$-orbits on $\widehat G$,
including the principal orbit. For $w_i:G\to K$, let
$$b_{i,\chi}=d^{-1}\sum_g w_i(g)\overline{\chi(g)}.$$
The least row count making $h\mapsto(\sum_\chi b_{i,\chi}h_\chi)_i$
injective on every nonnegative integer vector at one location is
$L=\lceil n_J/m\rceil$. Over all real embedded fields, the least
single-mask degree is the number $k$ of absolute Galois orbits.

An optimal palette can take every mean to be $\beta=1-r/(2d)$,
$r=(10^6\lceil\log(2q)\rceil)^{-1}$, with $0<w_i(g)<1$ and
$\sum_g(1-w_i(g))=r/2$. Use the pinned triangular prime deficit $H_i$
with these new masks. On joint GRH each row has
$H_i(X)>\sqrt X/25$ at every real $X\ge2$. Each row has only negative
or absent grouped residues at real zeros to the right of $1/2$.
With known $P$ of degree at least one and positive leading coefficient,
read one indexed real value of $H_i(P(p))$ or an erasure where
$P(p)\ge2$, cycling rows by the full rational-prime rank modulo $L$.
Allow uniform good errors $o(\sqrt{P(p)})$ and an unknown set of
$O(N^{1-\kappa})$ corruptions and erasures combined per late $[N,2N)$,
for known $\kappa>0$. Some positive power saving in the count of raw
reported negatives is equivalent to joint GRH. The same scalar data
determine every named primitive inducer's exact nontrivial divisor.

**Source and payoff:** The rational-palette landing proves the rational
case and uses a separate principal-only row. The shared triangular
sign-and-divisor landing `6e777c9fccca8071842f8dbf9ac0940932090ab8`
uses a single mask in a larger field. The proposed extension tests
packing with a common principal coefficient and no spare baseline
row, including fields that intersect $F$ or are not normal. This is
about a universal unbounded pointwise code, not an impossibility for
actual divisors, bounded orders, or other measurement schemes. The
samples are for the new masks, not recovered old observations. No
finite certification, precision optimum, or stability is claimed.

**Discriminating test:** Apply dimension over $\mathbb Q$ on the orbit
constants and split a cleared kernel vector into nonnegative parts.
Test a shifted, trace-one normal basis over $K$, coset sums per orbit,
and a positive $\mathbb Q$-basis of $K$ for packing. Check equivariant
Fourier inversion and exact coordinate decoding with the principal
order recovered in the first row and subtracted in every later row.
Exercise equal-degree fields $\mathbb Q(\sqrt5)$ and $\mathbb Q(\sqrt2)$
at $q=11$, checking the intersection, orbit counts, and round trips
including uneven conjugate orders and reused principal slots. Check
$q=2$ and the single-mask degree construction via Eisenstein at an
unramified prime of $F$. Finally verify the precise rowwise hypotheses
used by the pinned floor, negative excursions, cyclic prime count,
and median strip and square-bias line readout. Check both invisible
real residues and the guaranteed visibility of each actual zero.

## Adjudication

The minimum is $\lceil n_J/m\rceil$ even with the stated analytic
requirements. The rational construction at evidence lines 82–109 needs
its first row for the principal order. Here only the **first slot** of
that row is reserved; every other slot, including slot one in later
rows, can carry an entire orbit.

**Obstruction.** $E/K$ splits $T^d-1$ and is Galois. Restriction to
$F$ is injective, and the fixed field of its image in $F$ is
$F\cap E^J=F\cap K$. Thus its image is exactly
$\operatorname{Gal}(F/(F\cap K))$, without a normality hypothesis
on $K$. Fourier coefficients of a $K$-mask transform by permutation
of labels: $\sigma b_{i,\chi}=b_{i,\sigma\chi}$, since on roots of
unity conjugation is inversion. On the rational orbit constants the
output is consequently in $K$ in each row. If there are $l$ rows
with $lm<n_J$, this rational linear map has a nonzero kernel vector.
Clear its denominators. Its positive and negative parts are distinct
nonnegative integer inputs with the same outputs. This obstruction
does not require a margin or sign constraint.

**Attainment and decoding.** Choose a normal element $x$ of $E/K$ by
the normal basis theorem. In a fixed $K$-basis, adding a rational
$t$ to $x$ shifts every conjugate column by the same $t$ times the
column of $1$. The determinant is affine in $t$ by multilinearity and
nonzero at zero. Take an integer $t$ large enough that all conjugates
of $x+t$ have positive real part and avoiding the possible root. The
trace is real in the specified embedding and positive. Divide by it:
The conjugates of the resulting $\xi$ still form a basis, have positive
real parts, and sum to $1$. No other embedding of $K$ is used.
For each representative $\psi$ with stabilizer $B$ set
$$u_{\sigma\psi}=\sum_{\tau\in\sigma B}\tau\xi.$$
This is independent of the coset representative, equivariant, and
has positive real part. Within one orbit its normal-basis columns
are the indicators of a partition of $J$; different orbits need not
have different partitions.

Extend $1$ to a rational basis $\lambda_1=1,\ldots,\lambda_m$ of $K$
and shift the other elements by integers to make them positive. Pack
the orbits in distinct (row, slot) pairs in $L$ rows of $m$ slots,
putting the principal orbit first. Set $b_{i,1}=\beta$ in **every**
row. For a nonprincipal orbit in slot $j$ of row $i$ take
$b_{i,\chi}=-\varepsilon\lambda_j u_\chi$ there and zero elsewhere.
The finite sums allow one positive rational $\varepsilon$ such that
$\sum_{\chi\ne1}|b_{i,\chi}|\le r/(4d)$ in all rows. This uses no
zero data. Each inverse sum $w_i(g)=\sum_\chi b_{i,\chi}\chi(g)$ is
fixed by $J$, hence in $K\subset\mathbb R$. Orthogonality gives the
prescribed forward coefficients. The weights lie within $r/(4d)$ of
$\beta$, strictly between zero and one. Their mean is $\beta$, so the
total deficit is $r/2$.

Expand the first output in the rational basis
$\{\lambda_j\tau\xi:j=1,\ldots,m,\ \tau\in J\}$ of $E$. Since
$1=\sum_\tau\tau\xi$ and $\beta$ is rational, each slot-one coordinate
is $\beta h_1$. In **later** rows subtract $\beta h_1$ from the output
before reading *any* slot. Now for every nonprincipal occupied slot,
the coordinate at $\tau$ is exactly $-\varepsilon h_{\tau\psi}$.
Thus even labels exchanged by complex conjugation can have independent
orders at a point. The argument includes unused slots and $q=2$, where
one observes just $\beta h_1$. In particular no nonzero order vector is
invisible in all rows; one row alone can miss a zero.

**One-mask degree.** Restriction can only split absolute orbits, so
$n_J\ge k$. The obstruction gives $m\ge k$ for one mask. For $k>1$
choose a prime $p\nmid d$ and the positive real root $\alpha=p^{1/k}$.
At any prime of $F$ over $p$, the normalized valuation of $p$ is one
by cyclotomic unramifiedness. Thus $T^k-p$ is Eisenstein over both
$\mathbb Q$ and the valuation ring in $F$. For $K=\mathbb Q(\alpha)$
we have $[K:\mathbb Q]=[E:F]=k$. By the tower law $[E:K]=[F:\mathbb Q]$,
so restriction is onto and $n_J=k$. One row attains the bound. For
$k=1$ use $K=\mathbb Q$. A proper subfield generated by the entries
of a minimum-degree single mask would violate the same lower bound.

**Independent exact example.** At $q=11$ index characters by their
value $z^j$ at $2$, with $z=\zeta_{10}$. Absolute orbits are the
singletons $0,5$ and the two four-element sets of orders five and ten.
Since $2(z+z^{-1})-1=\sqrt5$, the subgroup fixing $\sqrt5$ consists
of $\{1,9\}$: It fixes $z+z^{-1}$ and is of index two. This gives two
singletons and four pairs, requiring three rows. In contrast
$F=\mathbb Q(\zeta_5)$ is unramified at two, so cannot contain
$\mathbb Q(\sqrt2)$ (discriminant eight). The intersection is rational,
all four absolute orbits persist, and two rows are necessary and suffice.

For reproduction, use rational polynomial coordinates modulo
$Z^{16}-Z^{12}+Z^8-Z^4+1=\Phi_{40}(Z)$, $z=Z^4$. In the first example
use $\xi=(4+z-z^{-1})/8$, and in the second use $\xi=(2+z)/9$ and
$\sqrt2=Z^5+Z^{-5}$. Form conjugates by replacing $z$ by $z^a$ for
$a$ in the indicated subgroup, fixing the quadratic multiplier. In both
cases their sum was one and the matrix of conjugates followed by their
quadratic multiples had full column rank. With orbits ordered by least
index, two slots in each row, and $\varepsilon=r/10000$, exact Fourier
inversion gave weights in the span of $1,\sqrt{5}$ or $1,\sqrt{2}$,
respectively, and transformed back to the assigned coefficients.
Stacking the rational columns for the ten unit inputs gave rank ten
in both cases. Reading the slot coordinates recovered the ten units and
$h_j=10^{80}+7j^2-j$. Dropping the last row gave ranks four and two on
the six- and four-dimensional orbit constants, respectively. These are
checks of the packing and subtraction; sharpness follows from the two
general arguments, not from testing bounded inputs.

**Analytic transfer.** The proof at evidence lines 111–144 uses
real bounded weights, not rational coordinates. In the explicit
formula (`6596fa6e`, lines 69–123) one completes with $w_i(p^j)$ at
$p^j$; replacement by primitive inducers costs $O_q(1)$ for fixed
masks by boundedly many exponents per omitted base in $[X,4X]$.
Write $A(s)=((2^s-1)/s)^2$. The pole cancels $\beta X$ since $A(1)=1$.
Subtracting the full sum reverses the zero sign; restoring squares
uses $w_i(g^2)$ and the fixed-class prime number theorem, and higher
powers are $o(\sqrt X)$. Thus
$$H_i(X)=\sum_z c_i(z)X^z+C_i\sqrt X+o(\sqrt X),\quad
 c_i(z)=A(z)\sum_\chi b_{i,\chi}m_\chi(z),\quad
 C_i=\frac{A(1/2)}{2d}\sum_g w_i(g^2).$$
Quadratic transform decay and the unit-height zero count give
$\sum_z |c_i(z)|(1+|z|)^{1/2}<\infty$. The transform is nonzero
in the open strip since $|2^z|>1$. Hence every zero is visible in
some row. At a real zero above $1/2$ the principal order vanishes by
the alternating eta series. Conjugation pairs labels and orders there,
so the row sum is real. Each active nonprincipal coefficient has
negative real part; with $A(z)>0$ the residue is negative if any
active order is positive, zero otherwise.

For the all-scale conditional floor, the class twists at `068a54ef`,
lines 230–243, have absolute coefficient sum one in every class. They
select $p^j\equiv g$ with the same proper-power bound and hence give
$|X/d-P_g|<200\sqrt X\log(2q)$ under joint GRH. In the exact deficit
identity at evidence lines 130–143, the omitted-base prime sum is
nonnegative. The total deficit $r/2$ therefore costs at most
$\sqrt X/10000$. Subtracting this loss from the three ordinary floors
at `6e777c9f`, lines 97–103, gives minimum $1031/25000>1/25$.
This uses the pinned sieve and holds for all real $X\ge2$.

In the stream of the proposition, joint GRH now allows only bad entries
to report negative eventually. Conversely fix any proposed saving $s>0$.
Off joint GRH, reflection gives $\theta=\sup\Re z>1/2$; choose
$0<e<\min(s,\kappa,1/20)$ and $1/2<b<u<\theta$ with
$u>\theta-e/(2D)$, $D=\deg P$. Select a zero right of $u$ and *then*
a row seeing it. Evidence lines 151–162 apply: A nonnegative tail of
$H_i(X)+X^u$ would have Mellin transform continuing to $\Re s>u$
with that visible pole. Its convergence abscissa cannot exceed $u$,
since there the real point is regular or a pole of negative residue,
the former excluded by Landau's nonnegative moments and the latter by
positivity from the right. An abscissa at or below $u$ contradicts the
visible pole. Hence $H_i(Y)<-Y^u$ arbitrarily late. With $P(T)=Y$,
on $[T,T+T^{1-e}]$ the half-moment bounds the change by
$O(Y^{\theta-e/(2D)}+\sqrt Y)=o(Y^u)$. The row stays below $-P(x)^b$,
dominating good noise. The pinned all-interval prime lower bound at
length $x^{9/10}$ packs into this interval, giving
$\gg T^{1-e}/\log T$ consecutive primes. Full prime ranks give the
selected row a $1/L$ share up to rounding before erasures. At least
half that share lies in a single dyadic block with $N\asymp T$;
subtracting its whole bad budget still beats $O(N^{1-s})$ along
the excursions. Erasures are not reported negatives.

Finally, evidence lines 180–210 and `6169a926`, lines 65–149, require
only the half-moment, known bias, and a good majority *per row*.
With $e=\min(\kappa/2,1/20)$ the same count in each of
$\lfloor M^e\rfloor$ equal cells per late dyadic block gives
$\gg M^{1-e}/(L\log M)$ primes of each color, exceeding twice the
whole block budget. Recompute the residual median after subtracting
exposed terms at each sample's own $P(p)$. For residual edge $a$ the
log-width $O(X^{-e/D})$ and the half-moment give median error
$O(X^{a-e/(2D)})+o(\sqrt X)$ about the residual series plus the bias.
Its Mellin discrepancy is holomorphic to the right of
$\max(1/2,a-e/(2D))$, so the median germ determines precisely the
nonzero residues in the exposed strip. Iterate to $a=1/2$. Subtract
$C_i$ from the normalized median before taking the logarithmic mean
against $X^{-it}$: The strictly left terms vanish by domination and the
line series is absolutely summable, so the mean selects $c_i(1/2+it)$
even at zero frequency. Union the locations, fill missing rows with
zero, divide by $A(z)$, and apply the slot decoder. The functional
equation and conjugation preserve the named order at $1-\bar z$.
This proves both readouts for the new masks without synchronous
observations. It does not transfer observations from another palette.
