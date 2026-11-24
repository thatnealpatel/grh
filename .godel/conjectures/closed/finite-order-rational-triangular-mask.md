---
evidence_revision: b9d8bfccb6e44666d56d3f64c9e8ba4cd9f8c24a
outcome: established
---

# Test one rational triangular mask on a finite order box

**Proposition:** Fix integer $q\ge2$, $G=(\mathbb Z/q\mathbb Z)^*$,
$d=\varphi(q)$, $F=\mathbb Q(\zeta_d)$, $f=\varphi(d)$ with
$\varphi(1)=1$, and $J=\operatorname{Gal}(F/\mathbb Q)$. Let $k$
count the $J$-orbits of $\widehat G$, including the principal
label $1$. For every integer $M\ge1$, among rational masks
$0<w(g)<1$ for which
$$
 h\longmapsto\sum_\chi b_\chi h_\chi,\qquad
 b_\chi=d^{-1}\sum_g w(g)\overline{\chi(g)},
$$
is injective on $\{0,\ldots,M\}^d$, the minimum common denominator
is $\asymp_q(M+1)^{k-1}$. This is the least positive $Q$ with
$Qw(g)\in\mathbb Z$ for every $g$, not a bound on the maximum
individual reduced denominator. The upper bound can have mean
$\beta=1-r/(2d)$, $r=(10^6\lceil\log(2q)\rceil)^{-1}$,
$|w(g)-\beta|\le r/(4d)$, total deficit $r/2$, and
$\Re b_\chi<0$ for every nonprincipal label. Constants depend
only on $q$, including the constant-denominator case $q=2$.

For known $T\ge1$ take $M=\lceil100\log(4q(T+2))\rceil$ and a
single such constructed mask, fixed throughout the stream.
With $K(s)=((2^s-1)/s)^2$, put
$$
H_w(X)=\beta X-\sum_{p\nmid q}(\log p)w(p\bmod q)
 (\mathbf1_{[0,\log 2]}*\mathbf1_{[0,\log 2]})(\log(p/X)).
$$
Use its actual common denominator $Q$, put $A=dQ$, and set
$$
g_T=\frac{(\sqrt2-1)^2}{(1/4+T^2)A(AdM)^{f-1}},\qquad
\eta=\min(1/100,g_T/4).
$$
For any known real polynomial $P$ of degree $D\ge1$ and positive
leading coefficient, receive one indexed real $y_p$ or an erasure
at primes with $P(p)\ge2$. For known $\kappa>0$, allow an unknown
combined set of $O(N^{1-\kappa})$ arbitrary corruptions and erasures
per late $[N,2N)$, and good limsup normalized absolute error
$\limsup |y_p-H_w(P(p))|/\sqrt{P(p)}\le\eta$ along the good tail.
These data determine the exact named nontrivial zero divisors of
all primitive inducers, including zeta, in the whole open strip
with $|\Im z|\le T$, including shared and central orders. Under
joint GRH, $H_w(X)>\sqrt X/25$ for every real $X\ge2$, hence only
$O(N^{1-\kappa})$ reported raw negatives per late block. An off-line
zero in the band implies that the raw negative count is not
$O(N^{1-s})$ for any $s>0$. Erasures do not count as negatives.

**Source and payoff:** The coefficient-field landing at the evidence
pin, lines 81–120 and 160–231, gives the normal-basis construction and
analytic transfer. The all-order rational obstruction is at
`836fa5e3174e0cb576774ac3660784748549cf1e`; the positive-noise line
selector and its multiplicity estimate are at
`7e7144a3b79704b7233c880832296e381f49a701`. The proposed replacement
uses bounded orders, not bounds relating actual zero orders across
labels. It supplies one rational mask without time multiplexing.
It does not give all-height labelled recovery, a full-GRH equivalence
from fixed-band raw counts, optimal separation, or a finite-work or
sampling-duration bound.

**Discriminating test:** Count the integral values of $dQ$ times the
code on orbit constants. For the upper bound take a shifted,
trace-one normal basis with positive real parts and form the
stabilizer coset sums $u_\chi$ of the evidence pin. With $B=M+1$,
assign $\beta$ to the principal and $-\varepsilon B^{-j}u_\chi$
to nonprincipal orbit $j=1,\ldots,k-1$ for one fixed positive
rational $\varepsilon(q)<\beta/2$. Check inverse Fourier reality,
fixed denominators, and coordinate separation of the principal
intervals followed by exact radix decoding. Exercise $q=11$,
$M=1,2$, including unequal conjugate orders and digit endpoints,
and $q=2$. Then check the positive Hadamard difference at each
in-band ordinate for off-line as well as line orders, and use the
cyclotomic integer norm to test the uniform line gap against
$2\eta$ including the absent word. Check the class deficit and
square bias, the prime mass and each median strip at positive
noise, and the line selector without supplied ordinates or a
convergent noise mean. In the median and sign arguments retain only
nonzero grouped residues. In particular, test the Landau pole and
half-moment excursion bound with the supremum of the *visible*
real parts, even if the global zero edge lies further right.

## Adjudication

One rational row suffices for the entire prescribed box. What changes
from the all-order palette is the decoder, not the character expansion.
In the analytic application it is essential to distinguish a zero of an
inducer from a pole of the scalar data.

**Denominator lower bound.** Write $B=M+1$, $A=dQ$, and $V(h)=\sum b_\chi
h_\chi$. Each $A b_\chi$ is an integral combination of roots of unity,
with the Galois group permuting these coefficients as it permutes the
labels. On the $B^k$ orbit-constant words $A V(h)$ is therefore a
rational algebraic integer. Since $|b_\chi|\le1$, these integers lie
between $-d^2QM$ and $d^2QM$. Distinctness forces
$$Q\ge (B^k-1)/(2d^2 M)\ge B^{k-1}/(2d^2).$$
The inputs being counted are universal test words, not observed orders.

**Attaining the exponent.** Use the rational-base case of the normal
basis at evidence lines 81–95. Shifting a normal element by an integer
adds the same column to all conjugates; their determinant is affine in
the shift and nonzero at zero. Thus a large shift can make every real
part positive without losing normality. Divide by the positive rational
trace to get $\sum_\tau\tau\xi=1$. For each nonprincipal representative
$\psi_j$ use $u_\chi=\sum_{\tau:\tau\psi_j=\chi}\tau\xi$ on its orbit.
Fix rational $0<\varepsilon<\beta/2$ such that
$\varepsilon\sum_{\chi\ne1}|u_\chi|\le r/(4d)$. Set $b_1=\beta$ and
$b_\chi=-\varepsilon B^{-j}u_\chi$ on orbit $j$. These coefficients
have the specified signs. For every $g$, each orbit sum
$v_j(g)=\sum_{\chi\in O_j}u_\chi\chi(g)$ is Galois-fixed. Hence
$w(g)=\beta-\varepsilon\sum_j B^{-j}v_j(g)$ is rational, transforms
back to the assigned coefficients by orthogonality, and lies within
$r/(4d)$ of its mean $\beta$. This proves the weight and deficit bounds.
A common denominator of the fixed rationals $\beta,\varepsilon v_j(g)$,
times $B^{k-1}$, clears all weights simultaneously.

The coefficient of $\tau\xi$ in $V(h)$ is
$$x_\tau=\beta h_1-\varepsilon\sum_{j=1}^{k-1} h_{\tau\psi_j} B^{-j}.$$
The digit sum lies between zero and $1-B^{-(k-1)}$ inclusive.
Thus $h_1=\lceil x_\tau/\beta\rceil$. The integer
$B^{k-1}(\beta h_1-x_\tau)/\varepsilon$ has the indicated $k-1$
base-$B$ digits, padded on the left. Varying $\tau$ reads every label,
regardless of repetitions of the same partition of $J$ across orbits.
For $q=2$ the only weight is $3999999/4000000$ and there are no digits.
The rational kernel obstruction at `836fa5e3`, lines 70–80, allows
arbitrarily large coordinates; it does not provide a collision here.

**Exact check.** At $q=11$ label characters by the exponent at $2$,
use representatives $0,1,2,5$, $z=\zeta_{10}$, $\xi=(2+z)/9$, and
$\varepsilon=r/10000$. Reduce modulo $z^4-z^3+z^2-z+1$. In the order
$z\mapsto z^a$, $a=1,3,7,9$, the matrix taking power-basis columns to
trace-one normal coordinates has rows $(1,7,2,-2)$, $(1,-2,2,7)$,
$(1,-2,-7,-2)$, and $(1,-2,2,-2)$. Summing $b_c z^{cg}$ at the ten
generator powers gave rational weights with the specified mean and
margin; the forward transform returned all $b_c$. At $M=1,2$ their
respective LCMs were $2880000000000$ and $3240000000000$. Encoding in
power coordinates and applying the matrix, ceiling, and digit inverse
returned all $1024$ and $59049$ inputs exactly. The $16$ and $81$
orbit-constant inputs gave distinct integers after scaling by $dQ$.
These checks exercise endpoints and unequal conjugate orders; the two
general arguments prove the denominator law.

**Order cap and line gap.** At `7e7144a3`, lines 80–113, the positive
Hadamard difference for each primitive completion is $2\Re D_\chi(2+it)$.
A zero at $\beta'+it$ contributes per order
$1/(2-\beta')+1/(1+\beta')\ge4/3$ since the denominators sum to three.
This applies off the line too. The upper bound there is independent of
$\beta'$: The conductor is at most $q$, the doubled Euler term costs
less than four, and the zeta pole-cancelling factors cost at most three.
For $x\in[1,3/2]$, $y=t/2$, and $J_0=\lceil2+|y|\rceil$, the digamma
head costs at most $1+\log J_0$ and its tail at most
$(x-1)/J_0+y^2/(2J_0^2)<1$. Thus $(4/3)m_\chi\le2\Re D_\chi(2+it)
<9+\log(4q(T+2))$ on the closed band, sufficient for the asserted $M$.
For distinct box words $h,h'$, $A V(h-h')$ is a nonzero algebraic
integer. All its conjugates have modulus at most $AdM$, because they
permute the $b_\chi$. The nonzero integer norm gives
$|V(h-h')|\ge 1/[A(AdM)^{f-1}]$. On the line the reverse triangle
inequality gives $|K(1/2+it)|\ge(\sqrt2-1)^2/(1/4+T^2)$. This proves
the stated gap at a common ordinate, including against the zero word.

**What the samples determine.** Apply `836fa5e3`, lines 111–128, to
this fixed row. Completion uses $w(p^j)$; the pole cancels the mean,
and restoring prime squares gives $C=K(1/2)\sum_g w(g^2)/(2d)$.
The deficit is $\sum_z c(z)X^z+C\sqrt X+o(\sqrt X)$ with
$c(z)=K(z)V(m(z))$ and $\sum |c(z)|(1+|z|)^{1/2}<\infty$.
Omit zero coefficients everywhere. The visible terms still pair to a
real sum, and the expansion and half-moment have not changed.

Take $e=\min(\kappa/2,1/20)$ and partition each late dyadic block
into $\lfloor N^e\rfloor$ equal cells. The all-interval prime-count
corollary of Guth and Maynard (arXiv:2405.20552) applies at length
$x^{9/10}$ since $17/30+1/10<9/10<0.99$. Packing disjoint intervals
of that length from successive left endpoints leaves $O(N^{9/10})$
uncovered. Each cell contains $\gg N^{1-e}/\log N$ primes, eventually
more than twice the entire bad budget. On the increasing tail of $P$
all are eligible. Starting at $a=1$, subtract the previously exposed
terms with $\Re z>a$ at each original nonerased sample's own $P(p)$.
Let $m_a$ be the residual median on each image cell and $S_a$ the
remaining visible sum. The image log-width is $O(X^{-e/D})$ since
$P'/P=O(1/N)$. The inequality $|e^{vz}-1|\ll(v|z|)^{1/2}$ for
$0\le v\le1$, the half-moment, and the strict good majority give
$$|m_a(X)-S_a(X)-C\sqrt X|\le O(X^{a-e/(2D)})+(\eta+o(1))\sqrt X.$$
The square root varies by a relative $o(1)$ across a cell. No earlier
median error is subtracted from the data.

For $a>1/2$, put $b=\max(1/2,a-e/(2D))$. The median's Mellin germ
has on $\Re s>b$ the residual pole sum (terms
$c(z)U^{z-s}/(s-z)$ for lower endpoint $U$), plus a holomorphic
discrepancy. The sum converges normally off its locally finite poles.
Uniqueness exposes all and only nonzero coefficients in $b<\Re z\le a$
at all heights. Reset $a=b$, so intermediate lower boundaries are not
lost. Unlike `7e7144a3`, lines 177–179, this requires **no** inverse at
an out-of-band pole. An invisible zero is not a missing subtraction.
In band, $K(z)\ne0$ since $|2^z|>1$, and the capped code is injective
including against absence. Thus division and the radix inverse name
every above-line order there.

At $a=1/2$, divide the median by $\sqrt X$ and subtract $C$. Strictly
left terms vanish by domination. For any $|t|\le T$, take the mean
against $X^{-it}dX/X$ on $[U,V]$, normalized by $\log(V/U)$. Each
unmatched line frequency has mean tending to zero, and absolute
summability permits the limit through the line series. The limsup of
the modulus of the averaged error is at most $\eta$. The true line word
therefore has limsup distance at most $\eta$ from the observed means;
all rivals have liminf distance at least $g_T-\eta>\eta$. This selects
absence as well as shared orders without an ordinate list, a noise
limit, or confusing the bias with a central order. The functional
equation and conjugation preserve each named order at $1-\bar z$,
filling the left half at the same height.

**Raw signs.** Under joint GRH the exact deficit identity and class
bounds at `836fa5e3`, lines 130–144, charge at most $200\log(2q)r/2
\le1/10000$ in units of $\sqrt X$; the omitted-base prime sum has the
favorable sign. Subtracting $1/10000$ from the three inherited ordinary
floors at `6e777c9f`, lines 97–103, gives minimum $1031/25000>1/25$.
This uses the pinned grid, not a new sieve. Only bad entries can be
reported negative eventually.

Conversely, an off-line zero in band gives a visible point right of
$1/2$ by same-label reflection and the box inverse. Put
$\theta_v=\sup_{c(z)\ne0}\Re z>1/2$. At a real zero right of the
line zeta has no order (the alternating eta series is positive).
Conjugate labels have equal orders there, $K(z)>0$, and every
nonprincipal coefficient has negative real part. Thus real poles there
have negative residue. For any $s>0$ take $0<e'<\min(s,\kappa,1/20)$
and $1/2<b<u<\theta_v$ with $u>\theta_v-e'/(2D)$. There is a visible
pole right of $u$. If $H_w(X)+X^u$ were eventually nonnegative, its
tail Mellin integral would continue to $\Re s>u$ by the visible pole
sum and holomorphic remainder. A real convergence abscissa above $u$
cannot be regular (the nonnegative logarithmic moments in a Taylor
disk would give convergence to its left), or a negative-residue pole
(the integral is nonnegative from the right). An abscissa at or below
$u$ makes the integral holomorphic at the chosen pole. This proves
arbitrarily late $H_w(Y)<-Y^u$ without assuming a rightmost zero.

Write $P(x_0)=Y$ on the increasing tail. On
$[x_0,x_0+x_0^{1-e'}]$ the same half-moment estimate, now with visible
edge $\theta_v$, bounds variation by
$O(Y^{\theta_v-e'/(2D)}+\sqrt Y)=o(Y^u)$. Thus all values there are
below $-P(x)^b$, dominating good error. Prime packing gives one late
block $N\asymp x_0$ containing $\gg N^{1-e'}/\log N$ such indices
(the interval meets at most two blocks). Subtracting the whole bad
budget still leaves a count with unbounded ratio to $N^{1-s}$.
Invisible out-of-band zeros neither generate poles nor contribute to
variation. No converse localizing negative counts to this band follows.
