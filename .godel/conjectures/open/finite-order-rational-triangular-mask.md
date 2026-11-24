---
evidence_revision: b9d8bfccb6e44666d56d3f64c9e8ba4cd9f8c24a
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
