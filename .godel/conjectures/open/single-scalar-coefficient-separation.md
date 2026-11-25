---
evidence_revision: 12ba4a031a429d27a8de06d9b1338a28f53ce187
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
