---
evidence_revision: 6e777c9fccca8071842f8dbf9ac0940932090ab8
---

# Test positive-noise finite-height decoding for the shared stream

**Proposition:** Fix known integer $q\ge2$ and real $T\ge1$.
Use exactly the shared operator, labels, triangular kernel $K$,
and natural logs at the evidence revision. In particular,
$d=\varphi(q)$, $\ell$ is the least prime greater than $d$,
$\alpha=2^{1/\ell}$, and $R=10^6\lceil\log(2q)\rceil$.
For units $g_j$ in least-positive order starting at $g_0=1$,
$w(g_j)=1-R^{-1}(\tfrac12\mathbf1_{j=0}+\alpha^{j+1}/(8d))$
and $b_\chi=d^{-1}\sum_g w(g)\overline{\chi(g)}$. Set
$$
M=\lceil100\log(4q(T+2))\rceil,\quad A_0=8d^2R,\quad
n_F=\ell\varphi(d),\quad B_0=2A_0dM,
$$
$$
k_T=\frac{(\sqrt2-1)^2}{1/4+T^2},\quad
\mathrm{gap}=\frac{k_T}{A_0B_0^{n_F-1}},\quad
\eta=\min(1/100,\mathrm{gap}/4)>0,
$$
with $\varphi(1)=1$. Let $P$ be a known real polynomial of
degree $D\ge1$ and positive leading coefficient, and let
$\kappa>0$ be known. At eligible prime indices $p$ with
$P(p)\ge2$, the data give indexed real $y_p$ or an erasure,
with at most $O(N^{1-\kappa})$ erased or arbitrarily bad
entries in each late block $[N,2N)$. Along the good tail,
$$\limsup_{p\to\infty}\frac{|y_p-H(P(p))|}{\sqrt{P(p)}}\le\eta.$$
The bad set is unknown. The same data determine all exact
nontrivial off-line locations and named orders at all
heights, and the exact line locations and named orders at
$|\Im z|\le T$, including the center. Joint GRH remains
equivalent to $O(N^{1-k})$ raw reported negatives per
block, omitting erasures, for some $k>0$.

**Source and payoff:** The shared card at the evidence pin
uses $o(\sqrt X)$ good errors for its line selector. The
robust and triangular predecessor cards at
`6169a926323525cf7f02428e73cee7d63e68d694` and
`6596fa6e00f481978d7f2792eec2b3dde99a8a29` provide,
respectively, median strip peeling and the contour input.
The proposed stronger consumer replaces the convergent
selector by finite-codebook identification with a known
positive tolerance, without a supplied list of ordinates,
zero tables, separation, or a rightmost zero. No GRH,
simplicity, convergent noise average, finite work, or
positive all-height line radius is assumed or asserted.

**Discriminating test:** Calculate the exact Hadamard
difference at $2+it$ and $-1+it$, then use the functional
equation, an explicit digamma sum, and the absolutely
convergent Euler bound to test $m_\chi(1/2+it)\le M$,
including the pole-cancelling terms of $\xi$ and $q=2$.
In $\mathbb Q(\zeta_d,\alpha)$ test integrality, nonvanishing,
and the conjugate bounds for $A_0\sum_\chi b_\chi h_\chi$
for nonzero codeword differences. Check the resulting
uniform distance against $2\eta$, including absence.
Recompute medians after samplewise subtraction from the
original values and verify the coefficient of $\eta$ does
not accumulate. Test Mellin holomorphy in every next open
strip and label-preserving reflection. At each arbitrary
$t$ in the closed band, test whether a potentially
nonconvergent twisted logarithmic mean selects a unique
codeword by limsup distance, including $t=0$ after
subtracting the known square bias. Recheck the raw sign
counts against the same good-error bound and bad budget.
