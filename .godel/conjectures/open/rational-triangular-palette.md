---
evidence_revision: 6e777c9fccca8071842f8dbf9ac0940932090ab8
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
