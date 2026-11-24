---
evidence_revision: 6169a926323525cf7f02428e73cee7d63e68d694
---

# Test one triangular stream for signs and labelled divisors

Use natural logs. For each integer $q\ge2$, list the units as
$g_0=1,\ldots,g_{d-1}$ in least-positive order, $d=\varphi(q)$.
Let $\ell$ be the least prime greater than $d$,
$\alpha=2^{1/\ell}>0$, and $r=(10^6\lceil\log(2q)\rceil)^{-1}$.
Use the weight
$$w(g_j)=1-rv_j,\qquad v_j=\tfrac12\mathbf1_{j=0}
 +\alpha^{j+1}/(8d).$$
For $h=\mathbf1_{[0,\log2]}*\mathbf1_{[0,\log2]}$, put
$$H(X)=\bar wX-\sum_{p\nmid q}(\log p)w(p\bmod q)h(\log(p/X)),$$
with $\bar w=d^{-1}\sum_j w(g_j)$ and the sum over primes.

**Proposition:** On joint GRH for all primitive inducers
modulo $q$, including zeta, $H(X)>\sqrt X/25$ for every
real $X\ge2$, with no link between $q$ and $X$.
Fix known $q$, a known real polynomial $P$ of degree $D\ge1$
with positive leading coefficient, and known $\kappa>0$.
At primes $p$ with $P(p)\ge2$, receive an indexed real value
$y_p$ or an erasure. At most $O(N^{1-\kappa})$ entries per
late block $[N,2N)$ are erased or arbitrarily corrupted,
with unknown bad set. Uniformly on the good tail,
$y_p=H(P(p))+o(\sqrt{P(p)})$. Joint GRH is equivalent to the
count of reported raw negatives, omitting erasures, being
$O(N^{1-k})$ for some $k>0$. The same scalar data determine
every named primitive inducer's exact nontrivial zero divisor,
including shared and central orders. Use signs for the first
readout and scalar values for the second; do not synthesize
either old operator from the samples. No finite work or
stability is asserted.

**Source and payoff:** All four pins are accepted ancestors:

- `068a54ef817f1d9b6a9ce77a4a0f73db4bf7456a`,
  `order-two-discounted-onset-two.md`: Ordinary-prime floor
  and identity-class discrepancy.
- `6596fa6e00f481978d7f2792eec2b3dde99a8a29`,
  `triangular-weighted-character-zero-divisors.md`:
  Character expansion and Fourier label inversion.
- `2a477e0bed19c2a3cfb88cf77d82a22104d69272`,
  `order-two-prime-index-violation-phase.md`: Continuous
  Landau, half-moment propagation, and prime mass.
- `6169a926323525cf7f02428e73cee7d63e68d694`,
  `robust-prime-index-labelled-zero-divisors.md`:
  Residual medians, Mellin strips, and the center.

The last landing proves its consumer for a different weight.
The proposed joint use tests compatibility of its label
coordinates with a uniform sign margin and negative real
residues, rather than combining two older measurements.

**Discriminating test:** Insert $\overline{\chi(g)}$ in the
orthogonality bound for each class, removing powers selected
by $p^k\equiv g$, and compare the discounted total loss to
the three certified ordinary-prime floor bounds. Derive the
character expansion, grouped residue signs, and exact
coordinates of $dc(z)/K(z)$ in the powers starting at
$\alpha^1$, including $d=1$ and arbitrary shared orders.
Check Landau without attainment at the top edge, propagate
late excursions at thresholds above the noise, and test the
prime mass against the whole bad budget. Verify realness,
samplewise subtraction, the median strip error, same-label
reflection, and square-bias subtraction at zero frequency
for this weight, not just for the earlier operator.
