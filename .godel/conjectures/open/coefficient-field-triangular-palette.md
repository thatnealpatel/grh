---
evidence_revision: 836fa5e3174e0cb576774ac3660784748549cf1e
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
