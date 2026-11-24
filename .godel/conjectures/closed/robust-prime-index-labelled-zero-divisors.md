---
evidence_revision: 2a477e0bed19c2a3cfb88cf77d82a22104d69272
outcome: established
---

# Recover named divisors from corrupted prime-index samples

**Proposition:** Fix known $q\in\mathbb Z$, $q\ge2$, a
known real polynomial $P$ of degree $D\ge1$ with positive
leading coefficient, and known $\kappa>0$. Use exactly the
labelled triangular operator $H$ in the source below. At
each prime $p$ with $P(p)\ge2$ the data give its index and
a real value $y_p$ or an erasure. In every sufficiently
large dyadic block $[N,2N)$ of indices at most
$O(N^{1-\kappa})$ eligible entries are bad, including each
erasure once and any unmarked corruption. At every good
index $y_p-H(P(p))=o(\sqrt{P(p)})$ uniformly in the tail.
Neither the bad set, the implicit bound, nor the noise
rate is given.

These data determine every nontrivial zero and its order
for the primitive inducer of each named character modulo
$q$, including shared points and central orders. With
$e=\min(\kappa/2,1/20)$, use at most $\lceil D/e\rceil$
meromorphic strip stages and one critical-line logarithmic
averaging stage. The spectral observable uses only the
supplied data and known parameters, not evaluations of
the defining prime sum or auxiliary zero tables. This is
exact asymptotic determination, not finite work, finite
precision stability, a result for arbitrary square-root
size noise, or a proof of GRH.

**Sources and payoff:** The [labelled triangle][labelled]
at `6596fa6e00f481978d7f2792eec2b3dde99a8a29` gives the
expansion, known square term, half-moment, and label
inversion. The [prime-index phase][phase] at the evidence
pin supplies the short-interval prime-mass input and
half-moment propagation template, but uses a different
operator and only threshold counts. The proposed new
consumer is strip peeling and line selection from noisy
prime-index scalar values.

**Discriminating test:** Partition large $[M,2M)$,
$M=2^j$, into $\lfloor M^e\rfloor$ equal half-open cells.
Check uniform prime mass versus the entire block's bad
budget, including endpoints and erased indices. After
subtracting already identified modes from individual
observations, test whether the median in every image cell
agrees with the remaining spectral sum to
$O(X^{\max(1/2,a-e/(2D))})$ when $\Re z\le a$. At
$a=1/2$, test the stronger $o(\sqrt X)$ error relative to
the line sum plus the known square term. Test whether
the residual median's Mellin germ has exactly the next
strip's poles, including infinite strips and intermediate
cuts, and whether the twisted logarithmic mean recovers
all line coefficients, including the center. Check
realness, finite bad prefixes, exact label decoding, and
same-label reflection.

[labelled]: ../closed/triangular-weighted-character-zero-divisors.md
[phase]: ../closed/order-two-prime-index-violation-phase.md

## Proof

**Every late cell has a majority, even against the whole block budget.**
Start at a dyadic $M_0$ chosen from $P$ alone so that $P$ is strictly
increasing on $[M_0,\infty)$ and $A=P(M_0)\ge2$. Use the partition
in the test; its image cells partition $[A,\infty)$. In a block starting
at $M$, each cell has length $L=M/\lfloor M^e\rfloor\asymp M^{1-e}$.
Use the prime-mass bound at [phase], lines 151–160 of the evidence
revision. Starting at the cell's left endpoint, pack successive
$(x,x+x^{9/10}]$ up to its right endpoint. Their total length is at
least $L-(2M)^{9/10}$, and their prime counts are bounded below by
their lengths divided by $2\log(2M)$. Discard at most one prime at
the excluded right endpoint. Since $1-e\ge19/20>9/10$, the cell
contains $n\gg M^{1-e}/\log M$ indexed primes, uniformly. The number
$r$ of bad entries there satisfies $r/n\ll M^{e-\kappa}\log M=o(1)$.
If $u$ of them are erased, $n-r>n/2\ge(n-u)/2$ entries are good
eventually. Thus even unmarked outliers all on one side cannot move
either middle rank outside an interval containing every good value.

**Recompute the median on each residual.** Use [labelled], lines
106–138 at its stated pin, in the form
$$H(X)=S_1(X)+C\sqrt X+o(\sqrt X),\qquad
S_a(X)=\sum_{\Re z\le a}c(z)X^z,\qquad
\sum_z |c(z)|(1+|z|)^{1/2}<\infty.$$
Here $C$ is known. The real weights give
$b_{\bar\chi}=\overline{b_\chi}$; conjugating the primitive functions
conjugates both the zero and the label. Hence $c(\bar z)=\overline{c(z)}$,
including reality at real zeros. At stage $a$ assume the data have
determined the terms strictly to its right (none initially at $a=1$).
Subtract their sum at **each nonerased sample's own argument** $P(p)$.
It converges absolutely there and is real by conjugation. Define
$m_a$ on each image cell to be the lower median of the resulting
values, or zero if there are none.

For $U\le V$ in an image cell, $X$ any point there, $X\asymp_P M^D$
and $P'/P=O_P(1/M)$ on the index cell. Thus
$v=\log(V/U)\ll M^{-e}\ll_P X^{-e/D}$. For $0\le v\le1$,
$|e^{vz}-1|\le\min(1+\exp(1),\exp(1)v|z|)$ by the triangle
inequality and integration. Taking the geometric mean of the bounds,
multiplying by $U^{\Re z}|c(z)|$, and summing gives
$$|S_a(V)-S_a(U)|\ll X^{a-h},\qquad h=e/(2D).$$
Compare each good residual at $U=P(p)$ with $S_a(X)+C\sqrt X$,
ordering the two arguments for the variation bound. The spectral
error is $O(X^{a-h})$, the square bias varies by
$O(\sqrt X\,X^{-e/D})$, and the expansion and measurement errors
are uniformly $o(\sqrt X)$ because $U/X\to1$ uniformly. The
majority transfers the same interval bound to the real median:
$$m_a(X)=S_a(X)+C\sqrt X+O(X^{a-h})+o(\sqrt X).$$
No bad index or noise rate is needed to construct it. This estimate
would not follow by subtracting a strip from an earlier median.

**Read the next open strip from the germ.** For $a>1/2$ set
$b=\max(1/2,a-h)$. The data give the Mellin integral of $m_a$ on
$\Re s>a$. There it equals
$$\sum_{\Re z\le a}\frac{c(z)A^{z-s}}{s-z}
 +\int_A^\infty (m_a(X)-S_a(X))X^{-s-1}\,dX.$$
The exchange uses absolute summability and $\Re s>a$. The integral
on the right is holomorphic on $\Re s>b$ by the uniform tail bound
$O(X^b)$. Arbitrarily large finite corruptions cause no difficulty:
On any bounded prefix there are finitely many bounded median values,
and integrating there adds an entire function. The pole sum is normal
on compacts avoiding its points: The exponential factors are bounded
there, only finitely many zeros are within distance one, and the
remaining denominators have modulus at least one. At each exposed
point the residue is $c(z)$, nonzero by the label inversion below.
Thus uniqueness of continuation fixes the poles and residues in
$b<\Re z\le a$ from the germ alone; the discrepancy integral proves
continuation and is not an input. Even an infinite strip can now be
subtracted at the samples by absolute summability. Reset $a=b$ and
recompute. Any intermediate lower edge is included as the next upper
edge. After at most $\lceil(1/2)/h\rceil=\lceil D/e\rceil$ strips
only $\Re z\le1/2$ remains.

**Read the line, then the labels.** At $a=1/2$ the median bound has
error $o(\sqrt X)$, not just $O(\sqrt X)$. After division by $\sqrt X$,
the strictly left terms tend to zero by domination by $|c(z)|$. Thus
$m_{1/2}(X)/\sqrt X-C$ is the absolutely summable line series
$\sum_{\Re z=1/2}c(z)X^{i\Im z}$ plus $o(1)$. For each real $t$,
average this observable times $X^{-it}$ over $[A,R]$ with measure
$dX/(X\log(R/A))$. For frequency difference $v\ne0$ the exponential
has mean $(R^{iv}-A^{iv})/(iv\log(R/A))\to0$; at $v=0$ it has mean
one. All means have modulus at most one, so the limit passes through
the series. The $o(1)$ error has zero mean in the limit, by splitting
off any fixed initial interval. This single family of limits gives
$c(1/2+it)$, zero at absent points, including the correct coefficient
at $t=0$ because $C$ was removed. An unknown $O(1)$ normalized noise
term would not suffice for this step.

In the notation of [labelled], $K(z)=((2^z-1)/z)^2\ne0$ in the
open critical strip. Write $d=\varphi(q)$ and $F=\mathbb Q(\zeta_d)$.
The coefficients of the powers $\alpha^j$, $0\le j<d$, in
$d c(z)/K(z)$ are $F_j=\sum_\chi\overline{\chi(g_j)}m_\chi(z)$.
These coordinates are unique: The Eisenstein degree $\ell$ of
$\alpha$ divides $[F(\alpha):\mathbb Q]$ and is prime to
$[F:\mathbb Q]\le d<\ell$, so $[F(\alpha):F]=\ell$ by the
polynomial upper bound. Then $d^{-1}\sum_j\psi(g_j)F_j=m_\psi(z)$
by orthogonality, also for $d=1$. In particular no point with a
positive order disappears, however many labels meet there. The
functional equation followed by conjugation preserves the label
and order under $z\mapsto1-\bar z$, filling the strictly left half.
The construction uses scalar observations, not threshold counts,
and requires neither exact clean samples nor a supplied zero list.
