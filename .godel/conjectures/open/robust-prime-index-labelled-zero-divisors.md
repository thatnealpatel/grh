---
evidence_revision: 2a477e0bed19c2a3cfb88cf77d82a22104d69272
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
