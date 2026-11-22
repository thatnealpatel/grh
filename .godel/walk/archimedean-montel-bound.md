# The Archimedean bound before Montel

**Status: Open as a formal finding.** Masullo, *The Music of the
Primes*, printed p. 29, claim in §1.4.3, “Montel's Theorem,” from
“Fix a compact subset” through the explanation of the common bound.
The chapter Markdown and layout extraction located the passage in the
[digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the prose. Direct inspection of rendered pixel crops checked
the half-planes defining the condition on $K$, the unbarred $\chi$ in
the lift, and the denominators $|1-t|$ and $|1-te^{i\theta}|$.
The remaining transcription uses the extraction. This finding stops
before “By Montel's Theorem.”

Masullo asserts a common bound for the two displayed Archimedean
expressions, independent of both $z\in K$ and the specific test. The
argument needs a bound in modulus, though the text says “bounded
above.” The appeal to finitely many Archimedean places does not bound
even the single real-place term. The explanation also previews the
finite-place logarithmic derivative limit asserted in §1.4.4; that is
a separate comparison, not a premise for analyzing the printed integral.

The [existing project check](../obligations/trace-to-zeros.md#two-proposed-deductions-not-two-proofs),
previously reviewed against extraction, applies to the rendered
real denominator. Take $F=\mathbb Q$, $\chi=1$, and a real $z_*$
strictly greater than $\max(1,\sup I)$. A sufficiently small closed
disc centered at $z_*$ is an admissible $K$. Choose nonnegative
smooth approximate identities and cutoffs as in
[§1.4.2](holomorphic-test-family.md), with $\varepsilon\to0$ and
$h\to1_{(1,\infty)}$. Write $a_n(t)$ for the resulting nonnegative
scalar profiles at $z_*$. The real norm of $tu$ is $t$ for both
$u=\pm1$. The two terms add and cancel the factor $1/2$, giving

$$
A_n=\int_1^\infty a_n(t)\frac{t^{-1/2}}{t-1}\,dt.
$$

Each $A_n$ is finite because the test is compactly supported away
from $t=1$. On $(1,2)$, the pointwise limiting integrand is
$t^{-z_*-1/2}/(t-1)$; its integral is infinite by comparison with
$1/(t-1)$. Fatou's lemma gives $\liminf_n A_n=+\infty$ at this one
real parameter. Correcting the [real sign denominator](characterwise-trace-formula.md)
leaves the positive branch, which already diverges with its factor
$1/2$. A term proportional to the value at the identity is zero for
every cutoff here. The obstruction neither needs a trace identity
nor depends on the character-lift problem for nontrivial $\chi$.

A limiting argument needs subtraction or another normalization that
accounts for the $t\downarrow1$ singularity and is compatible with
the entire trace identity. For instance, the project's conditional
[rational repair](../obligations/trace-to-zeros.md#fixed-parameter-subtraction-over-the-rationals)
uses the difference $e^{-zx}-e^{-z_0x}$ in log norm $x$, which is
$O(x)$ at zero, rather than one exponential. The
[Lean cutoff results](../obligations/trace-divisor-cutoff-profiles.md)
bound weighted scalar integrals or prove Laplace limits for the
subtracted profiles; they do not prove the original Archimedean
bound, a trace identity, or a zero-location theorem for this passage.
No new Lean claim is made.
