# The global orbital Mellin trace needs a nuclear expansion

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.9,
printed p. 18, claim beginning “For each φ”, including the global
setup, the Mellin trace display, and the paragraph identifying the
summation set. For every test $\varphi\in\mathcal D(C_F)$, the
induced convolution on the global $p$-primary quotient of the
norm-one isotype of the two-zero-moment theta space is asserted to
be nuclear. Its trace is stated to be

$$
\sum_{\varepsilon_p} N(\chi|\cdot|_F^{\varepsilon_p})
\int_{C_F}\varphi(g)\chi(g)|g|_F^{\varepsilon_p}\,d\bar\mu(g),
$$

where $\varepsilon_p$ runs over the distinct zeros of the product
of the reciprocal Euler factors above $p$ on the character
component of $\chi|_{C_F^1}$, and $N$ is their multiplicity. The
nuclearity wording and display were inspected in rendered pixels
from PDF page 18, independently of the chapter Markdown, text
extraction, and raster OCR used for the surrounding paragraphs.
The [edition](../sources/masullo/README.md) was verified against
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The Poisson formula on p. 19 is a separate claim.

**What the calculation explains.** Write $M(\varphi)(s)$ for the
integral in the display at $s$ in place of $\varepsilon_p$. If
the quotient has the asserted Mellin jet coordinates, the
transpose acts on each jet block by the product rule for
multiplication by $M(\varphi)$. In the block of orders $0$ through
$N-1$, the matrix is triangular and each diagonal entry is
$M(\varphi)(\varepsilon_p)$. This verifies the proposed
finite-block coefficient conditionally, not nuclearity or the
trace of the infinite sum.

**Open step.** The local Schauder assertion does not by itself
identify a global jet basis in the intrinsic topology of the
two-zero-moment quotient by the *actual* principal-value range.
One route is an equivariant topological isomorphism to the
periodic product-difference model with the matching factors.
For such a route one needs the actual inverse-image equality
between the model difference range and the global
principal-value range, and surjectivity modulo the model range.
Even with the correct global basis, a trace argument needs a
summable rank-one presentation with equicontinuous input
functionals and output vectors bounded in one Banach disc, and a
justification that the trace is its diagonal sum (cf. Lemma
C.3.1.2 and Proposition C.3.2.1, p. 694). Rapid decay of scalar
Mellin derivatives does not by itself give the needed control
of the normalized global jet functionals and their biorthogonal
vectors. Theorem 7.1.4.3(2)–(3), pp. 331–332, supplies a stated
ambient dual density and topological freeness/biorthogonality
result, not those estimates on this quotient. The proposed
comparison in Theorem 7.5.0.1, pp. 374–378, would require matching
the ranges and topologies, and invokes the local basis whose
[range comparison is open](local-orbital-schauder-basis.md).

**Scope of the later proof.** Theorem 7.4.2.1, p. 367, asserts
closedness and the same formula with strong nuclearity. It uses
the later unit-averaged principal-value product. At a ramified
place the corresponding Euler factor is 1, so it omits that
place, whereas the literal introductory uniformizer difference
retains a lattice of multiplier zeros. Unramifiedness at each
place above $p$ would make the two operators agree; it does not
supply the missing nuclear estimates. Masullo invokes the
renormalized rank-one expansion used for Theorem 7.4.1.1 and
refers to the block trace calculation at (11.2.2.12), p. 491, in
Theorem 11.2.2.1. The latter calculation is for a weighted Hilbert
quotient and assumes
unramifiedness above $p$ and Sobolev order $s\ge 2[F:\mathbb Q]$.
Its Hilbert-space bounds do not directly transfer to the
intrinsic quotient. See also the [rational zero-line range
audit](../obligations/trace-orbital-q.md), which distinguishes
that completion from the topology here. These later readings
are provisional, from chapter Markdown and PDF text extraction.
The nuclear trace assertion and jet strategy are Masullo's; the
conditional block calculation and scope comparison are the
reviewer's. No Lean statement is used to resolve this passage.
