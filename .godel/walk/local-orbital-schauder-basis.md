# The S-local orbital basis requires a quotient comparison

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.9,
printed p. 18, claim that the S-local p-primary orbital quotient
carries an absolute Schauder basis. The paragraph calls it a copy of
the twisted exponential system on the single-uniformizer quotients
and invokes explicit constructions and open mapping. The preceding
“But then” sentence introduces this analogy, not another identity.
The assertion and comparison were inspected in pixel crops rendered
from p. 18 of the pinned PDF, SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`,
with the chapter Markdown, PDF text extraction, and raster OCR used
separately to read the surrounding prose. The next paragraph turns
to a global trace, which is a separate passage.

**Later argument.** Theorem 7.3.1.6 (pp. 344–349) assumes saturated
finite $S$, including the Archimedean places and $S_p$, trivial
$S$-class group, and the character choices of Situation 7.3.1.1.
It asserts absolute bases in the primal quotient, biorthogonal to
the strong-dual bases of principal-part functionals and of
Fourier–Mellin jets. The derivative orders at a shared frequency
run up to one less than its multiplicity. This describes a model
for a product of differences, not a literal copy of just one
single-place basis when factors overlap. Masullo proposes to
transport the model basis of Theorem 4.6.1.5 (p. 212) through the
quotient comparison (7.3.1.19), using the surjectivity mechanism of
Corollary 4.6.3.1 (p. 219). These later readings are provisional,
from the chapter Markdown and PDF text extraction.

**Open step.** Write $H$ for the full local theta isotype and $A$
for the Fourier, norm, and theta map into the first model space
$Y$ in (7.3.1.19). Before applying open mapping in that route,
one needs $A^{-1}(P_XY)=\mathrm{PV}_{S,S_p}H$, surjectivity modulo
$P_XY$, and the hypotheses making the two quotients Fréchet in
their stated topologies. Multiplication by an Euler factor does
not prove the reverse inclusion in the inverse-image equality.
In particular, the proof at p. 349 cites Theorem 7.3.1.2(2) with
$S_0=S_p$ to pass from the pole-order condition to membership in
the principal-value image. Theorem 7.3.1.2 (p. 341) requires
$S_0$ to contain all Archimedean places. The finite-only range
criterion actually used needs a justification, not just continuity
of the coefficient functionals. These readings are also provisional.

The operator convention matters before that step: The
[introductory product](orbital-mellin-multiplier.md) uses literal
uniformizer differences while the later theta quotient uses the
unit-averaged factors. At a ramified place the latter factor is the
identity on that isotype, but the literal difference still has a
lattice of multiplier zeros. Therefore the later proof's comparison
with a literal periodic product over all $v\mid p$ needs matching
operators, for example by checking the argument with unramifiedness
at every $v\mid p$, or by specifying a model omitting the ramified
factors for the averaged product. Neither change proves the general
introductory claim. The printed claim and proposed transport are
Masullo's; the scope comparison and identification of the missing
range step are the reviewer's. No Lean declaration is offered as
proving or refuting the basis claim.
