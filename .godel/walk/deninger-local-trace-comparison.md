# The Deninger local-trace comparison is not supplied

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.10,
printed p. 20, paragraph beginning “These ‘local’ trace formulas,”
including footnote 2. The paragraph says the preceding formulas
fulfill Deninger’s expectations and points to the “local traces” in
C. Deninger, *Lefschetz trace formulas and explicit formulas in
analytic number theory*, J. Reine Angew. Math. 441 (1993). It gives
no equation or particular statement from that paper. The comparison
wording and footnote marker were spot-checked in rendered pixels of
PDF page 20, separately from the chapter Markdown and PDF text
extraction. The [pinned edition](../sources/masullo/README.md) was
verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The following §1.2.11 is outside this finding.

**What would establish the comparison.** Identify the particular
local trace distributions meant in the cited paper and prove
place-by-place equality with the operator traces of §§1.2.9–1.2.10
on a common test class. In particular, specify the transport of
the test and character, the direction of norm time, the Haar
normalization, and any correction on the trivial isotype. The
paragraph gives neither that correspondence nor an argument for it.
Deninger’s own text was not checked in this review.

Even before that comparison, the two introductory trace inputs
remain open at their printed scope:

- The [finite-place claim](global-orbital-mellin-trace.md), pp. 18–19,
  needs the nuclear trace identity on the intrinsic global
  two-zero-moment quotient by the introductory principal-value
  range. The claimed trace is indexed by a rational prime $p$ and
  a fixed norm-one character. Applying Poisson summation to its
  scalar Mellin expression is not by itself a comparison of
  single-place traces: Disintegrating the Mellin integral gives
  character-weighted integrals on norm fibres, not the unweighted
  uniformizer point samples printed on p. 19.
- The [Archimedean claim](archimedean-orbital-preview.md), p. 19,
  needs a trace identity on the introductory $S$-local quotient of
  the full theta isotype by the Archimedean-flat image. It takes a
  test on $J_{F,S}$ but integrates it over $C_F$ without specifying
  a transfer. The later global two-zero-moment matrix trace also
  has a subtraction on the trivial isotype; it does not identify
  the introductory local trace.

The comparison is Masullo’s assertion. The required identification
of test distributions and the distinction between scalar and operator
inputs are the reviewer’s. This note neither verifies nor refutes the
comparison, and uses no Lean declaration.

## The reprise in §1.5.2

**Printed passage.** Printed p. 33, second paragraph of §1.5.2,
from “The local traces that Deninger contemplated” through “the
Schauder bases on each.” Masullo says that *all* the contemplated
local traces are realized as actual trace formulas using orbital
subquotients of both local and global theta spaces and their
Schauder bases. Chapter Markdown and PDF layout extraction
located the paragraph; raster OCR checked the prose, and direct
inspection of crops of the rendered pinned page spot-checked the
realization assertion, “local and global,” and the basis wording.
The following paragraph about the role of visualization is
separate.

**Which traces are on offer.** Theorem 7.4.2.1(2), p. 367,
asserts a strongly nuclear trace on a **global** two-zero-moment
quotient by the unit-averaged principal-value range, grouped by
rational prime rather than by place. Theorem 7.4.3.2(2),
pp. 372–373, asserts a **matrix** trace in a specified basis on
a global Archimedean quotient for tests supported strictly above
norm one, with a subtraction on the trivial norm-one isotype.
Neither statement concerns the corresponding full $S$-local
isotype. Remark 7.5.0.2, pp. 378–379, uses a two-zero-moment
local numerator in the finite-place comparison; it does not
identify the full local quotient. See the [insertion audit] for
the moment obstruction to that identification by inclusion.

In §8.4, pp. 392–393, Masullo invokes the two global trace
results for the $S$-local pieces and labels the combined argument
in (8.4.0.10)–(8.4.0.11) heuristic. He points to Deninger’s
Theorem 1.7(4) in connection with that argument. The chapter
references here are provisional, from chapter Markdown and
text extraction. The $S$-local cutoff diagonal in Theorem
12.4.1.1, p. 514, is a different calculation: Its place integrals,
even if obtained for the admissible tests, do not identify them
as traces on the stated orbital quotients.

**Open step.** First justify the finite-place nuclear trace and
the Archimedean basis trace on their actual quotients, and prove
that the $S$-local quotient actions yield the corresponding trace
functionals, either by direct local computations or by continuous
convolution-intertwining comparisons compatible with the moments,
quotient ranges, traces, and correction terms. Then identify
the cited Deninger distributions and prove equality place by
place on a common test class, even starting with one norm-one
isotype and compactly supported tests strictly above norm one.
This must specify the character-weighted test transfer, Haar
factors, time convention and half-norm twist, and where the
trivial-isotype correction belongs. A scalar Mellin sum or a
Poisson or residue evaluation of it does not prove the operator
identity. The proposed realization is Masullo’s; the distinction
between these comparisons is the reviewer’s. Deninger’s own text
was not checked, and no Lean claim resolves the printed assertion.

[insertion audit]: orbital-subquotient-comparison.md
