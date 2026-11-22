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
