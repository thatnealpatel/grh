# The loci in the introductory orbital diagram

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.11,
printed p. 20, the paragraph from “The row below it indicates” through
“endowed with the subspace topology,” read with the middle row of the
preceding diagram. The diagram associates the polar-free isotype with
the all-nonzero stratum, the full isotype with the space of points with
at most one vanishing coordinate, and the orbital product with the
primed union of the one-zero strata, all modulo the norm-one S-ideles.
Masullo describes these as loci on which the spaces are supported. He
sets $D_{S,1}=\mathrm{GL}_1(\mathbf A_{F,S})$, $D_{S,v}=H_v^\times$,
and gives their union $D_{F,S}$ its subspace topology in
$\mathbf A_{F,S}$. The support wording, locus definitions, and direction
of the middle-row arrows were spot-checked in rendered pixels of PDF
p. 20, separately from the chapter Markdown and PDF text extraction.
The PDF matches the [pinned edition](../sources/masullo/README.md),
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The [top-row exactness claim](orbital-product-exactness.md) and the next
paragraph on the individual orbital pieces are separate passages.

**Checked scope.** In the finite product of local fields each one-zero
stratum is obtained by translating the point with all other coordinates
one. Its description by vanishing of that coordinate in $D_{F,S}$
displays it as relatively closed there. The all-nonzero stratum is
open, and multiplication by a norm-one idele preserves the zero
pattern. This checks the underlying loci and their inclusions. These
observations alone do not make any of the vector spaces in the top row
a sheaf or bundle on the quotient stack.

**Disposition.** The stack-support assignment is an open analytic
preview, not a construction of the vertical arrows. Masullo later
repeats the diagram in (8.4.0.6), p. 390, and describes those vertical
arrows on p. 391 as intuition, not morphisms. For a distributional
interpretation of the orbital column, one needs to specify how the
continuous duals of the stated subquotients pull back to test-space
duals and prove that the resulting equivariant distributions, when
restricted to $D_{F,S}$, vanish on tests off their indicated strata.
Theorem 8.3.0.1, pp. 387–388, is a lead for this only under its
additional hypotheses, including trivial S-class group and a global
character unramified outside $S$. It is phrased in terms of replacing
the test by one supported on the stratum, not as a construction of a
Fréchet bundle. No support notion for the full diagram or proof of these
localization maps is supplied in the introductory paragraph. The
Chapter 8 readings here are provisional, from chapter Markdown and
PDF text extraction. The support assignment is Masullo's; the
zero-pattern check and distinction from analytic localization are the
reviewer's. No Lean declaration is used.
