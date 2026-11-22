# The one-variable lift assumed in §1.3

**Printed passage.** Masullo, *The Music of the Primes*, §1.3,
printed p. 21, setup paragraph beginning “We are, for the moment,
giving for granted.” Masullo assumes a scalar-valued measurable
kernel on GL₁(A_F) × C_F with unspecified extra integrability
inherited from the spectral kernel, although the global geometric
kernel is given on C_F × C_F. This paragraph does not construct the
lift or specify the integrability norm. Both product domains were
spot-checked in rendered pixel crops of the [pinned PDF][source],
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The prose and paragraph boundary were read from the chapter Markdown
and layout extraction and cross-checked with raster OCR.

**Open lift and integrability interface.** A pullback along the
idele-class map in one variable is measurable once the quotient
kernel is measurable, but it is constant on each principal orbit in
that variable. It is not a summable orbit lift at points where the
kernel is nonzero. The recipe in §1.3.1, p. 24, instead writes a
convolution lift minus a doubly indented spectral term on two copies
of GL₁(A_F), then uses the second named variable for the cut. The
weight obtained by translating both indentation factors together is
invariant under the simultaneous action of F×, not separately
invariant in either variable in general. Simultaneous invariance
alone therefore does not construct a kernel on GL₁(A_F) × C_F.
To use the assumed kernel, identify a descent or partial periodization
of the actual lift, specify which coordinate remains idelic for the
cuts, and show that the resulting orbit recovery and skewered Haar
diagonal agree with those of the same quotient kernel in (1.3.1.12).
An unrelated lift satisfying orbit recovery is not this comparison.

For the introductory twist 1/2, nondegenerate symmetric base, degree
s=0, fixed norm-one isotype, and test supported strictly above norm
one, the p. 24 discussion specifies weighted product L² and absolute
Haar integrability of the averaged quotient diagonal. Identify the
spectral kernel of the intended operator in the Haar convention
before taking this difference and prove diagonal regularity and
absolute integrability for that same kernel and compatible averages
of its lift. Product L² convergence alone gives neither of these
diagonal conclusions. Definition 10.4.3.7, pp. 473–474, is stated for
s≥3, not the introductory s=0. Proposition 12.2.2.2(2), p. 508,
unfolds an already regular, absolutely integrable averaged quotient
diagonal for its particular two-variable lift; it does not prove
those prerequisites. See the [spectral audit][spectral] for the
conditional Haar conversion and diagonal argument.

The assumption and the later lift recipe are Masullo's. The
separation of measurable pullback, orbit recovery, partial descent,
and diagonal control is the reviewer's. The later passages were read
from chapter Markdown and PDF extraction and are provisional, not
rendered-page checks. No Lean result is used.

[source]: ../sources/masullo/README.md
[spectral]: ../obligations/trace-spectral.md#from-the-weighted-kernel-to-the-haar-diagonal
