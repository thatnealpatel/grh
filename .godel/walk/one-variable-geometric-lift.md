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

## The first-coordinate preview

**Printed passage.** §1.3, printed p. 21, paragraph beginning
“This is one of the aspects we will be discussing.” Masullo says
he will lift the kernel in the first of its two variables, from
C_F × C_F to GL₁(A_F) × C_F. The wording “first of the two”
and the target product were spot-checked in rendered pixel crops
of the same pinned PDF. The paragraph as a whole was read in
chapter Markdown, layout extraction, and raster OCR. It announces
a construction, but does not give one.

The p. 24 recipe is on two idelic coordinates and cuts in the
argument written as y, on a provisional reading of the chapter
Markdown and PDF extraction. The final bullet of §1.3.2, p. 27,
calls y the first variable by convention, though listed second.
The convention wording was spot-checked in rendered pixels and
cross-checked with raster OCR. Thus a difference in argument order
need not be a contradiction. It still matters which variable is
kept idelic: It must be the argument on which the divisorial
indicators act.

**Open comparison.** Even if the p. 24 lift has absolute orbit
recovery, plain orbit summation in its non-cut argument does not
produce the advertised summable lift. Write K(x,y) for the
simultaneously F×-invariant lift, with y the cut variable. For
any h₀ in F×, K(hx,h₀y) = K(h₀⁻¹hx,y), so where the orbit sum
converges absolutely, ∑ₕ K(hx,h₀y) = ∑ₕ K(hx,y) by reindexing.
The sum is then principal-invariant in both variables. A further
orbit sum in y diverges wherever this value is nonzero. One can
instead multiply the quotient kernel pulled back in y by a
normalized one-variable indentation, which restores orbit
recovery. That choice alone does not identify the terms cut from
K or compare their averaged skewered diagonals. The missing step
is a construction for the actual geometric lift, retaining y and
showing orbit recovery and the quotient-Haar diagonal comparison
with (1.3.1.12) under compatible averages. The reindexing and
the distinction between the two constructions are the reviewer's
observations, not a formal verification of Masullo's preview.

[source]: ../sources/masullo/README.md
[spectral]: ../obligations/trace-spectral.md#from-the-weighted-kernel-to-the-haar-diagonal
