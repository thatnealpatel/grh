# Evaluating the ambient smoothening on skewered diagonals

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 23, application paragraph beginning “Point (2) teaches
us.” It says to compute the integral of the smoothened quotient
kernel on its diagonal using integration over D and H of the
values of the *smoothening of the lift* Ψ(u) at (h⁻¹x,x) and
(x,h⁻¹x). This is the paragraph after item (4), not the next
paragraph about multipliers on p. 24. The [pinned PDF][source]
matched SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction give the paragraph.
Rendered pixel crops confirm the displayed lift of u (not ũ)
and the two skewers; OCR of the crop cross-checks the prose.

**Open interface.** Item (2), equations (1.3.1.4)–(1.3.1.9),
integrates Ψ(ũ), the lift of an already smoothened kernel. Its
conditional [unfolding check][unfold], using the normalized
measurable fundamental domain and counting Haar on H, does not
integrate the ambient smoothening of Ψ(u). Replacing the former
by the latter requires knowing that the normalized ambient box
averages at each skewer converge to Ψ(ũ) there for counting ×
restricted Haar almost every (h,x). Equivalently, by countability,
one Haar-conull set in D may be used for all h and both skewers.
The product-Haar almost-everywhere equality in (1.3.1.11) does
not supply this: In a nondiscrete G the skewers are product-Haar
null by Fubini, even though they carry single-variable Haar in
the computation. The pointwise regularity equivalence claimed
separately in item (4) is not a substitute for the value equality.
The later Proposition 12.2.2.2(4), printed p. 509, also states
its value equality for product-Haar almost every pair, not for
Haar almost every point of each skewer (provisional extraction
for this later locator).

**Sufficient extra input, not a check of the printed general
use.** Write P = π × π, f = u ∘ P, and w = u₀^Δ. At either
skewer z above q = π(x), let Aₖ denote the normalized ambient
box average. Its unweighted average Aₖ f is the quotient box
average at (q,q), by injectivity and the normalized slice measure
on each Uₖ ⊂ D. The same holds for Aₖ|f|. The difference between
Aₖ(wf) and w(z) Aₖ f is bounded by the oscillation of w relative
to w(z) on the box times Aₖ|f|. Thus bounded normalized absolute
quotient averages at (q,q), in addition to the signed diagonal
limit, suffice because w is continuous and the boxes shrink.
The bound is required on a quotient-Haar conull set of diagonal
parameters. The signed limit and L¹ integrability of its diagonal
do not themselves furnish that bound. Once the skewered values
are identified, the absolute convergence and equality of integrals
come from item (2), not from product differentiation.

This is the reviewer's conditional comparison, not Masullo's
argument establishing the missing hypothesis. The [spectral
audit][spectral] supplies an absolute-average bound for an
identified trace-class kernel using a singular-value expansion
and actual shrinking boxes. That repair does not identify the
manuscript's kernels or verify its choice of boxes. No Lean
endpoint for the required skewered limit equality was checked.

[source]: ../sources/masullo/README.md
[unfold]: skewered-diagonal-unfolding.md
[spectral]: ../obligations/trace-spectral.md#from-the-weighted-kernel-to-the-haar-diagonal
