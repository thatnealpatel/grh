# Product averaging sequences and smoothening

**Printed passage.** Masullo, *The Music of the Primes*, printed
pp. 22–23, §1.3.1, unnumbered definition and claims from “We define
smoothenings” through “regular.” Masullo uses the product boxes
Uₖ × Uₖ and π(Uₖ) × π(Uₖ) as D′-sequences upstairs and on the
quotient product, respectively. He gives the one-group formula for a
locally Haar-integrable u: Take the limit of its integrals over xUₖ
divided by μ_G(Uₖ), wherever the limit exists. Such points are called
regular. He asserts almost-everywhere existence and measurability of
the resulting function. This passage ends before “Let now u₀ be a
continuous H-indentation.”

The [pinned PDF][source] was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The text was read in chapter Markdown and PDF layout extraction, with
OCR of rendered crops as a cross-check. Rendered pixel crops were
inspected for the two overbars on the quotient factors, the denominator
μ_G(Uₖ) and domain xUₖ, and the closing term “regular” on p. 23.
The Appendix A and Chapter 12 readings below are provisional as to
direct visual attestation: They come from extraction.

**Product calculation.** For K either G or G/H with its Haar
measure μ, assume the corresponding sets Vₖ really form a Borel
D′-sequence of relatively compact neighborhoods. In K × K, the
difference set of Vₖ × Vₖ is (VₖVₖ⁻¹) × (VₖVₖ⁻¹), so the
product Haar mass of the box is μ(Vₖ)² and its doubling ratio is
the square of the factor ratio. Borelness, nesting, and containment
of the identity pass to the product. For any product identity
neighborhood, choose a basic rectangle inside it, then use shrinking
and nesting to reach both components at the same index. This is the
reviewer's explicit calculation of the product argument that Masullo
gives in Lemma A.5.2.5, p. 570, and cites for product smoothenings
following Definition 12.1.1.1, pp. 498–499. For K = G/H this assumes
the [preceding quotient transport][quotient]. It does not establish
that the literal idele-class boxes are a shrinking base.

**Measurability and the open input.** For each k, the normalized
average is finite by local integrability and relative compactness,
and measurable by parameter integration of (x,z) ↦ u(xz) on
z ∈ Vₖ. If u is measurable for completed Haar measure, choose a
Borel representative first: Left translation preserves null sets,
so this does not change any of the averages at any x. A countable
Cauchy criterion gives a Borel regular set. The limit there is
measurable, as is its extension by zero off that set. This is the
reviewer's argument; it does not require a uniform continuity claim.
Masullo's “better behaved” does not specify an additional regularity
theorem. For instance, on ℝ with centered shrinking intervals, the
smoothening of the positive half-line indicator still has a jump
at zero.

Almost-everywhere convergence on the ambient group, or on a product
with product Haar measure, is the input needed from Theorem
A.5.4.1(2)–(3), pp. 582–583. The missing step in the printed proof
is [almost-everywhere recovery for locally integrable u without the
invalid boundary-null inference][differentiation] on p. 585. Even a
valid theorem of that scope does not give almost-everywhere regularity
with respect to Haar measure of the diagonal parameter. That would
need a separate argument about the specific kernels. No Lean endpoint
was checked for the product or smoothening assertions.

[source]: ../sources/masullo/README.md
[quotient]: quotient-dprime-transport.md
[differentiation]: differentiation-preview.md
