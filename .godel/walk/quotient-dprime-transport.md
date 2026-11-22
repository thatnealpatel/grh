# Projecting a D′-sequence through a discrete quotient

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 22,
§1.3.1, unnumbered claim from “Say D is a fundamental domain” through
“is a D′-sequence for G/H.” Here G is second-countable, Hausdorff,
locally compact, and abelian, H is closed and discrete with counting
measure, and π is the quotient map. The hypothesis is a D′-sequence
(Uₖ) of relatively compact open symmetric identity neighborhoods, each
contained in the fundamental domain D. The claim is that (π(Uₖ)) is a
D′-sequence for G/H. It assumes (Uₖ); it does not construct one.

The [pinned PDF][source] was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction give the text. Rendered
pixel crops on p. 22 were checked for Uₖ ⊂ D, the image definition, and
the D′ conclusion on G/H; raster OCR also spot-checked the neighborhood
qualifiers. The Appendix A, Appendix D, and Chapter 12 readings below
are provisional as to direct visual attestation: They are based on
chapter Markdown and layout extraction (also raster OCR for the proof
text on p. 573).

**Measure comparison needed.** No proof accompanies this paragraph.
Write ν for the quotient Haar measure normalized by counting measure
on H. The nontrivial step is that ν(π(Uₖ)) = μ_G(Uₖ), whereas
ν(π(UₖUₖ⁻¹)) ≤ μ_G(UₖUₖ⁻¹). One cannot assume UₖUₖ⁻¹ lies in D or
that its measure is preserved. The reviewer’s indicator argument uses
the L¹ part of Theorem D.1.2.1, p. 747 (attributed there to [DE]):
For a relatively compact open B ⊂ G, the integral of the orbit count
of B is μ_G(B). This count is at least 1 on π(B), and equals the
indicator of π(B) if π is injective on B. Apply equality to B = Uₖ
by the fundamental-domain property, and the inequality to B = UₖUₖ⁻¹.
Because π is a homomorphism, this gives the same strict doubling
bound on the quotient as in Definition A.5.2.1, p. 569. The images
are open and contain the identity, inherit nesting and symmetry,
and shrink by applying the original shrinking axiom to preimages of
quotient neighborhoods. The two measure comparisons use only
injectivity on Uₖ, not compactness or measurability of D as a whole.

**Printed parallels and checked scope.** Situation 12.2.2.1, p. 508,
repeats the assertion. Proposition A.5.2.6, pp. 570–571, concerns a
two-way transfer with a relatively compact Borel global section E
whose interior contains the identity. Its proof on p. 573 asserts
transfer of doubling after the measure equality for Uₖ without
displaying the comparison on the product set. The forward indicator
argument above is not an invocation of that proposition, and it
checks neither its reverse direction nor its extra section hypotheses.
The subsequent product-sequence and smoothening assertions on p. 22
are outside this passage.

The accepted Lean source of `Masullo.lintegral_periodization` at
`0914c44c01168b68a96cf877d2a09fdfb0c4ebec` is a related nonnegative
integral identity for a countable fundamental domain, with a
restriction-pushforward measure and supplied measurable descent and
orbit-count identity. It does not state transfer of the D′ axioms
for the general topological quotient in this paragraph. The indicator
argument is a paper-level justification conditional on the stated
Weil formula, not a checked Lean endpoint; formal transport remains
open.

[source]: ../sources/masullo/README.md
