# Continuous indentation for a closed subgroup

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
claim beginning “Let G be a second countable,” printed pp. 21–22,
conditions (1)–(3) and equation (1.3.1.1). For a second-countable
Hausdorff locally compact abelian group G, a closed subgroup H,
and a chosen Haar measure μ_H on H, Masullo asserts the existence
of a continuous nonnegative real-valued function u₀ on G. Its
closed support must meet π⁻¹(π(K)) in a compact set for each
compact K in G, where π is the quotient map. The integral of
u₀(h⁻¹x) over H against μ_H must converge for every x and descend
to the constant 1 on G/H. This gives the asserted continuity and
H-invariance of the orbit integral. It is not an assertion of
compact support on all of G, and it does not assume H discrete.

The [pinned PDF][source] was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The support formula on p. 21 and the integrand and constant on
p. 22 were spot-checked in rendered pixel crops. The statement
and its page break were read from chapter Markdown and layout
extraction and cross-checked with raster OCR. Coverage stops
before the separate orbit-recovery assertion (1.3.1.2).

**Forward proof dependency.** The introduction states the claim
without proof. Lemma 12.2.1.1, printed pp. 504–505, states the
same existence claim and gives Masullo's construction using a
locally finite quotient cover, compactly supported functions on
G, and division by their sum's H-average. Masullo attributes the
construction to Bourbaki. The later statement and beginning of
the proof were located in the chapter Markdown and cross-checked
with raster OCR, not directly checked in rendered pixels. This
reference is a dependency on the general existence conclusion,
not on the lemma's separate orbit-recovery statement.

**What the construction needs.** The proof must arrange that
every fiber meets the *positive set* of the nonnegative sum f,
not just the projection of its closed support. The printed
containment Sₖ ⊂ π(supp ρ′ₖ) alone does not show this; the cited
lift is not checked here. To see the required choice directly,
take a locally finite, relatively compact open cover Uₖ of the
locally compact second-countable quotient, with a subordinate
partition of unity of compact supports Sₖ ⊂ Uₖ. For each point
of Sₖ choose one lift and a nonnegative bump positive there with
compact support inside π⁻¹(Uₖ). Openness of π makes the images
of the positive sets an open cover of Sₖ. A finite subcover
and the sum of the corresponding bumps give one function per
Uₖ. The sum f of those functions is locally finite and positive
somewhere in every fiber. Over any compact quotient set, only
finitely many Uₖ meet the set; the closed support of f there
is a closed subset of the finite union of the bump supports.

For x varying in a compact neighborhood L, the support of
h ↦ f(h⁻¹x) lies in H ∩ (L · C⁻¹), with
C = supp f ∩ π⁻¹(π(L)) compact. This is a fixed compact set
since H is closed. The integrands are bounded there, so the
H-average is finite and continuous by dominated convergence.
It is positive because each orbit meets the positive set and
Haar measure is positive on nonempty open sets. Left Haar
invariance makes the average H-invariant. Dividing f by this
average leaves its support unchanged and makes its H-average
one. This is the reviewer's unpacking of the cutoff and
normalization steps in Masullo's construction, not a formal
check of the general statement.

**Formal scope: Open.** The missing general Lean endpoint
must construct the quotient-locally compactly supported cutoff
and prove pointwise normalization for the chosen Haar measure
on an arbitrary closed H. The inspected source at revision
`3b8584b048a2c6a5fa82a87612add28a89e02e02` includes
`Masullo.monogenicPeriodization_cutoff_section` in
`Proofs/Theorems/MonogenicPeriodizationSection.lean`. It uses a
smooth, globally compactly supported real cutoff in real-log
coordinates and proves orbit recovery for smooth log-periodic
profiles by `HasSum` over an integer lattice with counting
measure. It does not supply the arbitrary group, subgroup, or
Haar-integral endpoint. No fresh Lean signature check or
independent formal review is asserted here.

[source]: ../sources/masullo/README.md
