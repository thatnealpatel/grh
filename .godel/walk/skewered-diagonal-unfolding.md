# Unfolding an integrable smoothened diagonal

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 23, claim in item (2), equations (1.3.1.4)–(1.3.1.9).
Write Q = G/H and π: G → Q. In the standing second-countable
locally compact Hausdorff abelian setting with H closed discrete
and counting measure, let u₀ be a continuous H-indentation and
w = u₀^Δ the diagonal weight from item (1). The lift is
Ψ(u) = w · (u ∘ (π × π)), asserted measurable for a measurable,
locally integrable kernel on Q × Q. If the diagonal is regular
for quotient-Haar almost every parameter q, the smoothened
diagonal d(q) = ũ(q,q) is measurable and defined almost everywhere.
If d is absolutely integrable, the two skewered evaluations of
Ψ(ũ), at (h⁻¹x,x) and (x,h⁻¹x), are measurable for counting
measure times Haar measure in those coordinates, and defined for
every h on one Haar-conull set of x. Masullo equates the integral
of d on Q with the integrals of both skewered evaluations, in
both orders over D and H, and asserts absolute convergence.

The [pinned PDF][source] was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction give the full item.
Rendered pixel crops verify the item opening, lift formula,
regularity wording, equation labels, and second-coordinate
skewer in the last two displays. In the locally integrable kernel
hypothesis, read the p. 23 quotient-Haar notation as product Haar
on Q × Q, as in the later proof, and use single quotient Haar for
q ↦ d(q). Coverage stops before item (3).

**Conditional paper-level check.** Use a measurable exact section
D such that the pushforward by π of μ_G restricted to D is the
normalized quotient Haar measure ν. For a Borel section this is
Proposition D.1.2.4, (D.1.2.5), p. 748 (provisional reading from
appendix Markdown). In particular,
quotient-null sets pull back to null sets on D and then on G by
the countable cover by H-translates; H is countable by discreteness
and second countability. The same argument for D × D, with ν × ν,
applies to the product quotient. Thus pullback preserves completed
measurability, not only Borel measurability. Multiplying the pulled
back kernel by the continuous weight proves measurability of Ψ(u).

For the diagonal, take a Borel representative of u modulo product
Haar null sets. This does not change any fixed translated average.
The averaging functions are Borel by parameter integration of the
translated kernel on the fixed product neighborhoods. Restrict each
average to q ↦ (q,q), use the countable Cauchy criterion for the
regular set, and take the limit there, extending by zero elsewhere.
This gives a Borel d. The assumed diagonal regularity and null
pullback give a single Haar-conull set on G for both skewers and all
h. This does not restrict an arbitrary completed product-measurable
representative to a null diagonal or deduce diagonal regularity from
product-almost-everywhere differentiation.

For each x put b(a) = u₀(a⁻¹x) for a in H. The b(a) are nonnegative
and sum to one. Summing w(h⁻¹x,x) first over h gives
Σₐ b(a) Σₕ b(ha) = 1, by reindexing nonnegative sums. Symmetry of
w gives the same result for w(x,h⁻¹x). Both pullbacks of ũ on the
skewers are d(π(x)). Consequently the counting integral of the
absolute value of either skewered lift is |d(π(x))|. Its integral
over D is ∫_Q |d| dν by the section identity and is finite by
hypothesis. Tonelli gives absolute integrability, Fubini allows
both orders, and the same weight normalization without absolute
values gives the four displayed equalities.

This is the reviewer's countable-sum and Borel-average version of
Masullo's argument in Proposition 12.2.2.2(2), statement on p. 508
and proof on pp. 509–511 (provisional readings from chapter Markdown).
The fixed-h equality uses symmetry of the product weight, not
invariance under simultaneous H-translation alone. Absolute
integrability is checked before interchanging complex integrals.
Item (2) lifts the already smoothened kernel; commuting the lift
with smoothening is a separate claim in item (4).

**Formal scope: Open.** The assumption of a fundamental domain on
p. 22 needs a measurable section with the normalized restriction
identity, not just a set of orbit representatives. The check above
does not verify that a specific later idelic domain qualifies. No
general Lean endpoint combining the Borel diagonal limit, the
skewered counting normalization, and both orders of integration
was checked. The inspected source of `Masullo.integral_periodization`
(`Proofs/Lemmas/FundamentalDomainQuotientMeasure.lean`, revision
`3b8584b048a2c6a5fa82a87612add28a89e02e02`) gives the one-variable
complex Borel L¹ Weil identity for the restriction-pushforward
measure, with a countable fundamental domain and a supplied
measurable descent and periodization identity. It verifies neither
the diagonal smoothening nor the two skewered integrals. The
conditional unfolding does not check regularity or integrability
for any spectral or geometric kernel.

[source]: ../sources/masullo/README.md
