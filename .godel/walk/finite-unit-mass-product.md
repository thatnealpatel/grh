# Finite Tamagawa unit masses give the reciprocal square root

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 25, claim in the paragraph beginning “Note also that the
infinite product of the volumes.” The product of the multiplicative
Tamagawa masses of the local integer units over all finite places is
said to have only finitely many nonunit factors and to converge to
“the square root of the absolute different.” This review ends before
“We define” and the display defining ρᵥ.

Chapter Markdown and PDF layout extraction located the passage and
normalizations. Direct inspection of crops from the rendered
[digest-verified PDF][source] confirmed the finite-support wording and
“square root of the absolute different” on p. 25, the p-adic absolute
value and square root in (A.3.2.2), p. 560, and the negative half power
of the different norm in both (A.3.1.2) and the finite additive mass
calculation in the proof of Lemma A.3.1.3, p. 556. These are distinct
from the positive half power used for the Archimedean additive mass
in that proof.

**Checked scope.** The finite-support claim is correct. The stated
value is false if “absolute different” means the positive norm of the
absolute different ideal. An ideal alone is not a positive real, and
reading the phrase as the finite idelic absolute value of a system of
local different generators would give the *reciprocal* of the positive
norm. That reading is a normalization clarification, not the
positive-norm equality.

In Masullo's normalizations (A.3.1.2) and (A.3.2.2), the multiplicative
unit mass equals the additive mass of the local integer ring. Thus the
finite product in Masullo's additive calculation also gives the
multiplicative product. Equivalently, at each rational prime p the
trace pairing after base change to ℤₚ is the orthogonal direct sum
of the local integral trace pairings at v above p. Taking determinants
in integral bases gives the p-adic discriminant factor as the product
of the local factors; a change of integral basis does not affect its
p-adic absolute value. If D is the absolute field discriminant, the
product is therefore

$$
\prod_{v \text{ finite}} \mu_v(\mathcal O_{F_v}^{\times})
= \prod_p |D|_p^{1/2}
= D^{-1/2}
= N(\mathfrak d_{F/\mathbb Q})^{-1/2}.
$$

Each local discriminant determinant lies in ℤₚ, so each factor is at
most one. For p not dividing D the factors above p are all one. For
F = ℚ(i), the basis (1, i) gives global discriminant −4, and the
[finite Gaussian audit] computes the sole place over 2 and its unit
mass 1/2. The product is 1/2, not 2. This correction does not affect
the product over places outside S when S contains every field-ramified
place; there each unit mass is one.

**Formal comparison.** At the inspected accepted revision
`440cba4511f9a646194d7d1eb732e8983a4a2c0e`, the [Lean measure module]
contains `Masullo.prod_finiteCompletionMultiplicativeHaar_unitMass`.
For a number field with the Borel measurable-space instances on the
finite completion unit groups, it multiplies the real values of the
actual constructed measures of the integral units over a finite set
containing the support of the global different. The right side is
`(Real.sqrt ((discr K).natAbs : ℝ))⁻¹`. The support lemma
`Masullo.finite_differentIdeal_multiplicity_support` in
[DifferentUnitScales] and `Masullo.finiteCompletionMultiplicativeHaar_unitMass_eq_one`
justify omitting the other places. The local theorem
`Masullo.finiteCompletionMultiplicativeHaar_unitMass_eq_sqrt_discr`
identifies the mass with the square root of the p-adic discriminant
norm for a supplied finite integral basis. The main endpoint is a
finite product with the corrected value, not an infinite-limit
statement, a Lean counterexample, or a statement about the volume of
an idèle class group. No Lean declaration was added or rebuilt here.

**Independent review.** Fresh Yah reviewer `JvouRSx` (output
`6c71e958e8a6bd112d0879a10e51a2b358fbe9e9`) checked the pinned pages
and those signatures at the exact accepted revision. The reviewer
independently recovered the reciprocal using local different
exponents and reproduced the ℚ(i) witness. The agreement is on the
scalar comparison, not on treating the ambiguous printed wording as
a definition of the norm convention.

[source]: ../sources/masullo/README.md
[finite Gaussian audit]: ../obligations/finite-gaussian-tamagawa.md
[Lean measure module]: ../../Proofs/Theorems/FiniteCompletionMultiplicativeHaar.lean
[DifferentUnitScales]: ../../Proofs/Theorems/DifferentUnitScales.lean
