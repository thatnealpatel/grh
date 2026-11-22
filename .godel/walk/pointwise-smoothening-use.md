# Smoothen-then-lift at a specified point

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 24, claim in the paragraph beginning “Part (4) teaches
us.” At a pair (x,y), the paragraph instructs the reader to smoothen
u at its quotient image and then apply the indentation lift Ψ. It
says the result is “exactly the smoothening” upstairs at (x,y),
without repeating a measure qualifier. The next paragraph, “We are
now back to the situation of interest,” is not reviewed here.

The [pinned PDF][source] matched SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction gave the paragraph.
Rendered pixel crops confirm “at points,” “exactly,” the closing
“at (x,y),” and the “almost all” qualifier on the cited equation
(1.3.1.11) on p. 23. Rendered-crop OCR cross-checks the prose.

**Scope of the citation.** As shorthand for item (4), the paragraph
inherits the product-Haar almost-everywhere qualification on its
value identity. The separate regularity equivalence in item (4)
asserts existence of limits, not their equality at a given pair.
Even a proof of product-Haar equality would not justify a specified
point or the [earlier application on skewered diagonals][skewers]:
When G is nondiscrete, the skewers are product-Haar null.

**Missing pointwise step.** Let P = π × π, z = (x,y), f = u ∘ P,
and w = u₀^Δ, so Ψ(u) = wf. Write Aₖ for normalized averages on
the ambient boxes at z. Masullo's unweighted step identifies Aₖf
with the quotient average at P(z), using Uₖ ⊂ D and the normalized
counting-measure quotient. If P(z) is regular, the specified-point
value identity then requires Aₖ((w − w(z))f) → 0. In Proposition
12.2.2.2(4), pp. 509 and 511–512, Masullo invokes Corollary
A.5.4.3 for this multiplier step; this later reading is provisional
from chapter Markdown. The reviewer's bound on the absolute error
is the oscillation of w relative to w(z) on the box times Aₖ|f|.
Continuity controls the oscillation, but convergence of signed
means does not supply a bound on Aₖ|f|. Bounded absolute means
would suffice for the value identity at that regular point; they
are an extra hypothesis, not printed here.

Separately, ambient and quotient almost-everywhere recovery by
differentiation, together with product-null pullback, would give the
product-Haar identity without this pointwise multiplier argument.
That is a conditional reading using the inputs identified in the
[differentiation audit][differentiation], not a check of Masullo's
general proof. No Lean endpoint for either scope was checked.

[source]: ../sources/masullo/README.md
[skewers]: skewered-smoothening-use.md
[differentiation]: differentiation-preview.md
