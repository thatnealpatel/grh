# The two-idèle geometric lift in §1.3.1

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 24, first bullet beginning “We lift” after “The key
points of this subsection.” Write G = GL₁(A_F), H = F×, and
π: G → C_F. Masullo places the smooth compactly supported test
φ̃ on G × G, but then uses it with one argument both in the
periodization ∑ξ φ̃(ξx) = φ(π(x)) and in the kernel formula
`K_geom(x,y) = φ̃(xy⁻¹) − Ψ^Δ(k_spec)(x,y)`, where Ψ^Δ denotes
his diagonal indentation lift for the chosen u₀. He says he will
choose u₀ using the domain τ(ℝ₊) · E_F¹.

The [pinned PDF][source] matched SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and layout extraction supplied the bullet.
Direct inspection of rendered pixel crops confirmed the product
in the domain of φ̃, the unary use in the periodization and the
kernel, and the fundamental-domain notation. This is only the
first bullet, not the diagonal-mass equation in the next bullet.

**Domain mismatch and a conditional repair.** Neither unary
expression evaluates a function on G × G as typed. The natural
repair is φ̃ in 𝒟(G). Compact support is then a property of φ̃,
not of its pullback along (x,y) ↦ xy⁻¹. For any point z where
φ̃(z) ≠ 0, the nonzero set of the pullback contains every
(zy,y), whose second projection is all of the noncompact G.

For the repaired test lift, use discreteness of H to choose
relatively compact open sheets of π over neighborhoods of the
compact support of φ. In those sheets choose finitely many
nonnegative Bruhat-smooth bumps whose positive sets project to
a cover of that support. Such bumps are made from smooth
Archimedean bumps and compact-open finite-idèle neighborhoods.
Write b for their sum. Its H-periodization P b is locally a
finite sum of translates, by compact support and closed
discreteness of H. Via the local sheets it descends to a smooth
function positive on a neighborhood of supp φ. On the inverse
image of that neighborhood, define φ̃ = b · ((φ / P b) ∘ π), with P b
viewed on C_F; extend by zero away from π⁻¹(supp φ) wherever
the denominator vanishes. This is smooth and supported in
supp b, and summation over H recovers φ at every class. This
is the reviewer's repair, not a proof of the product-domain
wording. Masullo makes a one-variable choice at (12.4.1.4),
p. 515, for S-idèles and S-units, not the global formula here. That
later comparison is provisional from chapter Markdown.

**Indentation input.** With τ an idelic norm section (for example
(A.2.2.11), p. 547, provisionally read in the appendix Markdown),
the map (t,g₁) ↦ τ(t)g₁ is a homeomorphism from ℝ₊ × G¹ onto G,
and H acts only on G¹ by the product formula. The domain claim
then needs E_F¹ to be a Borel, relatively compact transversal
on G¹, as in Definition A.2.3.6 (p. 549) and Proposition
A.2.3.10(1)–(2) (p. 552), provisionally read in the appendix
Markdown. Given that input, a continuous compactly supported
nonnegative cutoff on G¹ that is one on the closure of E_F¹
has a positive, locally finite continuous H-periodization.
Dividing by the periodization and extending constantly in the
norm coordinate gives a continuous normalized indentation on G.
Its support over a compact subset of the quotient is closed
in the product of a compact band of norms and the compact
support of the norm-one cutoff. This spells out a possible
choice using Masullo's domain. Its bare indicator is normalized
but need not be continuous, as required for the earlier lift.

For a supplied continuous normalized indentation, its diagonal
weight is finite and continuous by the local compact-support
argument in the [weight audit][weight]. Fix a finite Borel
representative of the spectral kernel. The repaired
formula is a measurable two-idèle kernel. In fact, summing
the diagonal weights over translations of the second variable
gives one: Sum first the translates of u₀ in the second factor,
then those in the first, using normalization and nonnegativity.
The test term also recovers its quotient value under that
summation, with finite support on each orbit. This is orbit
recovery before averaging, not a statement about absolute
Haar integrability of the averaged skewered diagonal, and not
a one-variable descent compatible with the divisorial cuts.

**Formal scope: Open.** No Lean endpoint for the repaired
global smooth test lift and the resulting geometric kernel was
checked. The source of `Masullo.isFundamentalDomain_ideleFullFundamentalDomain`
in `Proofs/Lemmas/IdeleFullPeriodization.lean` at
`094466e5c23c4bf296d8348619ac32c02d8a63ed` gives a measure-theoretic
fundamental domain for a log-split construction from supplied
norm-one ideal-class representatives. It does not type or
construct φ̃, supply this indentation, or prove the kernel's
diagonal-mass formula. The construction and recovery check given
here are classical, conditional, and scoped to the repaired
formula.

[source]: ../sources/masullo/README.md
[weight]: diagonal-indentation-weight.md
