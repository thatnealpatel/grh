# Diagonal averaging of a continuous indentation

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 23, claim beginning “Let now” through item (1), equation
(1.3.1.3). In the standing setting of a second-countable Hausdorff
locally compact abelian group G and a closed discrete subgroup H
with counting measure, take a continuous H-indentation u₀. Masullo
forms the product of u₀ with itself and asserts that its average over
simultaneous translation, the integral of u₀(h⁻¹x)u₀(h⁻¹y) over H,
converges at every pair (x,y). The resulting function u₀^Δ is
continuous, real, nonnegative, and invariant under simultaneous
left translation by H. This item is about the weight alone, not
about smoothening a kernel or integrating its diagonal.

The [pinned PDF][source] was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The page number, opening premise, equation label, common translating
variable in both factors, and pointwise convergence were checked in
rendered pixel crops. The full item was read in chapter Markdown
and PDF layout extraction. Coverage stops before item (2).

**Classical check with a supplied indentation.** Take a compact
neighborhood L of a first coordinate x and put
C = supp(u₀) ∩ π⁻¹(π(L)), where π is the quotient map. The support
condition for the indentation makes C compact. For x′ in L, a
nonzero summand at (x′,y′) requires h⁻¹x′ in C and hence h in
H ∩ LC⁻¹. This is a finite set because H is closed and discrete.
It is independent of both x′ in L and y′ in G. Thus near each pair
the weight is a finite sum of continuous nonnegative real functions.
Left translation of the counting index shows diagonal invariance.
This argument uses the support condition, not orbit normalization,
a fundamental domain, or a differentiation theorem. It does not
construct the supplied indentation.

This is the reviewer's local finite-sum version of Masullo's
compact-support argument in Proposition 12.2.2.2(1), statement on
p. 508, proof on p. 509. The later reading is provisional from
chapter Markdown. In that proof the inclusion (12.2.2.11) gives
relative compactness of the intersection in (12.2.2.10); to infer
compactness by this route, also note that the diagonal saturation
of a compact set is closed. It is the inverse image of a compact
set under the quotient by the closed diagonal copy of H in G × G,
whose quotient is Hausdorff.

**Formal scope: Open.** No general Lean endpoint was checked for
local finiteness of the translated products and continuity and
diagonal invariance of their sum for the printed hypotheses. The
accepted source of `Masullo.indentation_pair_weight_hasSum_zero`
(`Proofs/Theorems/IndentationShellSupport.lean`, revision
`f44dfe887421a288b8b624fed59f335d9310aa93`) instead gives a zero
sum for points on opposite sides of a subgroup when the input
function vanishes off that subgroup. It does not verify this
passage's general convergence and continuity claim.

[source]: ../sources/masullo/README.md
