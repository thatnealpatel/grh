# Multiplying an indentation lift by a quotient function

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 23, claim in item (3), equation (1.3.1.10). Write
Q = G/H and p = π × π. For ρ in C_c(Q × Q) and the kernel u
of item (2), the manuscript asserts Ψ(ρu) = (ρ ∘ p) Ψ(u)
almost everywhere for product Haar measure on G × G. Coverage
stops before item (4).

The [pinned PDF][source] was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction supplied the full item.
Rendered pixel crops confirm the hypothesis, equation label, the
placement of ρ and π × π in the formula, and the almost-everywhere
qualification. Proposition 12.2.2.2(3), printed p. 508, repeats the
identity as (12.2.2.8); its hypothesis and formula were spot-checked
in rendered pixels and the rest read in extraction. The reading of
its proof on p. 511 is provisional, from chapter Markdown.

**Paper-level check.** Masullo's proof is substitution into the
definition Ψ(u) = w · (u ∘ p), with w = u₀^Δ. For chosen actual
representatives, composition preserves pointwise multiplication,
and commutativity of complex multiplication moves ρ ∘ p past w.
This is pointwise wherever the expressions are defined. The
continuous compactly supported ρ is bounded and measurable, so ρu
is again a locally integrable measurable kernel. For the assertion
on product-Haar equivalence classes, use the measurability and
null-set pullback from [item (2)][unfolding]: For a measurable exact
section with compatibly normalized quotient Haar measure, product
quotient null sets pull back to product Haar null sets, by the
countable cover by translates of the product section. The algebra
itself does not need that measure comparison.

**Formal scope: Open.** No Lean declaration implementing this lift
and its multiplier identity was checked. This is an identity for a
quotient multiplier pulled back to both coordinates, so the multiplier
is invariant under independent H-translations. The identity does not
make an arbitrary ambient cutoff a quotient pullback, and compact
support of ρ does not imply compact support of ρ ∘ p. It contains no
averaging operator. To use it in an averaged diagonal identity, one
still has to justify the relevant averages and, if moving a multiplier
through their limit, control the corresponding averaging error at the
points in question. Those are not claims checked in item (3).

[source]: ../sources/masullo/README.md
[unfolding]: skewered-diagonal-unfolding.md
