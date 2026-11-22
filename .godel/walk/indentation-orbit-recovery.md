# Pointwise orbit recovery with a normalized indentation

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 22, claim in equation (1.3.1.2). For the continuous
nonnegative indentation u₀ from the preceding setup on a
second-countable Hausdorff locally compact abelian group G and a
closed subgroup H, Masullo states that, for each continuous
complex-valued u on G/H and every x in G, the integral of
(u₀ · (u ∘ π))(h⁻¹x) over H against the chosen Haar measure μ_H
converges to u(π(x)). This uses (1.3.1.1), the pointwise
normalization of the indentation. Neither H discrete nor u of
compact support is required. The printed page number, equation
label, integrand, and recovery value were checked in rendered
pixel crops of the [pinned PDF][source], SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The prose and paragraph boundary were read in chapter Markdown
and PDF layout extraction.

**Conditional classical check.** Fix x. The equality
π(h⁻¹x) = π(x) holds for all h in H, so the integrand is
u(π(x)) times the real nonnegative function h ↦ u₀(h⁻¹x).
This orbit function is measurable by continuity and has integral
one by (1.3.1.1). The integral of the absolute value of the
product is therefore |u(π(x))|, including when u(π(x)) = 0.
Pulling the same complex scalar out of the integral gives
u(π(x)). This is Masullo's quotient-invariance calculation in
the proof of Lemma 12.2.1.1, printed p. 505, after (12.2.1.3),
with the absolute-convergence step made explicit here. The later
passage was read in chapter Markdown only, so its attribution
and equation locator are provisional. The calculation does not
require a forward input from that lemma.

The check is pointwise in x. It does not construct u₀, prove
integrability of the lift over G, or treat the later kernel or
diagonal claims. To use the conditional result without a supplied
indentation still requires the [existence claim][cutoff].

**Formal scope: Open.** No general Lean endpoint was checked for
integrability of the complex-valued orbit integrand and its
pointwise Haar integral at every x for this quotient and given
normalized u₀. In source at revision
`a39f740d031ebe4afe2c49f6f5d1fb40c6324813`,
`Masullo.monogenicPeriodization_cutoff_section` in
`Proofs/Theorems/MonogenicPeriodizationSection.lean` constructs
a smooth compactly supported real-log cutoff and recovers smooth
log-periodic profiles by `HasSum` over integer powers. It does not
provide the general integral for arbitrary closed H and merely
continuous u. The evidence here is a classical audit of the
conditional assertion, not a general Lean verification.

[source]: ../sources/masullo/README.md
[cutoff]: continuous-indentation.md
