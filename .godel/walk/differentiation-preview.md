# Differentiation in the two-variable preview

**Printed passage.** Masullo, *The Music of the Primes*, printed
p. 22, §1.3.1, preview in the paragraph beginning “Now recall” and
ending “can be found in G.” Masullo invokes a Lebesgue differentiation
analogue for Hausdorff locally compact abelian groups and says it rests
on a Hardy–Littlewood maximal analogue, provided the group has an
analogue of Euclidean closed balls. This is conditional, not an
assertion that an arbitrary choice of shrinking neighborhoods works.
The next paragraph names the sequences and previews their construction;
that paragraph is outside this finding.

The [pinned PDF][source] was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction give the paragraph and its
context; rendered pixel crops were used to check the theorem names
and the closed-ball qualification. The appendix interfaces below are
provisional readings from Markdown and layout extraction, not a full
rendered review of their statements or proofs. The boundary-null
inference on p. 585 was also spot-checked in a rendered crop.

**Inputs needed.** Theorem A.5.4.1(2)–(3), pp. 582–583, supplies
the relevant conclusion: For a second-countable Hausdorff locally
compact abelian group with Haar measure μ and a Borel D′-sequence
(Uₖ), the averages of a locally μ-integrable f over xUₖ, divided by
μ(Uₖ), tend to f(x) for μ-almost every x. Definition A.5.2.1, p. 569,
requires nested sets containing the identity with finite positive Haar
mass, a uniform bound on μ(UₖUₖ⁻¹)/μ(Uₖ), and eventual containment
in every identity neighborhood for D′. Theorem A.5.3.7(1), p. 582,
states a weak (1,1) estimate with constant 2C for the *limsup* of
normalized absolute averages on a D′-sequence with compact first
closure. A sufficiently late tail has compact first closure and does
not change the limsup. The preview does not require part (1) of the
differentiation theorem on uniform continuity of individual averages.
Nor does product-measure differentiation imply almost-everywhere
regularity when points are instead measured along the diagonal.

**Open proof step.** Masullo appeals to the maximal estimate, then
reduces the convergence proof to indicators. Just before part (3) on
p. 585, the proof uses outer regularity to infer that a finite-measure
open set U has null boundary, by taking open supersets U′ with
arbitrarily small μ(U′ − U). This only controls the excess measure;
there is no requirement that U′ contain the boundary. The missing
step is to justify almost-everywhere recovery for general locally
integrable f without that inference. A classical route to check is
compactly supported continuous approximation after localization:
shrinking gives convergence for the approximants, and the weak (1,1)
estimate for the limsup of absolute error averages, together with
Chebyshev's inequality for the pointwise error, should give recovery
for f. This is a proposed repair, not verification of the printed
proof or a Lean result.

The [spectral trace audit][spectral] uses a project argument with a
*supremum* maximal bound and L² approximation for singular vectors;
it does not establish the full local L¹ statement or identify a
limsup estimate with uniform control over all scales. It also checks
that the literal general-field boxes fail to shrink on the idele
class group for ℚ(i). That concerns the following construction
preview, not the conditional differentiation claim reviewed here.

[source]: ../sources/masullo/README.md
[spectral]: ../obligations/trace-spectral.md
