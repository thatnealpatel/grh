module

public import Lemmas.RectangleCauchyKernel
import Lemmas.SimplePrincipalParts

/-!
# The finite rectangle in Masullo's explicit formula

Masullo (B.3.2.3), p. 606, invokes the residue theorem for the tested
integrand. The residue of that product need not be the test value times
the residue of the untested function at a higher pole. This proposition
uses simple principal parts of the tested integrand itself. For the
rational completed logarithmic derivative, the required germs are
provided by `Props.RationalExplicitFormulaResidues` (B.4.2.2), p. 614.
The boundary orientation is Figure 3, p. 605: Bottom and right forward,
top and left backward.
-/

open Complex Filter Set
open scoped Topology

namespace Masullo

/-- A counterclockwise rectangular boundary integral equals `2πi` times
 the sum of the coefficients of its interior simple principal parts.
 The assigned values of the integrand at the poles are immaterial. -/
public theorem rectangleIntegral_eq_sum_simpleResidues {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) {Z : Finset ℂ} {g k : ℂ → ℂ}
    (hZ : ∀ z ∈ Z, z ∈ Ioo a b ×ℂ Ioo c d)
    (hreg : ∀ w ∈ (Icc a b ×ℂ Icc c d) \ (Z : Set ℂ), AnalyticAt ℂ g w)
    (hpole : ∀ z ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧
      g =ᶠ[𝓝[≠] z] fun w ↦ k z * (w - z)⁻¹ + H w) :
    rectangleIntegral a b c d g = (2 * Real.pi * I) * ∑ z ∈ Z, k z := by
  obtain ⟨h, hh, heq⟩ := exists_analyticAt_remainder_of_simpleParts hreg hpole
  exact rectangleIntegral_eq_sum_of_eqOn hab.le hcd.le hZ
    (fun w hw ↦ (hh w hw).differentiableAt.differentiableWithinAt) heq

end Masullo
