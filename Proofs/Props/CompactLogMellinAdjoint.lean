module

public import Lemmas.CompactLogMellinAdjoint

/-!
# Pair a short Mellin-filtered test with a positive-log density

This is an original step in the rational test construction for the strip
comparison in Masullo, Theorem 12.5.1.1, pp. 519–520, (12.5.1.3–4).
Masullo moves derivatives by parts against a Mellin exponential in
(B.2.1.31), p. 599. Here the test is filtered, and we need to move the
whole filter against the actual trace density, which may be singular at zero.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- Pair the filtered test with `ρ` by pairing the seed with the average of
`P(-∂)ρ` at positive shifts. No integrability of `ρ` at zero is required.
The inner average is only used on the seed support. -/
public theorem integral_logPolynomialDeriv_logTranslateAverage
    {μ : Measure ℝ} [IsFiniteMeasure μ] {D a b : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0)
    (P : Polynomial ℝ) {φ ρ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (ha : 0 < a)
    (hs : tsupport φ ⊆ Icc a b) (hρ : ContDiffOn ℝ ∞ ρ (Ioi 0)) :
    let f := logPolynomialDeriv P (logTranslateAverage μ φ)
    let K := fun x ↦ ∫ u, logPolynomialAdjoint P ρ (x + u) ∂μ
    Integrable (fun x ↦ ρ x * f x) ∧ Integrable (fun x ↦ K x * φ x) ∧
      (∫ x, ρ x * f x) = ∫ x, K x * φ x := by
  obtain ⟨hsmooth, hsupp⟩ := logTranslateAverage_smooth_supported hμ hφ hs
  -- Integration by parts moves the polynomial, with a minus sign on the derivative.
  obtain ⟨hi, hparts⟩ := integral_logPolynomialDeriv_adjoint P hρ hsmooth ha hsupp
  -- Fubini moves the average, changing a shift by `-u` to one by `+u`.
  obtain ⟨hk, hshift⟩ := integral_logTranslateAverage_adjoint hμ
    (logPolynomialAdjoint_continuousOn P hρ) hφ.continuous ha hs
  exact ⟨hi, hk, hparts.trans hshift⟩

end Masullo
