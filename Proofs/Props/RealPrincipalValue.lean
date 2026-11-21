module

public import Lemmas.RealLogFourier

/-! # The real additive log distribution on zero-value tests

Masullo (B.4.4.1)–(B.4.4.2), pp. 619–620, defines the real local term by
pairing the negative logarithm with the standard additive Fourier transform,
then translating the multiplicative identity to zero. Off that identity,
Connes, Appendix II (34)–(36), uses normalized multiplicative Haar. The
extracted cutoff in (B.4.3.13) instead displays full real multiplicative Haar.
The computation below fixes the off-identity coefficient directly from the
additive definition. The zero-value case needs no gap in the support and
is the remainder after subtraction of a test with value one at the identity.
It does not compute the scalar contribution of that subtracted test.
-/

open MeasureTheory Set
open scoped ContDiff FourierTransform

namespace Masullo

/-- The zero-value remainder in Connes, Appendix II (34), with the
standard additive `2π` transform and Lebesgue measure. No vanishing on
a neighborhood is needed when all the indicated pairings are absolute. -/
public theorem real_log_fourier_of_zero {u : ℝ → ℂ} (hu : Continuous u)
    (hzero : u 0 = 0) (hi : Integrable u) (huf : Integrable (𝓕 u))
    (hlog : Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 u ξ))
    (hright : Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ))) :
    -(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 u ξ) = (1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ) := by
  have hv : Continuous (𝓕 u) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  -- Represent the logarithm by a subtracted Cauchy kernel with absolute Fubini.
  calc
    _ = ∫ a in Ioi (0 : ℝ), ∫ ξ,
          ((RealLogFourier.cauchy a ξ - RealLogFourier.cauchy a 1 : ℝ) : ℂ) * 𝓕 u ξ :=
        RealLogFourier.log_pairing_eq_cauchy hv hlog
    -- Fourier inversion at zero cancels the constant in each scale slice.
    _ = ∫ a in Ioi (0 : ℝ), (Real.pi : ℂ) * ∫ z, RealLogFourier.laplaceProfile a z * u z :=
        setIntegral_congr_fun measurableSet_Ioi fun a ha ↦
          RealLogFourier.cauchy_sub_pairing_eq_laplace hu hi huf hzero ha
    -- In space, integrating the Laplace kernel in scale produces the half factor.
    _ = _ := RealLogFourier.laplace_integral_eq_half hu hright

/-- With the standard additive `2π` Fourier convention and Lebesgue measure,
the negative logarithm has off-zero kernel `1 / (2 |z|)`. Here `u` is a
smooth compactly supported additive test that vanishes near zero. Both
pairings are absolutely integrable. -/
public theorem real_log_fourier_off_zero {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hgap : ∃ ε > 0, ∀ z, |z| < ε → u z = 0) :
    Integrable (fun ξ ↦ (Real.log |ξ| : ℂ) * 𝓕 u ξ) ∧
      Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ)) ∧
      -(∫ ξ, (Real.log |ξ| : ℂ) * 𝓕 u ξ) = (1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ) := by
  obtain ⟨ε, hε, hgap⟩ := hgap
  let v := hc.toSchwartzMap hu
  have hzero : u 0 = 0 := hgap 0 (by simpa using hε)
  have hright := RealLogFourier.integrable_div_abs hu.continuous hc hε hgap
  exact ⟨RealLogFourier.log_fourier_integrable v, hright,
    real_log_fourier_of_zero hu.continuous hzero v.integrable
      ((𝓕 v).integrable) (RealLogFourier.log_fourier_integrable v) hright⟩

end Masullo
