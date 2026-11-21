module

public import Lemmas.RealLogFourier

/-! # The real additive log distribution off the identity

Masullo (B.4.4.1)–(B.4.4.2), pp. 619–620, defines the real local term by
pairing the negative logarithm with the standard additive Fourier transform,
then translating the multiplicative identity to zero. Off that identity,
Connes, Appendix II (34)–(36), uses normalized multiplicative Haar. The
extracted cutoff in (B.4.3.13) instead displays full real multiplicative Haar.
The computation below fixes the off-identity coefficient directly from the
additive definition; it does not compute the subtraction at the identity.
-/

open MeasureTheory Set
open scoped ContDiff FourierTransform

namespace Masullo

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
  have hzero : v 0 = 0 := hgap 0 (by simpa using hε)
  have hright := RealLogFourier.integrable_div_abs hu.continuous hc hε hgap
  refine ⟨RealLogFourier.log_fourier_integrable v, hright, ?_⟩
  -- Represent the logarithm by a subtracted Cauchy kernel with absolute Fubini.
  calc
    _ = ∫ a in Ioi (0 : ℝ), ∫ ξ,
          ((RealLogFourier.cauchy a ξ - RealLogFourier.cauchy a 1 : ℝ) : ℂ) * 𝓕 u ξ :=
        RealLogFourier.log_pairing_eq_cauchy (𝓕 v)
    -- Fourier inversion at zero cancels the constant in each scale slice.
    _ = ∫ a in Ioi (0 : ℝ), (Real.pi : ℂ) * ∫ z, RealLogFourier.laplaceProfile a z * u z :=
        setIntegral_congr_fun measurableSet_Ioi fun a ha ↦
          RealLogFourier.cauchy_sub_pairing_eq_laplace v hzero ha
    -- In space, integrating the Laplace kernel in scale produces the half factor.
    _ = _ := RealLogFourier.laplace_integral_eq_half hu.continuous hright

end Masullo
