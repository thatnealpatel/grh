module

public import Props.ArchimedeanGammaLogDerivative
import Lemmas.ComplexGaussianPolar
import Lemmas.EvenRealIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The real local Gaussian zeta integral

The tests in (3.4.3.3)–(4), p. 152, match the scalar factors in
(3.2.1.4), p. 123. In the bilinear pairing (3.3.1.7), p. 130, the odd
Gaussian cancels the sign of the odd character. We give the absolute
convergence and value of the integral used in (3.4.3.12)–(13), p. 153,
including the radial frequency of the real-place restriction. The
source comparison is based on the extracted text, not rendered pages.
-/

open Complex MeasureTheory Set

namespace Masullo

/-- The real standard Gaussian of parity `b`. -/
public noncomputable def realZetaGaussian (b : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ b * exp (-(Real.pi * x ^ 2 : ℝ))

/-- The real bilinear zeta integrand against ordinary Lebesgue measure.
Definitions A.3.1.2(1), p. 556, and A.3.2.2(1), p. 560, give density
`|x|⁻¹` on the units. The totalized density at zero makes the integrand
zero there. The choice of sign at zero does not matter. -/
@[expose] public noncomputable def realGaussianZetaDensity (b : ℕ) (τ : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  realZetaGaussian b x * (if 0 < x then (1 : ℂ) else -1) ^ b *
    ((|x| : ℝ) : ℂ) ^ (s + (τ : ℂ) * I) * (|x|⁻¹ : ℝ)

private theorem realGaussianZetaDensity_eq_abs (b : ℕ) (τ : ℝ) (s : ℂ) (x : ℝ) :
    realGaussianZetaDensity b τ s x =
      ((|x| : ℝ) : ℂ) ^ b * exp (-(Real.pi * |x| ^ 2 : ℝ)) *
        ((|x| : ℝ) : ℂ) ^ (s + (τ : ℂ) * I) * (|x|⁻¹ : ℝ) := by
  have hsign : (x : ℂ) * (if 0 < x then (1 : ℂ) else -1) = ((|x| : ℝ) : ℂ) := by
    by_cases hx : 0 < x
    · simp [hx, abs_of_pos hx]
    · simp [hx, abs_of_nonpos (le_of_not_gt hx)]
  unfold realGaussianZetaDensity realZetaGaussian
  rw [show (x : ℂ) ^ b * exp (-(Real.pi * x ^ 2 : ℝ)) *
      (if 0 < x then (1 : ℂ) else -1) ^ b =
      ((x : ℂ) * (if 0 < x then (1 : ℂ) else -1)) ^ b *
        exp (-(Real.pi * x ^ 2 : ℝ)) by rw [mul_pow]; ring,
    hsign, sq_abs]

/-- For either parity the real local zeta integral converges absolutely
and gives the shifted real Archimedean factor. -/
public theorem realGaussianZetaDensity_integral (b : ℕ) (hb : b = 0 ∨ b = 1) (τ : ℝ)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (realGaussianZetaDensity b τ s) ∧
      (∫ x : ℝ, realGaussianZetaDensity b τ s x) =
        archimedeanGammaFactor Real.pi 2 (b : ℝ) τ s := by
  let w := s + (τ : ℂ) * I
  let a := (s + (b : ℂ) + (τ : ℂ) * I) / 2
  let G (t : ℝ) := (t : ℂ) ^ (a - 1) * exp (-(Real.pi * t : ℝ))
  have ha : 0 < a.re := by
    rw [show a = (s + (b : ℂ) + (τ : ℂ) * I) * ((1 / 2 : ℝ) : ℂ) by
      dsimp [a]; push_cast; ring]
    simp [mul_re]
    rcases hb with rfl | rfl <;> simp <;> linarith
  -- The sign from the Gaussian cancels the sign from the character.
  have he : Function.Even (realGaussianZetaDensity b τ s) := by
    intro x
    rw [realGaussianZetaDensity_eq_abs, realGaussianZetaDensity_eq_abs, abs_neg]
  -- On the positive half-line, twice the density is the square-map pullback.
  have hrad (x : ℝ) (hx : x ∈ Ioi 0) :
      realGaussianZetaDensity b τ s x = (2 : ℂ)⁻¹ * ((2 * x) • G (x ^ 2)) := by
    have hx' : 0 < x := hx
    have hx₀ : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx'.ne'
    have hpow : ((x ^ 2 : ℝ) : ℂ) ^ (a - 1) * (x : ℂ) ^ (2 : ℕ) =
        (x : ℂ) ^ b * (x : ℂ) ^ w := by
      rw [← Real.rpow_two, ← cpow_mul_ofReal_nonneg hx'.le, ← cpow_natCast,
        ← cpow_add _ _ hx₀, ← cpow_natCast, ← cpow_add _ _ hx₀]
      congr 1
      dsimp [a, w]
      ring
    rw [realGaussianZetaDensity_eq_abs, abs_of_pos hx']
    change (x : ℂ) ^ b * exp (-(Real.pi * x ^ 2 : ℝ)) * (x : ℂ) ^ w *
      (x⁻¹ : ℝ) = _
    simp only [ofReal_inv, G, Complex.real_smul, ofReal_mul, ofReal_ofNat]
    rw [show (x : ℂ) ^ b * exp (-((Real.pi : ℂ) * ((x ^ 2 : ℝ) : ℂ))) * (x : ℂ) ^ w =
      ((x : ℂ) ^ b * (x : ℂ) ^ w) * exp (-((Real.pi : ℂ) * ((x ^ 2 : ℝ) : ℂ))) by ring,
      ← hpow]
    field_simp
  obtain ⟨hG, hSubst⟩ := square_radial_substitution
    (integrableOn_scaledGammaDensity Real.pi_pos ha)
  have hf : IntegrableOn (realGaussianZetaDensity b τ s) (Ioi 0) :=
    (integrableOn_congr_fun hrad measurableSet_Ioi).mpr (hG.const_mul ((2 : ℂ)⁻¹))
  obtain ⟨hi, hFold⟩ := even_real_integral he hf
  refine ⟨hi, ?_⟩
  calc
    _ = (∫ t in Ioi (0 : ℝ), G t) := by
      rw [hFold, setIntegral_congr_fun measurableSet_Ioi hrad, integral_const_mul, hSubst,
        ← mul_assoc, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul]
    _ = archimedeanGammaFactor Real.pi 2 (b : ℝ) τ s := by
      rw [show (∫ t in Ioi (0 : ℝ), G t) = (1 / (Real.pi : ℂ)) ^ a * Gamma a by
        simpa only [G, ofReal_neg, ofReal_mul] using
          integral_cpow_mul_exp_neg_mul_Ioi ha Real.pi_pos, archimedeanGammaFactor_real]
      change (1 / (Real.pi : ℂ)) ^ a * Gamma a = Gammaℝ (s + (b : ℂ) + (τ : ℂ) * I)
      rw [Gammaℝ_def, one_div, inv_cpow _ _ (by
        rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne), ← cpow_neg, neg_div]

end Masullo
