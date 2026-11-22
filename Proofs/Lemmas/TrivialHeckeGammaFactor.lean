module

public import Theorems.CompletedHeckeEulerProduct

/-! # Infinite factors of the trivial Hecke character

Identify the parameters chosen by the restriction theorems, rather than
replacing the character by a formally untwisted Gamma factor.
-/

open Complex NumberField InfinitePlace.Completion

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] {v : InfinitePlace K}
local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)

public theorem localHeckeGammaFactor_one_real (hv : v.IsReal) :
    localHeckeGammaFactor χ₀ (fun _ ↦ norm_one) v = archimedeanGammaFactor Real.pi 2 0 0 := by
  obtain ⟨b, τ, hb, h, heq⟩ := localHeckeGammaFactor_real χ₀ (fun _ ↦ norm_one) hv
  let e := ringEquivRealOfIsReal hv
  have hc (y : ℝ) (hy : y ≠ 0) : (1 : ℂ) = (if 0 < y then (1 : ℂ) else -1) ^ b *
      exp (((τ * Real.log |y| : ℝ) : ℂ) * I) := by
    have h' := h (Units.mk0 (e.symm y) (by simpa using hy))
    change (1 : ℂ) = (if 0 < e (e.symm y) then (1 : ℂ) else -1) ^ b *
      exp (((τ * Real.log |e (e.symm y)| : ℝ) : ℂ) * I) at h'
    simpa only [RingEquiv.apply_symm_apply] using h'
  have hb0 : b = 0 := by
    by_contra hn
    have hb1 : b = 1 := by omega
    have H := hc (-1) (by norm_num)
    norm_num [hb1] at H
  have ht0 : τ = 0 := by
    by_contra hn
    have H := hc (Real.exp (Real.pi / τ)) (Real.exp_ne_zero _)
    rw [abs_of_pos (Real.exp_pos _), Real.log_exp, mul_div_cancel₀ _ hn] at H
    norm_num [hb0, exp_pi_mul_I] at H
  simpa [hb0, ht0] using heq

public theorem localHeckeGammaFactor_one_complex (hv : v.IsComplex) :
    localHeckeGammaFactor χ₀ (fun _ ↦ norm_one) v = archimedeanGammaFactor (2 * Real.pi) 1 0 0 := by
  obtain ⟨n, τ, h, heq⟩ := localHeckeGammaFactor_complex χ₀ (fun _ ↦ norm_one) hv
  let e := ringEquivComplexOfIsComplex hv
  have hc (z : ℂ) (hz : z ≠ 0) : (1 : ℂ) = (z / (‖z‖ : ℂ)) ^ n *
      exp (((τ * Real.log (‖z‖ ^ 2) : ℝ) : ℂ) * I) := by
    have h' := h (Units.mk0 (e.symm z) (by simpa using hz))
    change (1 : ℂ) = (e (e.symm z) / (‖e (e.symm z)‖ : ℂ)) ^ n *
      exp (((τ * Real.log (‖e (e.symm z)‖ ^ 2) : ℝ) : ℂ) * I) at h'
    simpa only [RingEquiv.apply_symm_apply] using h'
  have hn0 : n = 0 := by
    by_contra hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have H := hc _ (exp_ne_zero (((Real.pi / n : ℝ) : ℂ) * I))
    simp only [norm_exp_ofReal_mul_I, ofReal_one, div_one, one_pow, Real.log_one, mul_zero,
      ofReal_zero, zero_mul, exp_zero, mul_one, ← exp_int_mul] at H
    rw [← mul_assoc, ← ofReal_intCast, ← ofReal_mul, mul_div_cancel₀ _ hn', exp_pi_mul_I] at H
    norm_num at H
  have ht0 : τ = 0 := by
    by_contra hn
    let r := Real.exp (Real.pi / τ / 2)
    have hr : 0 < r := Real.exp_pos _
    have H := hc (r : ℂ) (ofReal_ne_zero.mpr hr.ne')
    have hl : τ * Real.log (r ^ 2) = Real.pi := by
      rw [Real.log_pow, show Real.log r = Real.pi / τ / 2 from Real.log_exp _]
      field_simp
      norm_num
    rw [norm_real, Real.norm_of_nonneg hr.le, hl, exp_pi_mul_I, hn0, zpow_zero, one_mul] at H
    norm_num at H
  simpa [hn0, ht0] using heq

end Masullo
