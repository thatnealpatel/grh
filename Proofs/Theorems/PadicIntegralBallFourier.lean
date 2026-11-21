module

public import Theorems.PadicStandardCharacter
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Lemmas.PadicAddHaar

import Mathlib.MeasureTheory.Group.Integral

/-!
# Fourier transforms of integral balls in `ℚ_[p]`

We normalize additive Haar measure as in Definition A.3.1.2(3) and Example
A.3.1.7, pp. 556–558. For the negative-exponent convention of Example A.3.1.5,
the phase of the translated indicator in (A.3.1.5) is the conjugate of the
positive standard character. The support depends on the dilation alone.
-/

open scoped Padic ENNReal
open MeasureTheory Set

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

local notation "B[" q "]" => Set.ofPred (fun x : ℚ_[q] ↦ ‖x‖ ≤ 1)

/-- The Fourier transform of the integral-ball indicator is itself. The
integral uses the conjugate of the positive standard character. -/
public theorem padicIntegralBall_fourier (y : ℚ_[p]) :
    (∫ x in B[p], star (padicStdAddChar p (x * y)) ∂padicAddHaar p) =
      (B[p]).indicator (fun _ ↦ (1 : ℂ)) y := by
  classical
  have hB : MeasurableSet B[p] := (isClosed_le continuous_norm continuous_const).measurableSet
  by_cases hy : y ∈ B[p]
  · -- The character is trivial on all products of integral elements.
    rw [indicator_of_mem hy]
    calc
      _ = ∫ x in B[p], (1 : ℂ) ∂padicAddHaar p := by
        apply setIntegral_congr_fun hB
        intro x hx
        change star (padicStdAddChar p (x * y)) = 1
        rw [(padicStdAddChar_eq_one_iff p _).mpr, star_one]
        calc
          ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
          _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg y)
          _ ≤ 1 := by rwa [one_mul]
      _ = 1 := by simp [Measure.real, padicAddHaar_integralBall]
  · -- Translation by the integral element `1` preserves the ball and changes the phase.
    let f : ℚ_[p] → ℂ := (B[p]).indicator (fun x ↦ star (padicStdAddChar p (x * y)))
    have h₁ : padicStdAddChar p 1 = 1 := (padicStdAddChar_eq_one_iff p _).mpr (by simp)
    have htranslate (x : ℚ_[p]) : f (1 + x) = star (padicStdAddChar p y) * f x := by
      have hmem : 1 + x ∈ B[p] ↔ x ∈ B[p] := by
        change ‖1 + x‖ ≤ 1 ↔ ‖x‖ ≤ 1
        rw [← padicStdAddChar_eq_one_iff p (1 + x), ← padicStdAddChar_eq_one_iff p x,
          AddChar.map_add_eq_mul, h₁, one_mul]
      by_cases hx : x ∈ B[p]
      · simp only [f, indicator_of_mem hx, indicator_of_mem (hmem.mpr hx), add_mul, one_mul,
          AddChar.map_add_eq_mul, star_mul']
      · simp [f, indicator_of_notMem hx, indicator_of_notMem (mt hmem.mp hx)]
    have hinvariance :
        star (padicStdAddChar p y) * (∫ x, f x ∂padicAddHaar p) =
          ∫ x, f x ∂padicAddHaar p := by
      rw [← integral_const_mul]
      simpa only [htranslate] using
        (integral_add_left_eq_self (μ := padicAddHaar p) f 1)
    have hphase : star (padicStdAddChar p y) ≠ 1 := by
      intro h
      apply hy
      apply (padicStdAddChar_eq_one_iff p _).mp
      simpa using congrArg star h
    have hzero : (∫ x, f x ∂padicAddHaar p) = 0 := by
      by_contra h
      exact hphase ((mul_eq_right₀ h).mp hinvariance)
    rw [indicator_of_notMem hy]
    simpa only [f, integral_indicator hB] using hzero

/-- The negative-sign Fourier transform of the indicator of `a + p^n ℤ_[p]`.
The frequency indicator at `p^n * y` means that `y ∈ p^(-n) ℤ_[p]`. -/
public theorem padicTranslatedBall_fourier (n : ℕ) (a y : ℚ_[p]) :
    (∫ x in {x : ℚ_[p] | ‖((p : ℚ_[p]) ^ n)⁻¹ * (x - a)‖ ≤ 1},
      star (padicStdAddChar p (x * y)) ∂padicAddHaar p) =
    ((p : ℂ) ^ n)⁻¹ * star (padicStdAddChar p (a * y)) *
      (B[p]).indicator (fun _ ↦ (1 : ℂ)) ((p : ℚ_[p]) ^ n * y) := by
  let d := (p : ℚ_[p]) ^ n
  have hd : d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  let dilate := ContinuousAddEquiv.mulLeft (Units.mk0 d⁻¹ (inv_ne_zero hd))
  let e := (MeasurableEquiv.subRight a).trans dilate.toHomeomorph.toMeasurableEquiv
  have he (x : ℚ_[p]) : e x = d⁻¹ * (x - a) := rfl
  have hinv (z : ℚ_[p]) : e.symm z = a + d * z := by
    apply e.injective
    rw [e.apply_symm_apply, he, add_comm a, add_sub_cancel_right,
      ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  have hmap : Measure.map e (padicAddHaar p) = ((p : ℝ≥0∞) ^ n)⁻¹ • padicAddHaar p := by
    change Measure.map ((fun x : ℚ_[p] ↦ d⁻¹ * x) ∘ (fun x ↦ x - a)) (padicAddHaar p) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), map_sub_right_eq_self,
      padicAddHaar_map_inv_pow]
  change (∫ x in e ⁻¹' B[p], star (padicStdAddChar p (x * y)) ∂padicAddHaar p) = _
  calc
    _ = ∫ z in B[p], star (padicStdAddChar p (e.symm z * y)) ∂Measure.map e (padicAddHaar p) := by
      rw [setIntegral_map_equiv]
      simp only [e.symm_apply_apply]
    _ = _ := by
      have hphase (z : ℚ_[p]) : star (padicStdAddChar p (e.symm z * y)) =
          star (padicStdAddChar p (a * y)) * star (padicStdAddChar p (z * (d * y))) := by
        rw [hinv, add_mul, show d * z * y = z * (d * y) by ring,
          AddChar.map_add_eq_mul, star_mul']
      simp only [hmap, Measure.restrict_smul, integral_smul_measure, hphase, integral_const_mul,
        padicIntegralBall_fourier, Complex.real_smul, ENNReal.toReal_inv, ENNReal.toReal_pow,
        ENNReal.toReal_natCast, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast]
      ring

end Masullo
