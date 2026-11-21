module

public import Props.CompactLogMellin
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring

/-! Joint domination for the subtracted real Gamma kernel on `Re s = 2`. -/

open Complex MeasureTheory Set
open scoped ContDiff

namespace Masullo

private theorem norm_gammaReal_rightLine_kernel_le (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖(exp (-2 * (x : ℂ)) - exp (-(2 + (t : ℂ) * I) * (x : ℂ))) /
      (1 - exp (-2 * (x : ℂ)))‖ ≤ |t| * (Real.exp (-x) / 2) := by
  have hphase : -(2 + (t : ℂ) * I) * (x : ℂ) = -2 * (x : ℂ) + I * ((-t * x : ℝ) : ℂ) := by
    push_cast
    ring
  have hexp : exp (-2 * (x : ℂ)) = (Real.exp (-2 * x) : ℂ) := by push_cast; rfl
  have hd : 0 < 1 - Real.exp (-2 * x) := sub_pos.mpr <|
    Real.exp_lt_one_iff.mpr (by linarith)
  have hnorm : ‖(1 : ℂ) - exp (-2 * (x : ℂ))‖ = 1 - Real.exp (-2 * x) := by
    rw [hexp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hchord : ‖(1 : ℂ) - exp (I * ((-t * x : ℝ) : ℂ))‖ ≤ |t| * x := by
    rw [norm_sub_rev]
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos hx] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -t * x))
  have hden : 1 - Real.exp (-2 * x) = Real.exp (-x) * (2 * Real.sinh x) := by
    rw [Real.sinh_eq, show (2 : ℝ) * ((Real.exp x - Real.exp (-x)) / 2) =
      Real.exp x - Real.exp (-x) by ring, mul_sub, ← Real.exp_add, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, show -x + -x = -2 * x by ring]
  rw [hphase, Complex.exp_add, ← mul_one_sub, norm_div, norm_mul, hnorm, hexp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply (div_le_iff₀ hd).2
  calc
    Real.exp (-2 * x) * ‖(1 : ℂ) - exp (I * ((-t * x : ℝ) : ℂ))‖ ≤
        Real.exp (-2 * x) * (|t| * x) := mul_le_mul_of_nonneg_left hchord (Real.exp_pos _).le
    _ ≤ Real.exp (-2 * x) * (|t| * Real.sinh x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr hx.le)
        (abs_nonneg t)) (Real.exp_pos _).le
    _ = |t| * (Real.exp (-x) / 2) * (1 - Real.exp (-2 * x)) := by
      rw [hden, show -2 * x = -x + -x by ring, Real.exp_add]
      ring

/-- A single product majorant works on the entire positive half-line.
The chord bound and `x ≤ sinh x` keep the cancellation at zero. -/
public theorem integrable_gammaReal_rightLine_product {W : ℝ → ℂ} (hW : Measurable W)
    (hWt : Integrable (fun t ↦ ‖W t‖ * (1 + |t|))) :
    let K := fun (t x : ℝ) ↦ (exp (-2 * (x : ℂ)) - exp (-(2 + (t : ℂ) * I) * (x : ℂ))) /
      (1 - exp (-2 * (x : ℂ)))
    Integrable (fun p : ℝ × ℝ ↦ W p.1 * K p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  dsimp only
  refine (hWt.mul_prod ((integrableOn_exp_neg_Ioi 0).div_const 2)).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  have hx : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume.restrict (Ioi 0))), p.2 ∈ Ioi 0 :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_snd measurableSet_Ioi)).mpr <|
      Filter.Eventually.of_forall fun _ ↦ ae_restrict_mem measurableSet_Ioi
  filter_upwards [hx] with p hp
  rw [norm_mul]
  calc
    _ ≤ ‖W p.1‖ * (|p.1| * (Real.exp (-p.2) / 2)) :=
      mul_le_mul_of_nonneg_left (norm_gammaReal_rightLine_kernel_le p.1 hp) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr
      linarith

/-- The reflected Mellin sum has an integrable first absolute moment as
well as an integrable zeroth moment. -/
public theorem compactLogMellin_reflected_integrable_moments {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let s := fun t : ℝ ↦ (2 : ℂ) + (t : ℂ) * I
    let W := fun t ↦ compactLogMellin g (s t) + compactLogMellin g (1 - s t)
    Continuous W ∧ Integrable W ∧ Integrable (fun t ↦ ‖W t‖ * (1 + |t|)) := by
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  let Φ := compactLogMellin g
  let W (t : ℝ) := Φ (s t) + Φ (1 - s t)
  have hΦ : Continuous Φ := continuous_iff_continuousAt.mpr fun _ ↦
    (analyticAt_compactLogMellin hg.continuous hc _).continuousAt
  have hW : Continuous W :=
    (hΦ.comp (by dsimp [s]; fun_prop)).add (hΦ.comp (by dsimp [s]; fun_prop))
  obtain ⟨B, hB, hbound⟩ := compactLogMellin_vertical_decay hg hc 2 3
  have hdecay (t : ℝ) : ‖W t‖ ≤ (2 * B) / (1 + |t|) ^ 3 := by
    have hr : ‖Φ (s t)‖ ≤ B / (1 + |t|) ^ 3 := by
      simpa only [Complex.ofReal_ofNat] using hbound 2 t (by norm_num)
    have hl : ‖Φ (1 - s t)‖ ≤ B / (1 + |t|) ^ 3 := by
      rw [show 1 - s t = -1 + ((-t : ℝ) : ℂ) * I by dsimp [s]; push_cast; ring, ← abs_neg t]
      simpa only [Complex.ofReal_neg, Complex.ofReal_one] using hbound (-1) (-t) (by norm_num)
    exact (norm_add_le _ _).trans (by rw [two_mul, add_div]; exact add_le_add hr hl)
  have hi : Integrable (fun t : ℝ ↦ (1 + ‖t‖) ^ (-(2 : ℝ))) := integrable_one_add_norm (by simp)
  have hmoment : Integrable (fun t ↦ ‖W t‖ * (1 + |t|)) := by
    refine (hi.const_mul (2 * B)).mono' ((hW.norm.mul (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs (r := ‖W t‖ * (1 + |t|)), abs_of_nonneg (by positivity),
      Real.norm_eq_abs (r := t), Real.rpow_neg (by positivity),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc
      _ ≤ ((2 * B) / (1 + |t|) ^ 3) * (1 + |t|) :=
        mul_le_mul_of_nonneg_right (hdecay t) (by positivity)
      _ = _ := by field_simp; ring
  exact ⟨hW, hmoment.mono' hW.aestronglyMeasurable (Filter.Eventually.of_forall fun t ↦
    le_mul_of_one_le_right (norm_nonneg _) (by simp)), hmoment⟩

/-- At fixed log position, the right-line exponential has constant modulus
in the ordinate. This applies before taking the combined position integral. -/
public theorem integrable_gammaReal_rightLine_exp_sample {W : ℝ → ℂ} (hW : Continuous W)
    (hi : Integrable W) (x : ℝ) :
    Integrable (fun t : ℝ ↦ W t * exp (-(2 + (t : ℂ) * I) * (x : ℂ))) := by
  refine (hi.norm.mul_const (Real.exp (-2 * x))).mono' ((hW.mul (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [norm_mul, Complex.norm_exp]
  simp

end Masullo
