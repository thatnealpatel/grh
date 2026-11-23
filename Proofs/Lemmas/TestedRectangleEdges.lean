module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Domination on the four edges of the tested logarithmic-derivative rectangle. -/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Masullo

public theorem integrable_tested_logDeriv_vertical {L Φ : ℂ → ℂ} (hΦ : Continuous Φ)
    (hdiff : ∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s)
    {B C σ : ℝ} (hB : 0 ≤ B) (hσ : σ = -1 ∨ σ = 2)
    (htest : ∀ t : ℝ, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 3)
    (hV : ∀ t : ℝ, L ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧
      ‖logDeriv L ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|)) :
    Integrable (fun t : ℝ ↦ Φ ((σ : ℂ) + (t : ℂ) * I) *
      logDeriv L ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hz : Continuous z := by dsimp [z]; fun_prop
  have hlog : Continuous (fun t ↦ logDeriv L (z t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hr : (z t).re = σ := by simp [z]
    have h₀ : z t ≠ 0 := by
      intro h; rw [h, zero_re] at hr; rcases hσ with hσ | hσ <;> linarith
    have h₁ : z t ≠ 1 := by
      intro h; rw [h, one_re] at hr; rcases hσ with hσ | hσ <;> linarith
    have ha : AnalyticAt ℂ L (z t) := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      filter_upwards [eventually_ne_nhds h₀, eventually_ne_nhds h₁] with s hs₀ hs₁
      exact hdiff s hs₀ hs₁
    exact (ha.deriv.div ha (hV t).1).continuousAt.comp hz.continuousAt
  have hs : Integrable (fun t : ℝ ↦ (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by simp)
  refine (hs.const_mul (B * C)).mono' ((hΦ.comp hz).mul hlog).aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.rpow_neg (by positivity),
    ← (show ((2 : ℕ) : ℝ) = 2 by norm_num), Real.rpow_natCast]
  have hpos : 0 < 1 + |t| := by positivity
  calc
    _ ≤ (B / (1 + |t|) ^ 3) * (C * (1 + |t|)) :=
      mul_le_mul (htest t) (hV t).2 (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

public theorem tendsto_tested_logDeriv_horizontal {L Φ : ℂ → ℂ} {B D : ℝ}
    (hB : 0 ≤ B) {w : ℕ → ℝ} (hw : Tendsto (fun n ↦ |w n|) atTop atTop)
    (hΦ : ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ t : ℝ,
      ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 3)
    (hL : ∀ n σ, σ ∈ Icc (-1 : ℝ) 2 →
      ‖logDeriv L ((σ : ℂ) + (w n : ℂ) * I)‖ ≤ D * (1 + |w n|) ^ 2) :
    Tendsto (fun n ↦ ∫ x : ℝ in (-1)..2,
      Φ (x + (w n : ℂ) * I) * logDeriv L (x + (w n : ℂ) * I)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n ↦ (1 + |w n|)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n ↦ by linarith) hw)
  refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using hinv.const_mul (3 * (B * D)))
  have hpos : 0 < 1 + |w n| := by positivity
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -1) (b := 2) (C := B * D / (1 + |w n|)) (f := fun x : ℝ ↦
      Φ (x + (w n : ℂ) * I) * logDeriv L (x + (w n : ℂ) * I)) (by
    intro σ hσ
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hσ
    have hm : σ ∈ Icc (-1 : ℝ) 2 := ⟨hσ.1.le, hσ.2⟩
    rw [norm_mul]
    calc
      _ ≤ (B / (1 + |w n|) ^ 3) * (D * (1 + |w n|) ^ 2) :=
        mul_le_mul (hΦ σ hm _) (hL n σ hm) (norm_nonneg _) (by positivity)
      _ = B * D / (1 + |w n|) := by field_simp)
  convert hbd using 1
  norm_num
  ring

end Masullo
