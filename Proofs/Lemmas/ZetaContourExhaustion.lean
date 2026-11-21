module

public import Props.ZetaContourEdges
public import Lemmas.RationalCompletedZetaZeros
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Lemmas.ZetaZeroSummability
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Convergence estimates for the rational contour in (B.4.2.2), p. 614. -/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Masullo

/-- Choose independently at the two ends to avoid all zero ordinates. -/
public theorem exists_completedZeta_contour_exhaustion :
    ∃ C > (0 : ℝ), ∃ u v : ℕ → ℝ,
      Tendsto u atTop atBot ∧ Tendsto v atTop atTop ∧
      (∀ n, u n < 0 ∧ 0 < v n) ∧
      (∀ n (ρ : criticalStripZetaZeros), (ρ : ℂ).im ≠ u n ∧ (ρ : ℂ).im ≠ v n) ∧
      ∀ n σ, σ ∈ Icc (-1 : ℝ) 2 →
        ‖logDeriv completedRiemannZeta ((σ : ℂ) + (u n : ℂ) * I)‖ ≤ C * (1 + |u n|) ^ 3 ∧
        ‖logDeriv completedRiemannZeta ((σ : ℂ) + (v n : ℂ) * I)‖ ≤ C * (1 + |v n|) ^ 3 := by
  obtain ⟨c, C, hc, hC, h⟩ := exists_height_completedZeta_logDeriv_le
  have hp (n : ℕ) := h ((n : ℤ) + 2) (by push_cast; rw [abs_of_nonneg (by positivity)]; linarith)
  have hm (n : ℕ) := h (-((n : ℤ) + 2)) (by
    push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; linarith)
  choose v hv₁ _hv₂ hvsep hvbd using hp
  choose u _hu₁ hu₂ husep hubd using hm
  have hv (n : ℕ) : (n : ℝ) + 2 < v n := by exact_mod_cast hv₁ n
  have hu (n : ℕ) : u n < -(n : ℝ) - 1 := by
    calc
      u n < ((-((n : ℤ) + 2) : ℤ) : ℝ) + 1 := hu₂ n
      _ = _ := by push_cast; ring
  have hnv : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨C, hC, u, v, ?_, tendsto_atTop_mono (fun n ↦ by linarith [hv n]) hnv,
    fun n ↦ ⟨by linarith [hu n], by linarith [hv n]⟩, ?_, fun n σ hσ ↦ ⟨hubd n σ hσ, hvbd n σ hσ⟩⟩
  · have hh : Tendsto (fun n ↦ -u n) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ by linarith [hu n]) hnv
    simpa only [Function.comp_def, neg_neg] using tendsto_neg_atTop_atBot.comp hh
  · intro n ρ
    have hne (m : ℤ) {t : ℝ}
        (hs : c / (1 + |(m : ℝ)|) ^ 2 ≤ |t - (ρ : ℂ).im|) : (ρ : ℂ).im ≠ t := by
      intro he
      rw [he, sub_self, abs_zero] at hs
      exact (not_le_of_gt (by positivity)) hs
    exact ⟨hne _ (husep n ρ), hne _ (hvsep n ρ)⟩

/-- Fourth-power test decay beats the cubic bound on a horizontal edge. -/
public theorem tendsto_completedZeta_horizontalIntegral {Φ : ℂ → ℂ} {B C : ℝ}
    (hB : 0 ≤ B) {w : ℕ → ℝ} (hw : Tendsto (fun n ↦ |w n|) atTop atTop)
    (hΦ : ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ t : ℝ,
      ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4)
    (hL : ∀ n σ, σ ∈ Icc (-1 : ℝ) 2 →
      ‖logDeriv completedRiemannZeta ((σ : ℂ) + (w n : ℂ) * I)‖ ≤ C * (1 + |w n|) ^ 3) :
    Tendsto (fun n ↦ ∫ x : ℝ in (-1)..2,
      Φ (x + (w n : ℂ) * I) * logDeriv completedRiemannZeta (x + (w n : ℂ) * I)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n ↦ (1 + |w n|)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n ↦ by linarith) hw)
  refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using hinv.const_mul (3 * (B * C)))
  have hpos : 0 < 1 + |w n| := by positivity
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -1) (b := 2) (C := B * C / (1 + |w n|)) (f := fun x : ℝ ↦
      Φ (x + (w n : ℂ) * I) * logDeriv completedRiemannZeta (x + (w n : ℂ) * I)) (by
    intro σ hσ
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] at hσ
    have hm : σ ∈ Icc (-1 : ℝ) 2 := ⟨hσ.1.le, hσ.2⟩
    rw [norm_mul]
    calc
      _ ≤ (B / (1 + |w n|) ^ 4) * (C * (1 + |w n|) ^ 3) :=
        mul_le_mul (hΦ σ hm _) (hL n σ hm) (norm_nonneg _) (by positivity)
      _ = B * C / (1 + |w n|) := by field_simp)
  convert hbd using 1
  norm_num
  ring

/-- On a vertical edge a linear bound for the completed derivative gives
an integrable inverse-cubic envelope after multiplication by the test. -/
public theorem integrable_completedZeta_vertical {Φ : ℂ → ℂ} (hΦ : Continuous Φ)
    {B C σ : ℝ} (hB : 0 ≤ B) (hσ : σ = 2 ∨ σ = -1)
    (htest : ∀ t : ℝ, ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4)
    (hL : ∀ t : ℝ,
      ‖logDeriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|)) :
    Integrable (fun t : ℝ ↦ Φ ((σ : ℂ) + (t : ℂ) * I) *
      logDeriv completedRiemannZeta ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hc : Continuous (fun t : ℝ ↦ logDeriv completedRiemannZeta (z t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hr : (z t).re = σ := by simp [z]
    have h0 : z t ≠ 0 := by
      intro h; rw [h, zero_re] at hr; rcases hσ with hσ | hσ <;> linarith
    have h1 : z t ≠ 1 := by
      intro h; rw [h, one_re] at hr; rcases hσ with hσ | hσ <;> linarith
    have hn : completedRiemannZeta (z t) ≠ 0 := by
      intro h
      obtain ⟨_, hp, hlt⟩ := mem_criticalStripZetaZeros.mp
        ((completedZeta_eq_zero_iff_mem_criticalStripZetaZeros h0 h1).mp h)
      rcases hσ with hσ | hσ <;> linarith
    have ha := analyticAt_completedZeta h0 h1
    exact (ha.deriv.div ha hn).continuousAt.comp (by dsimp [z]; fun_prop)
  have hs : Integrable (fun t : ℝ ↦ (1 + ‖t‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by simp)
  have hz : Continuous z := by dsimp [z]; fun_prop
  refine (hs.const_mul (B * C)).mono' ((hΦ.comp hz).mul hc).aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.rpow_neg (by positivity),
    ← (show ((3 : ℕ) : ℝ) = 3 by norm_num), Real.rpow_natCast]
  have hpos : 0 < 1 + |t| := by positivity
  calc
    _ ≤ (B / (1 + |t|) ^ 4) * (C * (1 + |t|)) :=
      mul_le_mul (htest t) (hL t) (norm_nonneg _) (by positivity)
    _ = _ := by field_simp

/-- The fourth-power decay on the strip also gives absolute summability
of the full divisor via the checked quadratic weight. -/
public theorem summable_norm_completedZeta_contour_terms {Φ : ℂ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (htest : ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ t : ℝ,
      ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B / (1 + |t|) ^ 4) :
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ)‖) := by
  refine (summable_zetaZeroOrder_div_one_add_norm_sq.mul_left (2 * B)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun ρ ↦ ?_
  have hin : (ρ : ℂ).re ∈ Icc (-1 : ℝ) 2 := by
    obtain ⟨_, hp, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
    exact ⟨by linarith, by linarith⟩
  have htestρ : ‖Φ (ρ : ℂ)‖ ≤ B / (1 + |(ρ : ℂ).im|) ^ 4 := by
    simpa only [re_add_im] using htest _ hin (ρ : ℂ).im
  have him : (shiftedZetaZero ρ).im = (ρ : ℂ).im := by simp [shiftedZetaZero]
  have hnorm : ‖shiftedZetaZero ρ‖ ≤ 1 + |(ρ : ℂ).im| := by
    have h := norm_le_abs_re_add_abs_im (shiftedZetaZero ρ)
    rw [him] at h
    linarith [abs_re_shiftedZetaZero_lt ρ]
  let A := 1 + |(ρ : ℂ).im|
  have hA : 1 ≤ A := by dsimp [A]; simp
  have hdenom : 1 + ‖shiftedZetaZero ρ‖ ^ 2 ≤ 2 * A ^ 4 := by
    have h1 : 1 ≤ A ^ 4 := one_le_pow₀ hA
    have h2 : ‖shiftedZetaZero ρ‖ ^ 2 ≤ A ^ 4 :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans (pow_le_pow_right₀ hA (by decide))
    linarith
  have hscalar : B / A ^ 4 ≤ (2 * B) / (1 + ‖shiftedZetaZero ρ‖ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hdenom hB]
  rw [norm_mul, norm_natCast]
  calc
    _ ≤ (zetaZeroOrder ρ : ℝ) * ((2 * B) / (1 + ‖shiftedZetaZero ρ‖ ^ 2)) := by
      gcongr
      exact htestρ.trans hscalar
    _ = _ := by ring

/-- Finite sums on the height windows converge to the unconditional sum.
The intervals need not be symmetric or even nested. -/
public theorem tendsto_sum_zetaZeros_boundedIm {α : Type*} {l : Filter α} {u v : α → ℝ}
    (hu : Tendsto u l atBot) (hv : Tendsto v l atTop)
    {f : criticalStripZetaZeros → ℂ} (hf : Summable f) :
    Tendsto (fun n ↦ ∑ ρ ∈ (criticalStripZetaZeros_boundedIm_finite (u n) (v n)).toFinset, f ρ)
      l (𝓝 (∑' ρ, f ρ)) := by
  classical
  let F (n : α) := (criticalStripZetaZeros_boundedIm_finite (u n) (v n)).toFinset
  have hF : Tendsto F l atTop := by
    refine tendsto_atTop.2 fun s ↦ (eventually_all_finset s).2 fun ρ _ ↦ ?_
    filter_upwards [hu.eventually (eventually_lt_atBot (ρ : ℂ).im),
      hv.eventually (eventually_gt_atTop (ρ : ℂ).im)] with n hlu huv
    exact (Set.Finite.mem_toFinset _).mpr ⟨hlu, huv⟩
  exact (show Tendsto (fun s : Finset criticalStripZetaZeros ↦ ∑ ρ ∈ s, f ρ)
    atTop (𝓝 (∑' ρ, f ρ)) from hf.hasSum).comp hF

end Masullo
