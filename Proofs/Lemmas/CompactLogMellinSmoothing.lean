module

public import Lemmas.CompactLogMellin
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral

/-! # Smoothing a compactly carried measure in the log coordinate -/

open Filter Function MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- The rightward translation average of a real log profile. -/
@[expose] public noncomputable def logTranslateAverage (μ : Measure ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, φ (x - t) ∂μ

private theorem eq_zero_of_notMem_Icc {φ : ℝ → ℝ} {a b x : ℝ}
    (hφ : tsupport φ ⊆ Icc a b) (hx : x ∉ Icc a b) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hm ↦ hx (hφ hm))

/-- The translation average has exact support control and preserves smoothness.
This is the smoothing step in the filtered short-test construction. -/
public theorem logTranslateAverage_smooth_supported {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D a b : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ Icc a b) :
    ContDiff ℝ ∞ (logTranslateAverage μ φ) ∧ tsupport (logTranslateAverage μ φ) ⊆ Icc a (b + D) := by
  have hD : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) D := ae_iff.mpr hμ
  have hr := Measure.restrict_eq_self_of_ae_mem hD
  constructor
  · apply contDiff_infty.mpr
    intro n
    have hp : ContDiff ℝ (n : ℕ∞) (uncurry (fun x t : ℝ ↦ φ (x - t))) :=
      ((contDiff_infty.mp hφ n).of_le (by simp)).comp (contDiff_fst.sub contDiff_snd)
    change ContDiff ℝ (n : ℕ∞) (fun x ↦ ∫ t, φ (x - t) ∂μ)
    simpa only [hr] using
      hp.parametric_integral isCompact_Icc Subset.rfl (measure_ne_top μ (Icc 0 D))
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    apply hx
    apply integral_eq_zero_of_ae
    filter_upwards [hD] with t ht
    apply eq_zero_of_notMem_Icc hs
    intro ht'
    exact hn ⟨by linarith [ht.1, ht'.1], by linarith [ht.2, ht'.2]⟩

/-- A compactly carried translation measure multiplies the log-Mellin transform of the test.
The positive sign in the exponential is the one used in `compactLogMellin`. -/
public theorem compactLogMellin_logTranslateAverage {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D a b : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hs : tsupport φ ⊆ Icc a b) (z : ℂ) :
    compactLogMellin (fun x ↦ (logTranslateAverage μ φ x : ℂ)) z =
      compactLogMellin (fun x ↦ (φ x : ℂ)) z * ∫ t, Complex.exp (z * (t : ℂ)) ∂μ := by
  have hD : ∀ᵐ t ∂μ, t ∈ Icc (0 : ℝ) D := ae_iff.mpr hμ
  let F (x t : ℝ) : ℂ := (φ (x - t) : ℂ) * Complex.exp (z * (x : ℂ))
  let K := Icc a (b + D) ×ˢ Icc (0 : ℝ) D
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hF : Continuous (uncurry F) := by
    dsimp [uncurry, F]
    exact (Complex.continuous_ofReal.comp (hφ.comp (continuous_fst.sub continuous_snd))).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)))
  have hi : Integrable (uncurry F) (volume.prod μ) := by
    refine ((integrable_indicator_iff hK.measurableSet).mpr
      (hF.continuousOn.integrableOn_compact hK)).congr ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hD] with p hp
    rw [indicator_apply]
    split_ifs with hmem
    · rfl
    · have hz : φ (p.1 - p.2) = 0 := eq_zero_of_notMem_Icc hs (fun h ↦
        hmem ⟨⟨by linarith [hp.1, h.1], by linarith [hp.2, h.2]⟩, hp⟩)
      simp [F, uncurry, hz]
  have hc : HasCompactSupport φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hφt (x : ℝ) : Integrable (fun t ↦ φ (x - t)) μ := by
    obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
    refine (integrable_const C).mono' (hφ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ?_
    exact Eventually.of_forall fun t ↦ hC (x - t)
  have hin (x : ℝ) : ∫ t, F x t ∂μ = (logTranslateAverage μ φ x : ℂ) * Complex.exp (z * (x : ℂ)) := by
    rw [show (fun t ↦ F x t) = fun t ↦ (φ (x - t) : ℂ) * Complex.exp (z * (x : ℂ)) from rfl,
      integral_mul_const]
    congr 1
    exact Complex.ofRealCLM.integral_comp_comm (hφt x)
  have htrans (t : ℝ) : ∫ x, F x t =
      compactLogMellin (fun x ↦ (φ x : ℂ)) z * Complex.exp (z * (t : ℂ)) := by
    calc
      (∫ x, F x t) = ∫ x, F (x + t) t := (integral_add_right_eq_self _ _).symm
      _ = (∫ x : ℝ, (φ x : ℂ) * Complex.exp (z * (x : ℂ))) * Complex.exp (z * (t : ℂ)) := by
        rw [← integral_mul_const]
        congr 1 with x
        simp only [F, add_sub_cancel_right, Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc]
      _ = _ := rfl
  unfold compactLogMellin at ⊢
  calc
    _ = ∫ x, (∫ t, F x t ∂μ) := integral_congr_ae (Eventually.of_forall fun x ↦ (hin x).symm)
    _ = ∫ t, (∫ x, F x t) ∂μ := integral_integral_swap hi
    _ = ∫ t, compactLogMellin (fun x ↦ (φ x : ℂ)) z * Complex.exp (z * (t : ℂ)) ∂μ :=
      integral_congr_ae (Eventually.of_forall htrans)
    _ = _ := integral_const_mul _ _

end Masullo
