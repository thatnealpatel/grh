module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Positivity of the real logarithmic Fourier band -/

open MeasureTheory Set
open scoped FourierTransform

namespace Masullo

private theorem intervalIntegrable_log_weight (K a b : ℝ) :
    IntervalIntegrable (fun w ↦ Real.log K - Real.log w) volume a b :=
  (intervalIntegrable_const).sub intervalIntegral.intervalIntegrable_log'

private theorem log_band_cos_half_pos {K : ℝ} (hK : 0 < K) (a : ℝ) :
    0 < ∫ w in (0 : ℝ)..K, (Real.log K - Real.log w) * Real.cos (a * w) := by
  let f (w : ℝ) := (Real.log K - Real.log w) * Real.cos (a * w)
  have hf : IntervalIntegrable f volume 0 K :=
    (intervalIntegrable_log_weight K 0 K).mul_continuousOn (by fun_prop)
  change 0 < ∫ w in (0 : ℝ)..K, f w
  by_cases ha : a = 0
  · refine intervalIntegral.intervalIntegral_pos_of_pos_on hf (fun w hw ↦ ?_) hK
    simpa [f, ha] using sub_pos.mpr (Real.log_lt_log hw.1 hw.2)
  -- A continuous version of (1 - cos (a*w)) / (a*w)^2 has value 1/2 at zero.
  let g (w : ℝ) := Real.sinc (a * w / 2) ^ 2 / 2
  have hg : Continuous g := (Real.continuous_sinc.comp (by fun_prop)).pow 2 |>.div_const 2
  have hg' (w : ℝ) (hw : w ≠ 0) : g w = (1 - Real.cos (a * w)) / (a * w) ^ 2 := by
    have haw := mul_ne_zero ha hw
    simp only [g, Real.sinc_of_ne_zero (div_ne_zero haw two_ne_zero)]
    conv_rhs => rw [show a * w = 2 * (a * w / 2) by ring, Real.cos_two_mul_eq_one_sub]
    field_simp
    ring
  have hg0 : 0 ≤ g := fun w ↦ by dsimp [g]; positivity
  have hgi : IntervalIntegrable g volume 0 K := hg.intervalIntegrable 0 K
  have hgpos : 0 < ∫ w in (0 : ℝ)..K, g w := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hK
      (continuousOn_const (c := (0 : ℝ))) hg.continuousOn (fun w _ ↦ hg0 w)
      ⟨0, ⟨le_rfl, hK.le⟩, by simp [g]⟩
    simpa using h
  -- Use a primitive of f - g, extending the boundary terms through zero.
  let P (w : ℝ) := (Real.log K * w - w * Real.log w) * Real.sinc (a * w) + w * g w
  have hP : Continuous P :=
    (((continuous_const.mul continuous_id).sub Real.continuous_mul_log).mul
      (Real.continuous_sinc.comp (by fun_prop))).add (continuous_id.mul hg)
  have hderiv (w : ℝ) (hw : w ∈ Ioo 0 K) : HasDerivAt P (f w - g w) w := by
    have hw' := hw.1.ne'
    have hl := (hasDerivAt_const w (Real.log K)).sub (Real.hasDerivAt_log hw')
    have hs := (Real.hasDerivAt_sin (a * w)).comp w ((hasDerivAt_id w).const_mul a)
    have hc := (Real.hasDerivAt_cos (a * w)).comp w ((hasDerivAt_id w).const_mul a)
    have hn := (hasDerivAt_const w (1 : ℝ)).sub hc
    have hd := ((hasDerivAt_id w).const_mul (a ^ 2))
    have h := (hl.mul (hs.div_const a)).add (hn.div hd (mul_ne_zero (pow_ne_zero 2 ha) hw'))
    have H : HasDerivAt (fun t ↦ (Real.log K - Real.log t) * (Real.sin (a * t) / a) +
        (1 - Real.cos (a * t)) / (a ^ 2 * t)) (f w - g w) w := by
      convert h using 1 <;> try rfl
      rw [hg' w hw']
      dsimp [f]
      field_simp
      ring
    apply H.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hw'] with t ht
    simp only [P, Real.sinc_of_ne_zero (mul_ne_zero ha ht), hg' t ht]
    field_simp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hK.le hP.continuousOn
    hderiv (hf.sub hgi)
  rw [intervalIntegral.integral_sub hf hgi] at he
  have hP0 : P 0 = 0 := by simp [P]
  have hPK : P K = K * g K := by simp [P, mul_comm (Real.log K) K]
  rw [hP0, hPK, sub_zero] at he
  linarith [mul_nonneg hK.le (hg0 K)]

private theorem log_band_eq_Icc (K : ℝ) : {w : ℝ | |w| ≤ K} = Icc (-K) K := by
  ext w
  change |w| ≤ K ↔ -K ≤ w ∧ w ≤ K
  exact abs_le

private theorem integrable_log_band_weight (K : ℝ) :
    IntegrableOn (fun w : ℝ ↦ Real.log K - Real.log |w|) {w : ℝ | |w| ≤ K} := by
  rw [log_band_eq_Icc, integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)]
  simpa only [Real.log_abs] using (intervalIntegrable_log_weight K (-K) K).1

/-- The cosine kernel of the finite logarithmic band is strictly positive
at every real argument, not only in the large-band limit. -/
public theorem real_log_band_cos_pos {K : ℝ} (hK : 0 < K) (a : ℝ) :
    0 < ∫ w in {w : ℝ | |w| ≤ K}, (Real.log K - Real.log |w|) * Real.cos (a * w) := by
  let f (w : ℝ) := (Real.log K - Real.log |w|) * Real.cos (a * w)
  have hi : IntervalIntegrable f volume (-K) K := by
    simpa only [f, Real.log_abs] using
      (intervalIntegrable_log_weight K (-K) K).mul_continuousOn
        (show ContinuousOn (fun w ↦ Real.cos (a * w)) _ by fun_prop)
  have hNK : -K ≤ K := by linarith
  have hi' := (intervalIntegrable_iff_integrableOn_Icc_of_le hNK).1 hi
  have hp : IntervalIntegrable f volume 0 K :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hK.le).2 (hi'.mono_set
      (Icc_subset_Icc_left (neg_nonpos.mpr hK.le)))
  have hn : IntervalIntegrable f volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (neg_nonpos.mpr hK.le)).2
      (hi'.mono_set (Icc_subset_Icc_right hK.le))
  have he : (∫ w in -K..(0 : ℝ), f w) = ∫ w in (0 : ℝ)..K, f w := by
    simpa [f] using (intervalIntegral.integral_comp_neg (a := 0) (b := K) (f := f)).symm
  change 0 < ∫ w in {w : ℝ | |w| ≤ K}, f w
  rw [log_band_eq_Icc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hNK,
    ← intervalIntegral.integral_add_adjacent_intervals hn hp, he]
  simpa only [f, Real.log_abs] using add_pos (log_band_cos_half_pos hK a)
    (log_band_cos_half_pos hK a)

/-- Strict positivity of the real part of the finite sharp scalar in
(12.4.1.24), p. 518, on the repaired rational real radial domain. The
input is any nonnegative integrable real test of positive mass. -/
public theorem real_log_fourier_sharp_pos {K : ℝ} (hK : 0 < K) {v : ℝ → ℝ}
    (hv : Integrable v) (hn : 0 ≤ᵐ[volume] v) (hm : 0 < ∫ x, v x) :
    0 < (∫ w in {w : ℝ | |w| ≤ K}, ((Real.log K - Real.log |w| : ℝ) : ℂ) *
      𝓕 (fun x ↦ (v x : ℂ)) w).re := by
  let s : Set ℝ := {w : ℝ | |w| ≤ K}
  let g (w : ℝ) : ℂ := (Real.log K - Real.log |w| : ℝ)
  let u (x : ℝ) : ℂ := v x
  let q := s.indicator g
  have hs : MeasurableSet s := measurableSet_le (by fun_prop) measurable_const
  have hq : Integrable q := (integrable_indicator_iff hs).2 (integrable_log_band_weight K).ofReal
  have hu : Integrable u := hv.ofReal
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hu hq
  rw [flip_innerₗ] at hflip
  change (∫ w, 𝓕 u w • q w) = ∫ x, u x • 𝓕 q x at hflip
  have he : (∫ w in s, g w * 𝓕 u w) = ∫ x, u x * 𝓕 q x := by
    rw [← integral_indicator hs]
    simpa only [smul_eq_mul, mul_comm (𝓕 u _), q, indicator_mul_left] using hflip
  have hqc : Continuous (𝓕 q) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hq
  have hi : Integrable (fun x ↦ u x * 𝓕 q x) :=
    hu.mul_bdd hqc.aestronglyMeasurable (.of_forall (Real.norm_fourier_le_integral_norm q))
  have hkernel (x : ℝ) : 0 < (𝓕 q x).re := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hj : Integrable (fun w : ℝ ↦ Complex.exp (↑(-2 * Real.pi * w * x) * Complex.I) • q w) := by
      refine hq.bdd_mul (c := 1) (by fun_prop) (.of_forall fun w ↦ ?_)
      simp [Complex.norm_exp, Complex.mul_re]
    have hjr := Complex.reCLM.integral_comp_comm hj
    simp only [Complex.reCLM_apply] at hjr
    rw [← hjr]
    have hrepr : (fun w : ℝ ↦ (Complex.exp (↑(-2 * Real.pi * w * x) * Complex.I) • q w).re) =
        s.indicator (fun w ↦ (Real.log K - Real.log |w|) * Real.cos ((2 * Real.pi * x) * w)) := by
      funext w
      by_cases hw : w ∈ s
      · simp only [q, smul_eq_mul, indicator_of_mem hw, g, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
        rw [show -2 * Real.pi * w * x = -(2 * Real.pi * x * w) by ring, Real.cos_neg, mul_comm]
      · simp [q, hw]
    rw [hrepr, integral_indicator hs]
    exact real_log_band_cos_pos hK (2 * Real.pi * x)
  change 0 < (∫ w in s, g w * 𝓕 u w).re
  rw [he]
  change 0 < Complex.reCLM (∫ x, u x * 𝓕 q x)
  rw [← Complex.reCLM.integral_comp_comm hi]
  have hr : (fun x ↦ Complex.reCLM (u x * 𝓕 q x)) = fun x ↦ v x * (𝓕 q x).re := by
    funext x
    simp [u, Complex.mul_re]
  have hip := Complex.reCLM.integrable_comp hi
  rw [hr] at hip ⊢
  refine (integral_pos_iff_support_of_nonneg_ae ?_ hip).2 ?_
  · filter_upwards [hn] with x hx using mul_nonneg hx (hkernel x).le
  · have heq : Function.support (fun x ↦ v x * (𝓕 q x).re) = Function.support v := by
      ext x
      simp [Function.mem_support, (hkernel x).ne']
    rw [heq]
    exact (integral_pos_iff_support_of_nonneg_ae hn hv).1 hm

end Masullo
