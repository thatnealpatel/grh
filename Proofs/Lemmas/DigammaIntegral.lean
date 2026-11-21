module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Gauss's integral for the digamma difference

Barner (p. 145) starts the Archimedean calculation with Gauss's
integral. We derive the subtracted form from Mathlib's Beta–Gamma
identity, keeping the cancellation at the singular endpoint.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Masullo

private noncomputable def digammaKernel (z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (z - 1) - 1) / (1 - (t : ℂ))

private theorem integrableOn_digammaKernel {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (digammaKernel z) (Ioo 0 1) := by
  have hpower : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ (z - 1)) volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_cpow' (by simpa using sub_lt_sub_right hz 1)
  have hleft : IntervalIntegrable (digammaKernel z) volume 0 (1 / 2) := by
    unfold digammaKernel
    simp only [div_eq_mul_inv]
    apply (hpower.sub intervalIntegrable_const).mul_continuousOn
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine (show Continuous (fun t : ℝ ↦ (1 : ℂ) - (t : ℂ)) by fun_prop).continuousOn.inv₀ ?_
    intro t ht
    rw [sub_ne_zero, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
    linarith [ht.2]
  let f (t : ℝ) := (t : ℂ) ^ (z - 1)
  have hf (t : ℝ) (ht : 0 < t) : DifferentiableAt ℝ f t := by
    exact differentiableAt_id.ofReal_cpow_const (z - 1) ht.ne'
  have hright : IntervalIntegrable (digammaKernel z) volume (1 / 2) 1 := by
    have hcont : ContinuousOn (fun t ↦ -dslope f 1 t) (Icc (1 / 2 : ℝ) 1) := by
      apply ContinuousOn.neg
      intro t ht
      rcases eq_or_ne t 1 with rfl | ht1
      · exact (continuousAt_dslope_same.mpr (hf 1 zero_lt_one)).continuousWithinAt
      · exact ((continuousAt_dslope_of_ne ht1).mpr
          (hf t (lt_of_lt_of_le (by norm_num) ht.1)).continuousAt).continuousWithinAt
    have hi : IntervalIntegrable (fun t ↦ -dslope f 1 t) volume (1 / 2) 1 :=
      hcont.intervalIntegrable_of_Icc (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hi ⊢
    refine (integrableOn_congr_fun ?_ measurableSet_Ioo).mp hi
    intro t ht
    change -dslope f 1 t = digammaKernel z t
    rw [dslope_of_ne f ht.2.ne, slope, Complex.real_smul]
    simp only [f, Complex.ofReal_one, one_cpow, digammaKernel, Complex.ofReal_inv,
      Complex.ofReal_sub, vsub_eq_sub]
    rw [show (t : ℂ) - 1 = -(1 - (t : ℂ)) by ring, inv_neg, neg_mul, neg_neg, div_eq_mul_inv,
      mul_comm]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (hleft.trans hright)

private theorem betaDifference_eq_quotient {z : ℂ} (hz : 0 < z.re) {e : ℝ} (he : 0 < e) :
    (∫ t in Ioo (0 : ℝ) 1, digammaKernel z t * (1 - (t : ℂ)) ^ (e : ℂ)) =
      (Gamma z * Gamma (1 + (e : ℂ)) / Gamma (z + (e : ℂ)) - 1) / (e : ℂ) := by
  have he' : 0 < (e : ℂ).re := he
  have hz' : 0 < (z + (e : ℂ)).re := add_pos hz he'
  have he0 : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he.ne'
  have hbeta : betaIntegral (1 : ℂ) (e : ℂ) = 1 / (e : ℂ) :=
    (betaIntegral_symm _ _).trans (betaIntegral_eval_one_right he')
  have hdiff : (∫ t in Ioo (0 : ℝ) 1, digammaKernel z t * (1 - (t : ℂ)) ^ (e : ℂ)) =
      betaIntegral z (e : ℂ) - betaIntegral 1 (e : ℂ) := by
    simp only [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rw [← integral_sub
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (betaIntegral_convergent hz he'))
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
        (betaIntegral_convergent (by simp : 0 < (1 : ℂ).re) he'))]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have hb : (1 : ℂ) - t ≠ 0 := by
      rw [sub_ne_zero, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
      exact ht.2.ne.symm
    simp only [digammaKernel, sub_self, cpow_zero, one_mul, cpow_sub _ _ hb, cpow_one]
    ring
  rw [hdiff, hbeta, betaIntegral_eq_Gamma_mul_div _ _ hz he', add_comm (1 : ℂ), Gamma_add_one _ he0]
  field_simp

private theorem tendsto_gammaDifference {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun e : ℝ ↦ (Gamma z * Gamma (1 + (e : ℂ)) / Gamma (z + (e : ℂ)) - 1) / (e : ℂ))
      (𝓝[>] 0) (𝓝 (digamma 1 - digamma z)) := by
  have hz0 := Gamma_ne_zero_of_re_pos hz
  let F (e : ℂ) := Gamma z * Gamma (1 + e) / Gamma (z + e)
  have hF0 : F 0 = 1 := by simp [F, hz0]
  have htranslate (w : ℂ) (hw : 0 < w.re) :
      HasDerivAt (fun e : ℂ ↦ Gamma (w + e)) (deriv Gamma w) 0 := by
    have h := (hasDerivAt_Gamma_of_re_pos hw).differentiableAt.hasDerivAt
    exact HasDerivAt.comp_const_add w 0 (by simpa only [add_zero] using h)
  have hF : HasDerivAt F (digamma 1 - digamma z) (0 : ℂ) := by
    convert ((htranslate 1 (by simp)).const_mul (Gamma z)).div (htranslate z hz)
      (by simpa using hz0) using 1
    simp only [digamma_def, logDeriv_apply, Gamma_one, div_one, add_zero, mul_one]
    field_simp
  have hreal : HasDerivAt (fun e : ℝ ↦ F (e : ℂ)) (digamma 1 - digamma z) 0 := by
    exact HasDerivAt.comp_ofReal (by simpa only [Complex.ofReal_zero] using hF)
  have hreal0 : F ((0 : ℝ) : ℂ) = 1 := by simpa only [Complex.ofReal_zero] using hF0
  have h := hreal.tendsto_slope_zero_right
  simp only [zero_add, Complex.real_smul, Complex.ofReal_inv, hreal0] at h
  simpa only [div_eq_inv_mul, F] using h

/-- The subtracted Gauss integral on the open right half-plane, with
absolute integrability. This is the scalar input used in Barner's
Archimedean argument cited after (B.4.2.16), p. 616. -/
public theorem digamma_one_sub_eq_integral {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ (z - 1) - 1) / (1 - (t : ℂ))) (Ioo 0 1) ∧
    (∫ t in Ioo (0 : ℝ) 1, ((t : ℂ) ^ (z - 1) - 1) / (1 - (t : ℂ))) = digamma 1 - digamma z := by
  have hK := integrableOn_digammaKernel hz
  refine ⟨hK, ?_⟩
  change (∫ t in Ioo (0 : ℝ) 1, digammaKernel z t) = _
  let F (e : ℝ) (t : ℝ) := digammaKernel z t * (1 - (t : ℂ)) ^ (e : ℂ)
  have hb (t : ℝ) : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
  have hlim : Tendsto (fun e ↦ ∫ t in Ioo (0 : ℝ) 1, F e t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioo (0 : ℝ) 1, digammaKernel z t)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ ‖digammaKernel z t‖) ?_ ?_ hK.norm ?_
    refine Eventually.of_forall ?_
    · intro e
      have hc : ContinuousOn (fun t : ℝ ↦ (1 - (t : ℂ)) ^ (e : ℂ)) (Ioo (0 : ℝ) 1) := by
        intro t ht
        refine ContinuousAt.continuousWithinAt (ContinuousAt.cpow (by fun_prop) continuousAt_const ?_)
        rw [hb, Complex.ofReal_mem_slitPlane]
        exact sub_pos.mpr ht.2
      exact hK.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioo)
    · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with e he
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      change ‖digammaKernel z t * (1 - (t : ℂ)) ^ (e : ℂ)‖ ≤ ‖digammaKernel z t‖
      rw [norm_mul, hb, norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr ht.2), Complex.ofReal_re]
      exact mul_le_of_le_one_right (norm_nonneg _) <|
        Real.rpow_le_one (by linarith [ht.2]) (by linarith [ht.1]) he.le
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hb0 : (1 : ℂ) - (t : ℂ) ≠ 0 := by
        rw [hb, Complex.ofReal_ne_zero]
        exact (sub_pos.mpr ht.2).ne'
      have hpow : ContinuousAt (fun e : ℝ ↦ (1 - (t : ℂ)) ^ (e : ℂ)) 0 :=
        Complex.continuous_ofReal.continuousAt.const_cpow (Or.inl hb0)
      have hprod : ContinuousAt (F · t) 0 := continuousAt_const.mul hpow
      have hzero : F 0 t = digammaKernel z t := by simp [F]
      rw [← hzero]
      exact hprod.continuousWithinAt
  refine tendsto_nhds_unique hlim ((tendsto_gammaDifference hz).congr' ?_)
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with e he
  exact (betaDifference_eq_quotient hz he).symm

end Masullo
