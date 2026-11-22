module

public import Lemmas.InteriorLogJet
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Bounded weighted convolution on the real log line -/

open MeasureTheory
open scoped ENNReal

namespace Masullo

noncomputable section

private abbrev LogL2 := Lp ℂ 2 (volume : Measure ℝ)

private def logConvolutionMajorant (s : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℝ :=
  2 ^ (s / 4) * symmetricStripWeightRoot 0 s y * ‖f y‖

private theorem logConvolutionMajorant_nonneg (s : ℝ) (f : ℝ → ℂ) (y : ℝ) :
    0 ≤ logConvolutionMajorant s f y := by
  unfold logConvolutionMajorant
  exact mul_nonneg (mul_nonneg (by positivity) (symmetricStripWeightRoot_pos ..).le) (norm_nonneg _)

private theorem continuous_logConvolutionMajorant {f : ℝ → ℂ} (hf : Continuous f) (s : ℝ) :
    Continuous (logConvolutionMajorant s f) :=
  (continuous_const.mul (continuous_symmetricStripWeightRoot 0 s)).mul hf.norm

private theorem hasCompactSupport_logConvolutionMajorant {f : ℝ → ℂ}
    (hcf : HasCompactSupport f) (s : ℝ) : HasCompactSupport (logConvolutionMajorant s f) :=
  hcf.norm.mul_left

private theorem stripWeightRoot_ratio_le {s : ℝ} (hs : 0 ≤ s) (x y : ℝ) :
    symmetricStripWeightRoot 0 s x / symmetricStripWeightRoot 0 s (x - y) ≤
      2 ^ (s / 4) * symmetricStripWeightRoot 0 s y := by
  apply (div_le_iff₀ (symmetricStripWeightRoot_pos ..)).2
  have hxy : 1 + x ^ 2 ≤ 2 * (1 + y ^ 2) * (1 + (x - y) ^ 2) := by
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y * (x - y))]
  simp only [symmetricStripWeightRoot_apply, zero_mul, Real.exp_zero, one_mul]
  calc
    _ ≤ (2 * (1 + y ^ 2) * (1 + (x - y) ^ 2)) ^ (s / 4) :=
      Real.rpow_le_rpow (by positivity) hxy (by positivity)
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]

private theorem norm_logConvolution_integrand_le {s : ℝ} (hs : 0 ≤ s)
    (f u : ℝ → ℂ) (x y : ℝ) :
    ‖(symmetricStripWeightRoot 0 s x : ℂ) *
      (f y * (u (x - y) / (symmetricStripWeightRoot 0 s (x - y) : ℂ)))‖ ≤
      logConvolutionMajorant s f y * ‖u (x - y)‖ := by
  simp only [norm_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (symmetricStripWeightRoot_pos ..).le, logConvolutionMajorant]
  calc
    _ = (symmetricStripWeightRoot 0 s x / symmetricStripWeightRoot 0 s (x - y)) *
        ‖f y‖ * ‖u (x - y)‖ := by simp only [div_eq_mul_inv]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (stripWeightRoot_ratio_le hs x y) (norm_nonneg _)) (norm_nonneg _)

private theorem measurable_logConvolution_integrand {s : ℝ} {f : ℝ → ℂ}
    (hf : Continuous f) (u : LogL2) :
    Measurable (fun p : ℝ × ℝ ↦ f p.2 *
      (u (p.1 - p.2) / (symmetricStripWeightRoot 0 s (p.1 - p.2) : ℂ))) := by
  have hu := (Lp.stronglyMeasurable u).measurable
  have hw := (Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot 0 s)).measurable
  have hsub : Measurable (fun p : ℝ × ℝ ↦ p.1 - p.2) := measurable_fst.sub measurable_snd
  exact hf.measurable.comp measurable_snd |>.mul ((hu.comp hsub).div (hw.comp hsub))

/-- The divided convolution integral is absolutely convergent at every `x` for the
`Lp` representative, before passing to the output `Lp` class. -/
public theorem integrable_weightedLogConvolution_integrand {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : Continuous f) (hcf : HasCompactSupport f)
    (u : Lp ℂ 2 (volume : Measure ℝ)) (x : ℝ) :
    Integrable (fun y : ℝ ↦ f y * (u (x - y) /
      (symmetricStripWeightRoot 0 s (x - y) : ℂ))) := by
  have hg : MemLp (logConvolutionMajorant s f) 2 volume :=
    (continuous_logConvolutionMajorant hf s).memLp_of_hasCompactSupport
      (hasCompactSupport_logConvolutionMajorant hcf s)
  have hu : MemLp (fun y ↦ ‖u (x - y)‖) 2 volume :=
    ((Lp.memLp u).comp_measurePreserving (volume.measurePreserving_sub_left x)).norm
  have hgu : Integrable (fun y ↦ logConvolutionMajorant s f y * ‖u (x - y)‖) :=
    memLp_one_iff_integrable.mp (hg.mul hu)
  have hpair : Measurable (fun y : ℝ ↦ (x, y)) := measurable_const.prodMk measurable_id
  have hm := (measurable_logConvolution_integrand (s := s) hf u).comp hpair
  have hI := hgu.mono' (measurable_const.mul hm).aestronglyMeasurable
    (ae_of_all volume (norm_logConvolution_integrand_le hs f u x))
  have hw : (symmetricStripWeightRoot 0 s x : ℂ) ≠ 0 := by
    exact_mod_cast (symmetricStripWeightRoot_pos 0 s x).ne'
  simpa only [Pi.mul_apply, Function.comp_apply, ← mul_assoc, inv_mul_cancel₀ hw, one_mul] using
    hI.const_mul (symmetricStripWeightRoot 0 s x : ℂ)⁻¹

private def logConvolutionValue (s : ℝ) (f u : ℝ → ℂ) (x : ℝ) : ℂ :=
  (symmetricStripWeightRoot 0 s x : ℂ) * ∫ y : ℝ,
    f y * (u (x - y) / (symmetricStripWeightRoot 0 s (x - y) : ℂ))

private theorem logConvolutionValue_congr {s : ℝ} {f : ℝ → ℂ} {u v : ℝ → ℂ}
    (h : u =ᵐ[volume] v) (x : ℝ) : logConvolutionValue s f u x = logConvolutionValue s f v x := by
  unfold logConvolutionValue
  congr 1
  apply integral_congr_ae
  have hshift := (volume.measurePreserving_sub_left x).quasiMeasurePreserving
  filter_upwards [h.comp_tendsto hshift.tendsto_ae] with y hy
  change u (x - y) = v (x - y) at hy
  rw [hy]

/-- Weighted Cauchy–Schwarz, with no division by the mass of the weight. -/
private theorem sq_lintegral_mul_le (g v : ℝ → ℝ≥0∞) (hg : Measurable g) (hv : Measurable v) :
    (∫⁻ y, g y * v y)^2 ≤ (∫⁻ y, g y) * ∫⁻ y, g y * (v y)^2 := by
  have hhalf (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hsquare (a : ℝ≥0∞) : (a ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = a := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hprod (a b : ℝ≥0∞) : a ^ (1 / 2 : ℝ) * (a * b ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = a * b := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc, ← pow_two, hhalf, hsquare]
  have hCS : (∫⁻ y, (g y) ^ (1 / 2 : ℝ) * (g y * (v y)^2) ^ (1 / 2 : ℝ)) ≤
      (∫⁻ y, g y) ^ (1 / 2 : ℝ) * (∫⁻ y, g y * (v y)^2) ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_norm_pow_le (μ := volume) hg.aemeasurable
      (hg.mul (hv.pow_const 2)).aemeasurable (p := 1 / 2) (q := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  simp_rw [hprod] at hCS
  simpa only [mul_pow, hhalf] using pow_le_pow_left' hCS 2

private theorem eLpNorm_two_eq {u : ℝ → ℂ} (hu : AEStronglyMeasurable u volume) :
    eLpNorm u 2 volume = (∫⁻ x, ‖u x‖ₑ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hu]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

private theorem logConvolutionValue_estimate {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (u : LogL2) :
    MemLp (logConvolutionValue s f u) 2 volume ∧
      eLpNorm (logConvolutionValue s f u) 2 volume ≤
        ENNReal.ofReal (∫ y, logConvolutionMajorant s f y) * eLpNorm u 2 volume := by
  let g : ℝ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (logConvolutionMajorant s f y)
  let v : ℝ → ℝ≥0∞ := fun x ↦ ‖u x‖ₑ
  have hg : Measurable g := (continuous_logConvolutionMajorant hf s).measurable.ennreal_ofReal
  have hv : Measurable v := (Lp.stronglyMeasurable u).measurable.eNorm
  have hgI : (∫⁻ y, g y) = ENNReal.ofReal (∫ y, logConvolutionMajorant s f y) :=
    (ofReal_integral_eq_lintegral_ofReal
      ((continuous_logConvolutionMajorant hf s).integrable_of_hasCompactSupport
        (hasCompactSupport_logConvolutionMajorant hcf s))
      (ae_of_all _ (logConvolutionMajorant_nonneg s f))).symm
  have hmeas : AEStronglyMeasurable (logConvolutionValue s f u) volume := by
    have hw := Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot 0 s)
    have hI := (measurable_logConvolution_integrand (s := s) hf u).stronglyMeasurable
    exact hw.aestronglyMeasurable.mul hI.integral_prod_right'.aestronglyMeasurable
  have hsection (x : ℝ) : ‖logConvolutionValue s f u x‖ₑ ≤ ∫⁻ y, g y * v (x - y) := by
    rw [logConvolutionValue, ← integral_const_mul]
    refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun y ↦ ?_)
    rw [show g y * v (x - y) = ENNReal.ofReal (logConvolutionMajorant s f y * ‖u (x - y)‖) by
      rw [ENNReal.ofReal_mul (logConvolutionMajorant_nonneg s f y), ofReal_norm], ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_logConvolution_integrand_le hs f u x y)
  have hprod : Measurable (fun p : ℝ × ℝ ↦ g p.2 * v (p.1 - p.2)^2) :=
    (hg.comp measurable_snd).mul ((hv.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  -- After swapping the integrals, translations preserve the inner squared norm.
  have hswap : (∫⁻ x : ℝ, ∫⁻ y : ℝ, g y * v (x - y)^2) =
      (∫⁻ y, g y) * ∫⁻ x, (v x)^2 := by
    rw [lintegral_lintegral_swap (f := fun x y ↦ g y * v (x - y)^2) hprod.aemeasurable]
    calc
      _ = ∫⁻ y, g y * ∫⁻ x, (v x)^2 := by
        refine lintegral_congr fun y ↦ ?_
        have hy : Measurable (fun x : ℝ ↦ v (x - y)^2) :=
          (hv.comp (measurable_id.sub measurable_const)).pow_const 2
        rw [lintegral_const_mul _ hy]
        congr 1
        exact (measurePreserving_sub_right volume y).lintegral_comp (hv.pow_const 2)
      _ = _ := lintegral_mul_const _ hg
  have hsq : (∫⁻ x, ‖logConvolutionValue s f u x‖ₑ ^ (2 : ℕ)) ≤
      (∫⁻ y, g y)^2 * ∫⁻ x, (v x)^2 := calc
    _ ≤ ∫⁻ x : ℝ, (∫⁻ y, g y) * ∫⁻ y, g y * v (x - y)^2 := by
      refine lintegral_mono fun x ↦ (pow_le_pow_left' (hsection x) 2).trans ?_
      exact sq_lintegral_mul_le g (fun y ↦ v (x - y)) hg
        (hv.comp (measurable_const.sub measurable_id))
    _ = _ := by
      rw [lintegral_const_mul _ hprod.lintegral_prod_right', hswap, pow_two, mul_assoc]
  have hbound : eLpNorm (logConvolutionValue s f u) 2 volume ≤
      ENNReal.ofReal (∫ y, logConvolutionMajorant s f y) * eLpNorm u 2 volume := by
    rw [eLpNorm_two_eq hmeas, eLpNorm_two_eq (Lp.aestronglyMeasurable u), ← hgI]
    refine (ENNReal.rpow_le_rpow hsq (by norm_num : 0 ≤ (1 / 2 : ℝ))).trans_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num [v]
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp u).eLpNorm_lt_top),
    hbound⟩

private def logConvolutionLinear {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) : LogL2 →ₗ[ℂ] LogL2 where
  toFun u := (logConvolutionValue_estimate hs hf hcf u).1.toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(logConvolutionValue_estimate hs hf hcf (u + v)).1.coeFn_toLp,
      Lp.coeFn_add ((logConvolutionValue_estimate hs hf hcf u).1.toLp _)
        ((logConvolutionValue_estimate hs hf hcf v).1.toLp _),
      (logConvolutionValue_estimate hs hf hcf u).1.coeFn_toLp,
      (logConvolutionValue_estimate hs hf hcf v).1.coeFn_toLp] with x huv hadd hu hv
    rw [huv, hadd, Pi.add_apply, hu, hv, logConvolutionValue_congr (Lp.coeFn_add u v)]
    simp only [logConvolutionValue, Pi.add_apply, add_div, mul_add,
      integral_add (integrable_weightedLogConvolution_integrand hs hf hcf u x)
        (integrable_weightedLogConvolution_integrand hs hf hcf v x)]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(logConvolutionValue_estimate hs hf hcf (c • u)).1.coeFn_toLp,
      Lp.coeFn_smul c ((logConvolutionValue_estimate hs hf hcf u).1.toLp _),
      (logConvolutionValue_estimate hs hf hcf u).1.coeFn_toLp] with x hcu hsmul hu
    rw [RingHom.id_apply]
    rw [hcu, hsmul, Pi.smul_apply, hu, logConvolutionValue_congr (Lp.coeFn_smul c u)]
    simp only [logConvolutionValue, Pi.smul_apply, smul_eq_mul, mul_div_assoc,
      mul_left_comm (f _ : ℂ) c, integral_const_mul, mul_left_comm _ c]

private theorem logConvolutionLinear_bound {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (u : LogL2) :
    ‖logConvolutionLinear hs hf hcf u‖ ≤ (∫ y, logConvolutionMajorant s f y) * ‖u‖ := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u))
    (logConvolutionValue_estimate hs hf hcf u).2
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integral_nonneg (logConvolutionMajorant_nonneg s f)), ← Lp.norm_def] at h
  simpa only [logConvolutionLinear, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp] using h

/-- Convolution by a compactly supported continuous kernel, conjugated by multiplication
by the square root of the symmetric-strip weight with `α = 0`. -/
public def weightedLogConvolution {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (logConvolutionLinear hs hf hcf).mkContinuous (∫ y, logConvolutionMajorant s f y)
    (logConvolutionLinear_bound hs hf hcf)

/-- The operator acts on representatives by dividing by the weight, convolving,
and multiplying the result by the weight, up to a volume-null set. -/
public theorem weightedLogConvolution_ae {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (⇑(weightedLogConvolution hs hf hcf u) : ℝ → ℂ) =ᵐ[volume]
      (fun x ↦ (symmetricStripWeightRoot 0 s x : ℂ) * ∫ y : ℝ,
        f y * (u (x - y) / (symmetricStripWeightRoot 0 s (x - y) : ℂ))) :=
  (logConvolutionValue_estimate hs hf hcf u).1.coeFn_toLp

/-- Weighted `L¹` control of the convolution operator norm. -/
public theorem norm_weightedLogConvolution_le {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    ‖weightedLogConvolution hs hf hcf‖ ≤ 2 ^ (s / 4) *
      ∫ y : ℝ, symmetricStripWeightRoot 0 s y * ‖f y‖ := by
  have h := (logConvolutionLinear hs hf hcf).mkContinuous_norm_le
    (integral_nonneg (logConvolutionMajorant_nonneg s f)) (logConvolutionLinear_bound hs hf hcf)
  simpa only [weightedLogConvolution, logConvolutionMajorant, mul_assoc, integral_const_mul] using h

end

end Masullo
