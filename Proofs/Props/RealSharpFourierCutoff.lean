module

public import Props.RealLogProfileHaar

/-! # The sharp real Fourier cutoff

This evaluates the scalar in Masullo (12.4.1.24), p. 518, after summing both
real unit signs and setting the rational norm-one quotient volume to one.
It does not derive that scalar from the preceding geometric integral.
-/

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace Masullo

/-- Sharp upper frequency exhaustion of the additive log pairing. The
logarithmic tail is absolutely integrable, and Fourier inversion at zero
cancels the constant part of the cutoff weight. -/
public theorem real_log_fourier_sharp_tendsto {u : ℝ → ℂ} (hu : Continuous u)
    (hzero : u 0 = 0) (hi : Integrable u) (huf : Integrable (𝓕 u))
    (hlog : Integrable (fun w ↦ (Real.log |w| : ℂ) * 𝓕 u w))
    (hright : Integrable (fun z ↦ u z / ((|z| : ℝ) : ℂ))) :
    Tendsto (fun L : ℝ ↦ ∫ w in {w | |w| ≤ L},
      ((Real.log L - Real.log |w| : ℝ) : ℂ) * 𝓕 u w) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ))) := by
  let s (L : ℝ) : Set ℝ := {w | |w| ≤ L}
  let g (w : ℝ) : ℂ := (Real.log |w| : ℂ) * 𝓕 u w
  have hg : Integrable g := hlog
  have hsm (L : ℝ) : MeasurableSet (s L) := measurableSet_le (by fun_prop) measurable_const
  have hmono : Monotone s := fun _ _ hab _ hw ↦ le_trans hw hab
  have huniv : ⋃ L, s L = univ := by
    ext w
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨|w|, show |w| ≤ |w| from le_rfl⟩
  have hexhaust {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {v : ℝ → E} (hv : Integrable v) :
      Tendsto (fun L ↦ ∫ w in s L, v w) atTop (𝓝 (∫ w, v w)) := by
    simpa only [huniv, setIntegral_univ] using
      tendsto_setIntegral_of_monotone hsm hmono hv.integrableOn
  have htail : Tendsto (fun L ↦ ∫ w in (s L)ᶜ, ‖g w‖) atTop (𝓝 0) := by
    simp_rw [setIntegral_compl (hsm _) hg.norm]
    simpa only [sub_self] using
      (tendsto_const_nhds (x := ∫ w, ‖g w‖)).sub (hexhaust hg.norm)
  have hweighted : Tendsto (fun L ↦ ∫ w in (s L)ᶜ, (Real.log L : ℂ) * 𝓕 u w)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ htail
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    refine (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_on (huf.const_mul (Real.log L : ℂ)).norm.integrableOn
        hlog.norm.integrableOn (hsm L).compl ?_)
    intro w hw
    have hwL : L < |w| := lt_of_not_ge hw
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
    have hlogw : Real.log L ≤ Real.log |w| :=
      Real.log_le_log (zero_lt_one.trans_le hL) hwL.le
    change ‖(Real.log L : ℂ) * 𝓕 u w‖ ≤ ‖(Real.log |w| : ℂ) * 𝓕 u w‖
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hlogL, abs_of_nonneg (hlogL.trans hlogw)]
    exact mul_le_mul_of_nonneg_right hlogw (norm_nonneg _)
  have hinv := congrFun (hu.fourierInv_fourier_eq hi huf) 0
  rw [Real.fourierInv_eq', hzero] at hinv
  have hmass : (∫ w, 𝓕 u w) = 0 := by simpa using hinv
  rw [← real_log_fourier_of_zero hu hzero hi huf hlog hright, ← zero_sub (∫ w, g w)]
  have hlimit : Tendsto (fun L ↦ -(∫ w in (s L)ᶜ, (Real.log L : ℂ) * 𝓕 u w) -
      (∫ w in s L, g w)) atTop (𝓝 (0 - ∫ w, g w)) := by
    simpa only [neg_zero] using hweighted.neg.sub (hexhaust hg)
  refine hlimit.congr ?_
  intro L
  -- The constant on the retained band equals minus the omitted tail.
  simp_rw [Complex.ofReal_sub, sub_mul]
  rw [integral_sub (huf.const_mul _).integrableOn hlog.integrableOn]
  rw [integral_const_mul, integral_const_mul, setIntegral_compl (hsm L) huf, hmass,
    zero_sub, mul_neg, neg_neg]

/-- The sharp scalar in (12.4.1.24) for the two-sign real log profile.
The reflected log argument represents inversion of `1 + z`. Vanishing
at log norm zero is enough; no support gap or moment condition is used. -/
public theorem real_log_profile_sharp_fourier_tendsto {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hzero : f 0 = 0) :
    let u := realLogProfileAdditive (fun t ↦ f (-t))
    Tendsto (fun L : ℝ ↦ ∫ w in {w | |w| ≤ L},
      ((Real.log L - Real.log |w| : ℝ) : ℂ) * 𝓕 u w) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ z, u z / ((|z| : ℝ) : ℂ))) := by
  intro u
  have hF : ContDiff ℝ ∞ (fun t ↦ f (-t)) := hf.comp contDiff_neg
  have hFc : HasCompactSupport (fun t ↦ f (-t)) := hc.comp_homeomorph (Homeomorph.neg ℝ)
  obtain ⟨hd, hk, h₀⟩ := real_log_profile_additive_test hF hFc
  have huz : u 0 = 0 := by simpa [u, hzero] using h₀
  let v := hk.toSchwartzMap hd
  refine real_log_fourier_sharp_tendsto (u := u) hd.continuous huz v.integrable
    (𝓕 v).integrable (RealLogFourier.log_fourier_integrable v) ?_
  simpa only [huz, zero_mul, sub_zero] using
    RealLogFourier.remainder_div_integrable (u := u) hd.continuous
      v.differentiable.differentiableAt v.integrable

end Masullo
