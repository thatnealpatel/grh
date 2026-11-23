module

public import Lemmas.CompactLogMellinAdjoint
public import Mathlib.Analysis.Analytic.Basic
import Lemmas.FilteredLogDensityAnalyticAverage
import Lemmas.FilteredLogDensityFactor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Adjoint-filtered positive-log densities -/

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

/-- The adjoint-filtered density averaged over a translation measure. -/
@[expose] public noncomputable def filteredLogDensity (μ : Measure ℝ) (P : Polynomial ℝ)
    (r t : ℝ) : ℝ :=
  ∫ u, logPolynomialAdjoint P
    (fun x ↦ Real.exp (r * x) / (1 - Real.exp (-2 * x))) (t + u) ∂μ

private theorem positiveLogDenom_ne_zero {s : ℝ} (hs : 0 < s) :
    1 - Real.exp (-2 * s) ≠ 0 :=
  sub_ne_zero.mpr ((Real.exp_lt_one_iff.mpr (by linarith : -2 * s < 0)).ne.symm)

/-- The geometric log density is smooth away from its possible pole at zero. -/
public theorem contDiffOn_rationalLogTraceDensity (r : ℝ) :
    ContDiffOn ℝ ∞ (fun x ↦ Real.exp (r * x) / (1 - Real.exp (-2 * x))) (Ioi 0) := by
  refine (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn.div
    ((contDiff_const.sub (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).contDiffOn) ?_
  exact fun _ h ↦ positiveLogDenom_ne_zero h

private theorem adjoint_exp (P : Polynomial ℝ) (r s : ℝ) :
    logPolynomialAdjoint P (fun x ↦ Real.exp (r * x)) s = P.eval (-r) * Real.exp (r * s) := by
  rw [logPolynomialAdjoint, Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [iteratedDeriv_exp_const_mul, neg_pow]
  ring

private theorem adjoint_logKernel_split (P : Polynomial ℝ) (r : ℝ) {s : ℝ} (hs : 0 < s) :
    logPolynomialAdjoint P (fun x ↦ Real.exp (r * x) / (1 - Real.exp (-2 * x))) s =
      P.eval (-r) * Real.exp (r * s) +
        logPolynomialAdjoint P (fun x ↦ Real.exp ((r - 2) * x) / (1 - Real.exp (-2 * x))) s := by
  let f : ℝ → ℝ := fun x ↦ Real.exp (r * x)
  let g : ℝ → ℝ := fun x ↦ Real.exp ((r - 2) * x) / (1 - Real.exp (-2 * x))
  have hfg : (fun x ↦ Real.exp (r * x) / (1 - Real.exp (-2 * x))) =ᶠ[𝓝 s] f + g := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
    have hden := positiveLogDenom_ne_zero hx
    change Real.exp (r * x) / (1 - Real.exp (-2 * x)) =
      Real.exp (r * x) + Real.exp ((r - 2) * x) / (1 - Real.exp (-2 * x))
    rw [show (r - 2) * x = r * x + -2 * x by ring, Real.exp_add]
    generalize Real.exp (-2 * x) = q at hden ⊢
    field_simp
    ring
  have hf : ContDiffAt ℝ ∞ f s :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hg : ContDiffAt ℝ ∞ g s :=
    ((contDiffOn_rationalLogTraceDensity (r - 2)) s hs).contDiffAt (isOpen_Ioi.mem_nhds hs)
  change _ = P.eval (-r) * Real.exp (r * s) + logPolynomialAdjoint P g s
  rw [← adjoint_exp]
  simp only [logPolynomialAdjoint, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [hfg.iteratedDeriv_eq n, iteratedDeriv_add (hf.of_le (by simp)) (hg.of_le (by simp))]
  ring

private theorem integrable_of_continuousOn_carrying {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D : ℝ} (hD : ∀ᵐ u ∂μ, u ∈ Icc 0 D) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 D)) :
    Integrable g μ := by
  simpa only [Measure.restrict_eq_self_of_ae_mem hD] using
    (hg.integrableOn_compact (μ := μ) isCompact_Icc).integrable

/-- Remove the first exponential term of the geometric log kernel before averaging. -/
public theorem filteredLogDensity_sub_exp {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) (P : Polynomial ℝ) (r : ℝ) :
    EqOn (filteredLogDensity μ P r)
      (fun t ↦ Real.exp (r * t) * (P.eval (-r) * ∫ u, Real.exp (r * u) ∂μ) +
        filteredLogDensity μ P (r - 2) t) (Ioi 0) := by
  intro t ht
  have hD : ∀ᵐ u ∂μ, u ∈ Icc 0 D := ae_iff.mpr hμ
  have ht' : 0 < t := ht
  let g : ℝ → ℝ := fun u ↦ logPolynomialAdjoint P
    (fun x ↦ Real.exp ((r - 2) * x) / (1 - Real.exp (-2 * x))) (t + u)
  have hg : Integrable g μ := integrable_of_continuousOn_carrying hD
    ((logPolynomialAdjoint_continuousOn P (contDiffOn_rationalLogTraceDensity (r - 2))).comp
      (continuous_const.add continuous_id).continuousOn
      (fun _ hu ↦ add_pos_of_pos_of_nonneg ht' hu.1))
  have hi : Integrable (fun u ↦ (Real.exp (r * t) * P.eval (-r)) * Real.exp (r * u)) μ :=
    (integrable_of_continuousOn_carrying hD
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).const_mul _
  calc
    filteredLogDensity μ P r t =
        ∫ u, (Real.exp (r * t) * P.eval (-r)) * Real.exp (r * u) + g u ∂μ := by
      unfold filteredLogDensity
      apply integral_congr_ae
      filter_upwards [hD] with u hu
      rw [adjoint_logKernel_split P r (add_pos_of_pos_of_nonneg ht' hu.1), mul_add, Real.exp_add]
      dsimp [g]
      ring
    _ = _ := by
      rw [integral_add hi hg, integral_const_mul, mul_assoc]
      rfl

/-- Use a globally continuous clamped parameter for the geometric factor. Near
zero the clamp is the identity. Compact parametric integration gives a uniform
bound on the integrand over a compact neighborhood of zero times the carrying
interval, so the limiting argument does not require estimates at the pole. -/
private theorem filteredLogDensity_tendsto_of_factor {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) {P : Polynomial ℝ} {r : ℝ} {A : ℂ → ℂ}
    (hA : ContinuousOn A (Metric.ball 0 1)) (hA0 : (A 0).re = P.eval (-r))
    (hfac : ∀ s : ℝ, 0 < s → logPolynomialAdjoint P
      (fun x ↦ Real.exp (r * x) / (1 - Real.exp (-2 * x))) s =
      Real.exp (r * s) * (A (↑(Real.exp (-2 * s)) : ℂ)).re) :
    Tendsto (fun t ↦ Real.exp (-r * t) * filteredLogDensity μ P r t)
      atTop (𝓝 (P.eval (-r) * ∫ u, Real.exp (r * u) ∂μ)) := by
  have hD : ∀ᵐ u ∂μ, u ∈ Icc 0 D := ae_iff.mpr hμ
  have hr := Measure.restrict_eq_self_of_ae_mem hD
  let c (x : ℝ) : ℝ := max (-(1 / 2)) (min x (1 / 2))
  let z (p : ℝ × ℝ) : ℂ := ↑(c p.1 * Real.exp (-2 * max 0 p.2))
  let F (x u : ℝ) : ℝ := Real.exp (r * u) * (A (z (x, u))).re
  have hz (p : ℝ × ℝ) : z p ∈ Metric.ball (0 : ℂ) 1 := by
    have hc : |c p.1| ≤ 1 / 2 := abs_le.mpr
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
    have he := Real.exp_le_one_iff.mpr (show -2 * max 0 p.2 ≤ 0 by
      nlinarith [le_max_left (0 : ℝ) p.2])
    rw [Metric.mem_ball, dist_zero_right]
    change ‖(↑(c p.1 * Real.exp (-2 * max 0 p.2)) : ℂ)‖ < 1
    rw [Complex.norm_real, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (1 / 2) * 1 := mul_le_mul hc he (Real.exp_pos _).le (by norm_num)
      _ < _ := by norm_num
  have hzc : Continuous z := by
    unfold z c
    fun_prop
  have hFc : Continuous (uncurry F) := by
    change Continuous (fun p : ℝ × ℝ ↦ Real.exp (r * p.2) * (A (z p)).re)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul
      (Complex.continuous_re.comp (hA.comp_continuous hzc hz))
  let G (x : ℝ) : ℝ := ∫ u in Icc 0 D, F x u ∂μ
  have hG : Continuous G := continuous_parametric_integral_of_continuous hFc isCompact_Icc
  have hG0 : G 0 = P.eval (-r) * ∫ u, Real.exp (r * u) ∂μ := by
    have hc0 : c 0 = 0 := by norm_num [c]
    simp only [G, F, z, hc0, zero_mul, Complex.ofReal_zero, hA0, hr]
    simp_rw [mul_comm _ (P.eval (-r)), integral_const_mul]
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-2 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg
      (by norm_num : (-2 : ℝ) < 0)).2 tendsto_id)
  rw [← hG0]
  refine (hG.continuousAt.tendsto.comp hexp).congr' ?_
  have hexp' : ∀ᶠ t : ℝ in atTop, Real.exp (-2 * t) < 1 / 2 :=
    hexp.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hexp'] with t ht he
  have hc' : c (Real.exp (-2 * t)) = Real.exp (-2 * t) := by
    change max (-(1 / 2)) (min (Real.exp (-2 * t)) (1 / 2)) = _
    rw [min_eq_left he.le, max_eq_right]
    exact (by norm_num : (-(1 / 2) : ℝ) ≤ 0).trans (Real.exp_pos _).le
  change (∫ u in Icc 0 D, F (Real.exp (-2 * t)) u ∂μ) =
    Real.exp (-r * t) * filteredLogDensity μ P r t
  rw [hr, filteredLogDensity, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hD] with u hu
  have heq : z (Real.exp (-2 * t), u) = (↑(Real.exp (-2 * (t + u))) : ℂ) := by
    dsimp [z]
    rw [hc', max_eq_right hu.1, ← Real.exp_add]
    congr 2
    ring
  change Real.exp (r * u) * (A (z (Real.exp (-2 * t), u))).re = _
  rw [heq, hfac _ (add_pos_of_pos_of_nonneg ht hu.1),
    show r * (t + u) = r * t + r * u by ring, Real.exp_add (r * t) (r * u)]
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add,
    show -r * t + r * t = 0 by ring, Real.exp_zero, one_mul]

/-- The normalized average tends to the first exponential coefficient. -/
public theorem filteredLogDensity_tendsto {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) (P : Polynomial ℝ) (r : ℝ) :
    Tendsto (fun t ↦ Real.exp (-r * t) * filteredLogDensity μ P r t)
      atTop (𝓝 (P.eval (-r) * ∫ u, Real.exp (r * u) ∂μ)) := by
  obtain ⟨A, hA, hA0, hfac⟩ := exists_filteredLogDensity_factor P r
  exact filteredLogDensity_tendsto_of_factor hμ hA.continuousOn hA0 hfac

private noncomputable def complexDensityFactor (A : ℂ → ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((r : ℂ) * z) * A (Complex.exp (-2 * z))

private theorem complexDensityFactor_analytic (A : ℂ → ℂ) (r : ℝ)
    (hA : AnalyticOnNhd ℂ A (Metric.ball 0 1)) :
    AnalyticOnNhd ℂ (complexDensityFactor A r) {z : ℂ | 0 < z.re} := by
  intro z hz
  have harg : Complex.exp (-2 * z) ∈ Metric.ball (0 : ℂ) 1 := by
    have hz' : 0 < z.re := hz
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp, Real.exp_lt_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.re_ofNat,
      Complex.im_ofNat, neg_zero, zero_mul, sub_zero]
    linarith
  have hlin (a : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ a * w) z := analyticAt_const.mul analyticAt_id
  have ha : AnalyticAt ℂ (fun w : ℂ ↦ A (Complex.exp (-2 * w))) z :=
    AnalyticAt.comp (f := fun w : ℂ ↦ Complex.exp (-2 * w)) (hA _ harg) (hlin (-2)).cexp'
  exact (hlin (r : ℂ)).cexp'.mul ha

private theorem complexDensityFactor_re (A : ℂ → ℂ) (r s : ℝ) :
    (complexDensityFactor A r (Complex.ofReal s)).re =
      Real.exp (r * s) * (A (Complex.ofReal (Real.exp (-2 * s)))).re := by
  unfold complexDensityFactor
  have hneg : (-2 : ℂ) = ((-2 : ℝ) : ℂ) := by norm_num
  have he (a : ℝ) : Complex.exp ((a : ℂ) * (s : ℂ)) = (Real.exp (a * s) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_exp]
  rw [hneg, he r, he (-2)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The averaged adjoint is real analytic away from the log kernel's pole. -/
public theorem filteredLogDensity_analyticOnNhd {μ : Measure ℝ} [IsFiniteMeasure μ]
    {D : ℝ} (hμ : μ (Icc 0 D)ᶜ = 0) (P : Polynomial ℝ) (r : ℝ) :
    AnalyticOnNhd ℝ (filteredLogDensity μ P r) (Ioi 0) := by
  obtain ⟨A, hA, _, hfac⟩ := exists_filteredLogDensity_factor P r
  have hAvg := compactLogAverage_analyticOnNhd hμ (complexDensityFactor_analytic A r hA)
  have hD : ∀ᵐ u ∂μ, u ∈ Icc 0 D := ae_iff.mpr hμ
  intro t ht
  refine (hAvg t ht).congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  unfold filteredLogDensity
  apply integral_congr_ae
  filter_upwards [hD] with u hu
  rw [complexDensityFactor_re, hfac _ (add_pos_of_pos_of_nonneg hx hu.1)]

end Masullo
