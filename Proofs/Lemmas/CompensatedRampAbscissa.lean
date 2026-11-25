module

public import Lemmas.CompensatedRampContinuation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Mellin convergence for the nonnegative compensated von Mangoldt ramp

Source: Bob, `5f22f5a60aef:.godel/bob/unsigned-edge-rh.md:24–30` (ramp on line 15).
Owning check session: `01a21012-2ca1-71e9-a51f-6efd061fa400`.

Scope: eventual nonnegativity of the compensated ramp and real-axis nonvanishing
of zeta on `(1/2, 1)` imply actual Mellin tail integrability for every real `r > 1/2`.
The proof starts with the convergent formula on `Re s > 1`, uses the removable
singularity at `1`, and rules out any abscissa above `1/2` by Landau's lemma.
It asserts neither convergence at `1/2` nor nonvanishing at nonreal points.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace PrimeSquareRamp

-- Keep the actual tail holomorphic strictly inside its region of integrability.
private theorem analyticOnNhd_mellinTail_of_converges {g : ℝ → ℝ} {A α : ℝ}
    (hA : 2 ≤ A) (hg : AEMeasurable g (volume.restrict (Ioi A)))
    (hconv : ∀ r > α, Masullo.MellinTailConverges g A r) :
    AnalyticOnNhd ℂ (Masullo.nonnegativeMellinTail g A) {s | α < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change α < s.re at hs
  obtain ⟨q, hq, hqs⟩ := exists_between hs
  obtain ⟨p, hp, hpq⟩ := exists_between hq
  let μ := volume.restrict (Ioi A)
  let F (z : ℂ) (x : ℝ) := (g x : ℂ) * (x : ℂ) ^ (-(z + 1))
  let F' (z : ℂ) (x : ℝ) := F z x * (-(Real.log x : ℂ))
  have hx : ∀ᵐ x ∂μ, 1 ≤ x := (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦
    (show 1 ≤ A by linarith).trans (mem_Ioi.mp hx).le
  have hm (z : ℂ) : AEMeasurable (F z) μ := by
    refine (Complex.continuous_ofReal.measurable.comp_aemeasurable hg).mul ?_
    refine ContinuousOn.aemeasurable (continuousOn_of_forall_continuousAt ?_) measurableSet_Ioi
    intro x hx
    exact continuousAt_ofReal_cpow_const _ _ (Or.inr (show 0 < x by
      linarith [mem_Ioi.mp hx]).ne')
  have hn (z : ℂ) (x : ℝ) (hx : 1 ≤ x) : ‖F z x‖ = ‖g x‖ * x ^ (-(z.re + 1)) := by
    simp [F, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
  have hi (z : ℂ) (hz : α < z.re) : Integrable (F z) μ := by
    refine (show Integrable (fun x ↦ g x * x ^ (-(z.re + 1))) μ from hconv _ hz).norm.mono'
      (hm z).aestronglyMeasurable (hx.mono fun x hx ↦ ?_)
    rw [hn _ _ hx, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)]
  -- The gap `q - p` absorbs the logarithm in the kernel derivative.
  let bound (x : ℝ) := ‖g x * x ^ (-(p + 1))‖ / (q - p)
  have hbound : Integrable bound μ :=
    (show Integrable (fun x ↦ g x * x ^ (-(p + 1))) μ from hconv _ hp).norm.div_const _
  have hlocal : {z : ℂ | q < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hqs
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') hlocal
    (Eventually.of_forall fun z ↦ (hm z).aestronglyMeasurable) (hi s hs)
    ((hm s).mul
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg.aemeasurable)
      |>.aestronglyMeasurable)
    (hx.mono fun x hx z hz ↦ by
      change q < z.re at hz
      have hx' := zero_lt_one.trans_le hx
      rw [show ‖F' z x‖ = (‖g x‖ * x ^ (-(z.re + 1))) * Real.log x by
        change ‖F z x * -(Real.log x : ℂ)‖ = _
        rw [norm_mul, hn _ _ hx, norm_neg, Complex.norm_real,
          Real.norm_of_nonneg (Real.log_nonneg hx)]]
      calc
        _ ≤ (‖g x‖ * x ^ (-(q + 1))) * (x ^ (q - p) / (q - p)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
              (norm_nonneg _)) (Real.log_le_rpow_div hx'.le (sub_pos.mpr hpq))
            (Real.log_nonneg hx) (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx'.le _))
        _ = bound x := by
          change _ = ‖g x * x ^ (-(p + 1))‖ / (q - p)
          rw [← mul_div_assoc, mul_assoc, ← Real.rpow_add hx',
            show -(q + 1) + (q - p) = -(p + 1) by ring,
            norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx'.le _)])
    hbound (hx.mono fun x hx z _ ↦ by
      have hx' := zero_lt_one.trans_le hx
      have hd := (((hasDerivAt_id z).add_const 1).neg.const_cpow
        (c := (x : ℂ)) (Or.inl (ofReal_ne_zero.mpr hx'.ne'))).const_mul (g x : ℂ)
      convert hd using 1
      · rfl
      · rw [← ofReal_log hx'.le]
        dsimp [F, F', id]
        ring)
  exact hderiv.2.differentiableAt.differentiableWithinAt

-- Patch only the analytic expression at `1`, not the actual tail integral there.
private theorem exists_realRay_compensatedFormula (K : ℝ) {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J univ)
    (hζ : ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) :
    ∃ F : ℂ → ℂ, (∀ t : ℝ, 1 / 2 < t → AnalyticAt ℂ F (t : ℂ)) ∧
      ∀ s : ℂ, 1 < s.re → F s =
        2 * (K : ℂ) / (s - 1 / 2) ^ 3 + logDeriv riemannZeta s / s ^ 2 + 1 / (s - 1) - J s := by
  obtain ⟨P, hP, hP_eq⟩ := exists_analyticAt_compensated_zeta_one
  let M (s : ℂ) := 2 * (K : ℂ) / (s - 1 / 2) ^ 3
  let F (s : ℂ) := M s + (if s = 1 then P 1 else
    logDeriv riemannZeta s / s ^ 2 + 1 / (s - 1)) - J s
  have hM {s : ℂ} (hs : 1 / 2 < s.re) : AnalyticAt ℂ M s := by
    have hn : s - 1 / 2 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hid : AnalyticAt ℂ (fun z : ℂ ↦ z) s := analyticAt_id
    have hd : AnalyticAt ℂ (fun z : ℂ ↦ z - 1 / 2) s := hid.sub analyticAt_const
    have hc : AnalyticAt ℂ (fun _ : ℂ ↦ 2 * (K : ℂ)) s := analyticAt_const
    exact hc.div (hd.pow 3) (pow_ne_zero _ hn)
  have hF₁ : AnalyticAt ℂ F 1 := by
    refine (((hM (s := 1) (by norm_num)).add hP).sub (hJ 1 (mem_univ _))).congr ?_
    filter_upwards [eventually_nhdsWithin_iff.mp hP_eq] with s hs
    by_cases h : s = 1
    · simp [F, h]
    · have heq := hs (show s ∈ ({1} : Set ℂ)ᶜ from h)
      simp [F, h, heq]
  have hζ_analytic : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    refine DifferentiableOn.analyticOnNhd ?_ isClosed_singleton.isOpen_compl
    intro z hz
    exact DifferentiableAt.differentiableWithinAt (differentiableAt_riemannZeta hz)
  have hF_real (t : ℝ) (ht : 1 / 2 < t) : AnalyticAt ℂ F (t : ℂ) := by
    by_cases ht₁ : (t : ℂ) = 1
    · simpa only [ht₁] using hF₁
    have htn : t ≠ 1 := fun h ↦ ht₁ (by simp [h])
    have hz : riemannZeta (t : ℂ) ≠ 0 := by
      rcases lt_or_gt_of_ne htn with h | h
      · exact hζ t ht h
      · exact riemannZeta_ne_zero_of_one_lt_re (by simpa only [ofReal_re] using h)
    have ht₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
    have ha : AnalyticAt ℂ riemannZeta (t : ℂ) := hζ_analytic _ ht₁
    have hlog : AnalyticAt ℂ (logDeriv riemannZeta) (t : ℂ) := ha.deriv.div ha hz
    have hid : AnalyticAt ℂ (fun s : ℂ ↦ s) (t : ℂ) := analyticAt_id
    have hsum := (hlog.div (hid.pow 2) (pow_ne_zero _ ht₀)).add
      (analyticAt_const.div (hid.sub analyticAt_const) (sub_ne_zero.mpr ht₁) :
        AnalyticAt ℂ (fun s : ℂ ↦ 1 / (s - 1)) (t : ℂ))
    refine (((hM (by simpa only [ofReal_re] using ht)).add hsum).sub
      (hJ _ (mem_univ _))).congr ?_
    filter_upwards [eventually_ne_nhds ht₁] with s hs
    simp [F, hs]
  refine ⟨F, hF_real, fun s hs ↦ ?_⟩
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs
  simp only [F, M, ite_eq_right hs₁]
  ring

/-- A nonnegative compensated log-ramp tail is absolutely Mellin integrable at each
real `r > 1/2`, assuming nonvanishing of zeta only on the real interval `(1/2, 1)`. -/
public theorem compensated_vonMangoldt_logRamp_mellinTailConverges {K A : ℝ}
    (hK : 0 ≤ K) (hA : 2 ≤ A) :
    let B (x : ℝ) :=
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log (x / n)
    let g (x : ℝ) := K * Real.sqrt x * Real.log x ^ 2 - (B x - x)
    (∀ x > A, 0 ≤ g x) →
      (∀ σ : ℝ, 1 / 2 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) →
      ∀ r : ℝ, 1 / 2 < r → Masullo.MellinTailConverges g A r := by
  intro B g hg₀ hζ r hr
  let μ := volume.restrict (Ioi A)
  have hx : ∀ᵐ x ∂μ, 1 ≤ x := (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦
    (show 1 ≤ A by linarith).trans (mem_Ioi.mp hx).le
  -- Start with independently proved integrability on the right of `1`.
  have hright₁ (t : ℝ) (ht : 1 < t) : Masullo.MellinTailConverges g A t := by
    have hi := (compensated_vonMangoldt_logRamp_mellin hK hA
      (s := (t : ℂ)) (by simpa only [ofReal_re] using ht)).1
    change Integrable (fun x : ℝ ↦ (g x : ℂ) * (x : ℂ) ^ (-((t : ℂ) + 1))) μ at hi
    refine (Complex.reCLM.integrable_comp hi).congr (hx.mono fun x hx ↦ ?_)
    change Complex.reCLM ((g x : ℂ) * (x : ℂ) ^ (-((t : ℂ) + 1))) = g x * x ^ (-(t + 1))
    rw [← ofReal_one, ← ofReal_add, ← ofReal_neg, ← Complex.ofReal_cpow (zero_le_one.trans hx),
      ← ofReal_mul, Complex.reCLM_apply, ofReal_re]
  have hg : AEMeasurable g μ := by
    have h2 : Integrable (fun x : ℝ ↦ g x * x ^ (-(2 + 1 : ℝ))) μ :=
      hright₁ 2 (by norm_num)
    have hw : Measurable (fun x : ℝ ↦ x ^ (-(2 + 1 : ℝ))) := measurable_id.pow_const _
    refine (h2.aemeasurable.div hw.aemeasurable).congr (hx.mono fun x hx ↦ ?_)
    change g x * x ^ (-(2 + 1 : ℝ)) / x ^ (-(2 + 1 : ℝ)) = g x
    exact mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _).ne'
  have hmono {a b : ℝ} (hab : a ≤ b) (ha : Masullo.MellinTailConverges g A a) :
      Masullo.MellinTailConverges g A b := by
    refine (show Integrable (fun x ↦ g x * x ^ (-(a + 1))) μ from ha).norm.mono'
      (hg.mul (measurable_id.pow_const _).aemeasurable).aestronglyMeasurable
      (hx.mono fun x hx ↦ ?_)
    simp only [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
      (norm_nonneg _)
  -- A failure of convergence would force a finite abscissa above `1/2`.
  by_contra hfail
  let C := {t : ℝ | Masullo.MellinTailConverges g A t}
  let α := sInf C
  have hne : C.Nonempty := ⟨2, hright₁ 2 (by norm_num)⟩
  have hlower : ∀ t ∈ C, r ≤ t := fun t ht ↦ le_of_not_gt fun h ↦ hfail (hmono h.le ht)
  have hbdd : BddBelow C := ⟨r, hlower⟩
  have hα : 1 / 2 < α := hr.trans_le (le_csInf hne hlower)
  have hright (t : ℝ) (ht : α < t) : Masullo.MellinTailConverges g A t := by
    obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt hne ht
    exact hmono hut.le hu
  have hleft (t : ℝ) (ht : t < α) : ¬ Masullo.MellinTailConverges g A t :=
    fun h ↦ ht.not_ge (csInf_le hbdd h)
  have htail := analyticOnNhd_mellinTail_of_converges hA hg hright
  let J (s : ℂ) := ∫ x in (1 : ℝ)..A, (g x : ℂ) * (x : ℂ) ^ (-(s + 1))
  have hJ : AnalyticOnNhd ℂ J univ :=
    analyticOnNhd_compensated_vonMangoldt_logRamp_initial (K := K) hA
  obtain ⟨F, hF_real, hF_formula⟩ := exists_realRay_compensatedFormula K hJ hζ
  have hF_right (s : ℂ) (hs : 1 < s.re) : F s = Masullo.nonnegativeMellinTail g A s := by
    rw [hF_formula s hs]
    exact (compensated_vonMangoldt_logRamp_mellin hK hA hs).2.symm
  have hFα := hF_real α hα
  -- Join the convergent-side part of a disk at the abscissa to the real ray.
  -- This uses no nonvanishing at nonreal points outside that small disk.
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hFα.eventually_analyticAt
  let U : Set ℂ := Complex.ofReal '' Ioi α
  let V : Set ℂ := Metric.ball (α : ℂ) ε ∩ {s | α < s.re}
  have hU : IsPreconnected U := isPreconnected_Ioi.image _ Complex.continuous_ofReal.continuousOn
  have hV : IsPreconnected V := ((convex_ball _ _).inter (convex_halfSpace_re_gt _)).isPreconnected
  have hmeet : ((α + ε / 2 : ℝ) : ℂ) ∈ U ∩ V := by
    have hαε : α < α + ε / 2 := by linarith
    refine ⟨⟨_, hαε, rfl⟩, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real,
        show α + ε / 2 - α = ε / 2 by ring, Real.norm_of_nonneg (by positivity)]
      linarith
    · change α < ((α + ε / 2 : ℝ) : ℂ).re
      rwa [ofReal_re]
  have hU_right : U ⊆ {s | α < s.re} := by
    rintro _ ⟨t, ht, rfl⟩
    change α < (t : ℂ).re
    rwa [ofReal_re]
  have hFU : AnalyticOnNhd ℂ F (U ∪ V) := by
    rintro s (hs | hs)
    · rcases hs with ⟨t, ht, rfl⟩
      exact hF_real t (hα.trans ht)
    · exact hball (Metric.mem_ball.mp hs.1)
  have hseed : ((α + 2 : ℝ) : ℂ) ∈ U ∪ V :=
    Or.inl ⟨_, by change α < α + 2; linarith, rfl⟩
  have heq := hFU.eqOn_of_preconnected_of_eventuallyEq
    (htail.mono (union_subset hU_right inter_subset_right))
    (hU.union _ hmeet.1 hmeet.2 hV) hseed (by
      have hnhds : ∀ᶠ s : ℂ in 𝓝 ((α + 2 : ℝ) : ℂ), 1 < s.re :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
          change 1 < α + 2
          linarith)
      exact hnhds.mono hF_right)
  refine Masullo.nonnegativeMellinTail_no_analytic_extension hA hg
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hg₀ x hx)
    hright hleft hFα ?_
  have hnear : ∀ᶠ s in 𝓝 (α : ℂ), s ∈ Metric.ball (α : ℂ) ε := Metric.ball_mem_nhds _ hε
  exact hnear.mono fun s hs hsα ↦ heq (Or.inr ⟨hs, hsα⟩)

end PrimeSquareRamp
