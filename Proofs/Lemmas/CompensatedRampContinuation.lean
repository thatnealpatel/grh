module

public import Lemmas.CompensatedRampMellin
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Local continuation of the compensated von Mangoldt ramp

Source: Bob, `5f22f5a60aef:.godel/bob/unsigned-edge-rh.md:24–30` (ramp on line 15),
with the convergent transform from `d54485e6664:Proofs/Lemmas/CompensatedRampMellin.lean`.
Scan pin: `03fd044fb601cbe11dd1ef50a928893a50565845`.
Owning check session: `01a20fbf-64d4-7ae0-ac41-09f991160e63`.

Scope: removal of the apparent pole at `s = 1`, entire dependence of the actual
initial-interval correction, and local continuation of the actual tail from `Re s > 1`.
No sign of the tail, abscissa of convergence, or application of Landau's theorem is asserted.
-/

open Complex Filter MeasureTheory Set
open scoped Asymptotics Topology

namespace PrimeSquareRamp

/-- The sum of the two singular terms in the compensated transform extends analytically
across `1`. Only punctured-neighborhood agreement is asserted, since the expression
using totalized division does not supply its analytic value at `1`. -/
public theorem exists_analyticAt_compensated_zeta_one :
    ∃ P : ℂ → ℂ, AnalyticAt ℂ P 1 ∧
      ∀ᶠ s in 𝓝[≠] (1 : ℂ), P s = logDeriv riemannZeta s / s ^ 2 + 1 / (s - 1) := by
  classical
  let W (s : ℂ) := (s - 1) * riemannZeta s
  -- The residue is 1; the product `(s - 1) * ζ(s)` has totalized value 0 at 1.
  let Z := Function.update W 1 1
  have hZW {s : ℂ} (hs : s ≠ 1) : Z =ᶠ[𝓝 s] W := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    exact Function.update_of_ne ht _ _
  have hd : ∀ᶠ s : ℂ in 𝓝[≠] 1, DifferentiableAt ℂ Z s := by
    rw [eventually_nhdsWithin_iff]
    refine Eventually.of_forall fun s hs ↦ (hZW hs).differentiableAt_iff.mpr ?_
    exact (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
  have hZ : AnalyticAt ℂ Z 1 :=
    analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd
      (continuousAt_update_same.mpr riemannZeta_residue_one)
  have hZ₁ : Z 1 = 1 := Function.update_self ..
  have hZ₀ : Z 1 ≠ 0 := by simp [hZ₁]
  -- In the sum, the residual rational term is `(s + 1) / s ^ 2`.
  let P (s : ℂ) := (logDeriv Z s + (s + 1)) / s ^ 2
  have hid : AnalyticAt ℂ (fun s : ℂ ↦ s) 1 := analyticAt_id
  have hl : AnalyticAt ℂ (logDeriv Z) 1 := hZ.deriv.div hZ hZ₀
  refine ⟨P, (hl.add (hid.add analyticAt_const)).div (hid.pow 2) (by norm_num), ?_⟩
  have hnz : ∀ᶠ s in 𝓝 (1 : ℂ), Z s ≠ 0 :=
    hZ.continuousAt.tendsto.eventually (eventually_ne_nhds hZ₀)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hnz, eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with s hz hs₀ hs₁
  have hs₁' : s ≠ 1 := hs₁
  have hzeta : riemannZeta s ≠ 0 := by
    intro h
    apply hz
    rw [(hZW hs₁').eq_of_nhds]
    simp [W, h]
  have hlog : logDeriv Z s = 1 / (s - 1) + logDeriv riemannZeta s := by
    rw [(logDeriv_congr_nhds (hZW hs₁')).eq_of_nhds]
    have h := logDeriv_fun_mul (f := fun t : ℂ ↦ t - 1) (g := riemannZeta) s
      (sub_ne_zero.mpr hs₁') hzeta (differentiableAt_id.sub_const 1)
      (differentiableAt_riemannZeta hs₁')
    simpa [W, logDeriv_apply, (hasDerivAt_id s |>.sub_const 1).deriv] using h
  dsimp only [P]
  rw [hlog]
  field_simp [hs₀, sub_ne_zero.mpr hs₁']
  ring

/-- The actual bounded initial-interval correction in the compensated transform is
entire in `s`, with the same `x ^ (-(s + 1))` normalization as the tail. -/
public theorem analyticOnNhd_compensated_vonMangoldt_logRamp_initial {K A : ℝ}
    (hA : 2 ≤ A) :
    let B (x : ℝ) :=
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log (x / n)
    let g (x : ℝ) := K * Real.sqrt x * Real.log x ^ 2 - (B x - x)
    AnalyticOnNhd ℂ (fun s : ℂ ↦ ∫ x in (1 : ℝ)..A, (g x : ℂ) * (x : ℂ) ^ (-(s + 1)))
      univ := by
  intro B g
  have hA' : 1 ≤ A := le_trans (by norm_num) hA
  -- Use the absolutely integrable profile at `s = 2` and extend it by zero.
  let w (x : ℝ) := (x : ℂ) ^ (-(2 + 1 : ℂ))
  let m (x : ℝ) := ((K * Real.sqrt x * Real.log x ^ 2 : ℝ) : ℂ)
  let f := (Ioc (1 : ℝ) A).indicator (fun x ↦ (g x : ℂ) * w x)
  have hm : ContinuousOn (fun x ↦ m x * w x) (Icc 1 A) := by
    refine continuousOn_of_forall_continuousAt fun x hx ↦ ?_
    have hx₀ : x ≠ 0 := (zero_lt_one.trans_le hx.1).ne'
    have hlog := Real.continuousAt_log hx₀
    exact (show ContinuousAt m x by unfold m; fun_prop).mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hx₀))
  have hmi : IntegrableOn (fun x ↦ m x * w x) (Ioc 1 A) :=
    (hm.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hri := (vonMangoldt_logRamp_mellin (s := 2) (by norm_num)).1
  change IntegrableOn (fun x ↦ ((B x : ℂ) - (x : ℂ)) * w x) (Ici 1) at hri
  have hfi : Integrable f := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    refine (hmi.sub (hri.mono_set (fun x hx ↦ hx.1.le))).congr_fun ?_ measurableSet_Ioc
    intro x _
    simp only [Pi.sub_apply, g, m, Complex.ofReal_sub]
    ring
  have htop (a : ℝ) : f =O[atTop] (fun x : ℝ ↦ x ^ (-a)) := by
    apply Asymptotics.IsBigO.of_bound 0
    filter_upwards [eventually_gt_atTop A] with x hx
    simp [f, indicator_of_notMem (show x ∉ Ioc 1 A from fun h ↦ hx.not_ge h.2)]
  have hbot (b : ℝ) : f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ ↦ x ^ (-b)) := by
    apply Asymptotics.IsBigO.of_bound 0
    filter_upwards [(eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with x hx
    simp [f, indicator_of_notMem (show x ∉ Ioc 1 A from fun h ↦ hx.not_ge h.1.le)]
  have hdiff : Differentiable ℂ (mellin f) := by
    intro s
    exact mellin_differentiableAt_of_isBigO_rpow (hfi.locallyIntegrable.locallyIntegrableOn _)
      (htop (s.re + 1)) (lt_add_one _) (hbot (s.re - 1)) (sub_lt_self _ zero_lt_one)
  -- The profile already carries `x ^ (-3)`, so the Mellin parameter is `3 - s`.
  have hI (s : ℂ) : (∫ x in (1 : ℝ)..A, (g x : ℂ) * (x : ℂ) ^ (-(s + 1))) =
      mellin f (3 - s) := by
    rw [intervalIntegral.integral_of_le hA', mellin]
    simp_rw [f, ← indicator_smul]
    rw [integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict_of_subset (show Ioc (1 : ℝ) A ⊆ Ioi 0 from
        fun _ hx ↦ zero_lt_one.trans hx.1)]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
    simp only [smul_eq_mul, w]
    rw [← mul_left_comm, ← cpow_add _ _ (ofReal_ne_zero.mpr (zero_lt_one.trans hx.1).ne')]
    congr 2
    ring
  simp_rw [hI]
  intro s _
  have hshift : Differentiable ℂ (fun s : ℂ ↦ 3 - s) := by fun_prop
  exact (hdiff.comp hshift).analyticAt s

/-- For `K ≥ 0` and `A ≥ 2`, the actual absolutely convergent compensated Mellin tail
on `Re s > 1` has an analytic extension to an open disk about `1`. The assertion does
not identify this extension at `1` with the totalized tail integral there. -/
public theorem compensated_vonMangoldt_logRamp_mellin_continuation {K A : ℝ}
    (hK : 0 ≤ K) (hA : 2 ≤ A) :
    let B (x : ℝ) :=
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * Real.log (x / n)
    let g (x : ℝ) := K * Real.sqrt x * Real.log x ^ 2 - (B x - x)
    ∃ r : ℝ, 0 < r ∧ ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (Metric.ball 1 r) ∧
      ∀ s ∈ Metric.ball (1 : ℂ) r, 1 < s.re → H s = Masullo.nonnegativeMellinTail g A s := by
  intro B g
  obtain ⟨P, hP, hagree⟩ := exists_analyticAt_compensated_zeta_one
  let J (s : ℂ) := ∫ x in (1 : ℝ)..A, (g x : ℂ) * (x : ℂ) ^ (-(s + 1))
  let H (s : ℂ) := 2 * (K : ℂ) / (s - 1 / 2) ^ 3 + P s - J s
  have hJ : AnalyticAt ℂ J 1 :=
    analyticOnNhd_compensated_vonMangoldt_logRamp_initial (K := K) hA 1 (mem_univ _)
  have hid : AnalyticAt ℂ (fun s : ℂ ↦ s) 1 := analyticAt_id
  have hm : AnalyticAt ℂ (fun s : ℂ ↦ 2 * (K : ℂ) / (s - 1 / 2) ^ 3) 1 :=
    analyticAt_const.div ((hid.sub analyticAt_const).pow 3) (by norm_num)
  have hH : AnalyticAt ℂ H 1 := (hm.add hP).sub hJ
  have hagree' := eventually_nhdsWithin_iff.mp hagree
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hH.eventually_analyticAt.and hagree')
  refine ⟨r, hr, H, fun s hs ↦ (hball (Metric.mem_ball.mp hs)).1, ?_⟩
  intro s hs hsre
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hsre
  have hp := (hball (Metric.mem_ball.mp hs)).2 hs₁
  have ht := (compensated_vonMangoldt_logRamp_mellin hK hA hsre).2
  change Masullo.nonnegativeMellinTail g A s =
    2 * (K : ℂ) / (s - 1 / 2) ^ 3 + logDeriv riemannZeta s / s ^ 2 + 1 / (s - 1) - J s at ht
  rw [ht]
  dsimp only [H]
  rw [hp]
  ring

end PrimeSquareRamp
