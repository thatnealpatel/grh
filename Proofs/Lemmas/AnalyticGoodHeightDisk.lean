module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lemmas.EntireFiniteFactors
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Local disk factorization for choosing good heights

Remove the full orders of the zeros on a closed disk. Jensen bounds their
sum, and the normalized logarithm bounds the loss from the zero-free quotient
on a smaller disk. These estimates are used in the repair of the horizontal
edges for Masullo's inverse-range argument (p. 309, §6.3.2).
-/

open Complex Filter MeromorphicOn Metric Set
open scoped Topology

namespace Masullo

-- As in `Lemmas.ZeroFreeDiskLogDeriv`, the continuous lift is locally a
-- translate of the principal logarithm of the ratio to its value at the center.
private theorem analytic_goodHeight_log_lift {U : Set ℂ} {g : ℂ → ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) {L : ℂ → ℂ} (hL : ContinuousOn L U)
    (hexp : EqOn (exp ∘ L) g U) : AnalyticOnNhd ℂ L U := by
  intro w hw
  have hUₙ : U ∈ 𝓝 w := hU.mem_nhds hw
  have hn : g w ≠ 0 := by rw [← hexp hw]; exact exp_ne_zero _
  have hl : ContinuousAt (fun z ↦ (L z - L w).im) w :=
    continuous_im.continuousAt.comp ((hL.continuousAt hUₙ).sub continuousAt_const)
  have hs : ∀ᶠ z in 𝓝 w, (L z - L w).im ∈ Ioo (-Real.pi) Real.pi :=
    hl.eventually (p := fun y ↦ y ∈ Ioo (-Real.pi) Real.pi) (by
      simp only [sub_self, zero_im]
      exact Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
  have hh : AnalyticAt ℂ (fun z ↦ log (g z / g w)) w :=
    (hg w hw).div_const.clog (by rw [div_self hn]; exact one_mem_slitPlane)
  apply (hh.add (analyticAt_const (v := L w))).congr
  filter_upwards [hs, hUₙ] with z hz hzU
  have he : exp (L z - L w) = g z / g w := by
    rw [exp_sub, ← hexp hzU, ← hexp hw]; rfl
  change log (g z / g w) + L w = L z
  rw [← he, log_exp hz.1 hz.2.le, sub_add_cancel]

private theorem log_norm_lower_on_inner_disk {g : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball c 5)) (hn : ∀ z ∈ ball c 5, g z ≠ 0)
    (hbd : ∀ z ∈ ball c 5, ‖g z‖ ≤ M) {z : ℂ} (hz : z ∈ closedBall c 4) :
    Real.log ‖g c‖ - 8 * (Real.log M - Real.log ‖g c‖ + 1) ≤ Real.log ‖g z‖ := by
  have hc : c ∈ ball c 5 := mem_ball_self (by norm_num)
  have hgc := norm_pos_iff.mpr (hn c hc)
  let B := Real.log M - Real.log ‖g c‖ + 1
  have hB : 0 < B := by
    have hlog := Real.log_le_log hgc (hbd c hc)
    dsimp [B]
    linarith
  have hsc : IsSimplyConnected (ball c (5 : ℝ)) := by
    let := Metric.contractibleSpace_ball (x := c) (by norm_num : (0 : ℝ) < 5)
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hL, hexp⟩ := exists_continuousOn_eqOn_exp_comp hsc isOpen_ball hg.continuousOn
    (by rintro ⟨w, hw, hgw⟩; exact hn w hw hgw)
  let H (w : ℂ) := L w - L c
  have hH : AnalyticOnNhd ℂ H (ball c 5) := fun w hw ↦
    (analytic_goodHeight_log_lift isOpen_ball hg hL hexp w hw).sub analyticAt_const
  have hRe (w : ℂ) (hw : w ∈ ball c 5) :
      (H w).re = Real.log ‖g w‖ - Real.log ‖g c‖ := by
    have hE : exp (H w) = g w / g c := by
      change exp (L w - L c) = _
      rw [exp_sub, ← hexp hw, ← hexp hc]; rfl
    have he := congrArg norm hE
    rw [norm_exp, norm_div] at he
    rw [← Real.log_exp (H w).re, he, Real.log_div (norm_ne_zero_iff.mpr (hn w hw)) hgc.ne']
  have hRe_le (w : ℂ) (hw : w ∈ ball c 5) : (H w).re ≤ B := by
    rw [hRe w hw]
    have hlog := Real.log_le_log (norm_pos_iff.mpr (hn w hw)) (hbd w hw)
    dsimp [B]
    linarith
  -- Borel–Carathéodory is centered at zero.
  let F (w : ℂ) := H (w + c)
  have htrans (w : ℂ) (hw : w ∈ ball (0 : ℂ) 5) : w + c ∈ ball c 5 := by
    simpa [mem_ball, dist_eq_norm] using hw
  have hdF : DifferentiableOn ℂ F (ball 0 5) := by
    intro w hw
    have hwc : DifferentiableAt ℂ (fun u : ℂ ↦ u + c) w := by fun_prop
    exact ((hH (w + c) (htrans w hw)).differentiableAt.comp w hwc).differentiableWithinAt
  have hq : ‖z - c‖ ≤ 4 := by simpa [dist_eq_norm] using hz
  have hq' : z - c ∈ ball (0 : ℂ) 5 := mem_ball_zero_iff.mpr (by linarith)
  have hb := borelCaratheodory_zero hB hdF (fun u hu ↦ hRe_le (u + c) (htrans u hu))
    (by norm_num) hq' (by simp [F, H])
  simp only [F, sub_add_cancel] at hb
  have hnorm : ‖H z‖ ≤ 8 * B := by
    refine hb.trans ?_
    apply (div_le_iff₀ (by linarith : 0 < 5 - ‖z - c‖)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq hB.le]
  have hz' : z ∈ ball c 5 := closedBall_subset_ball (by norm_num) hz
  have hre := (neg_le_abs (H z).re).trans ((abs_re_le_norm (H z)).trans hnorm)
  rw [hRe z hz'] at hre
  exact sub_le_comm.mp (by simpa only [B, neg_sub] using hre :
    Real.log ‖g c‖ - Real.log ‖g z‖ ≤ 8 * (Real.log M - Real.log ‖g c‖ + 1))

/-- Factor out every zero in the closed disk of radius `5`, with its full order.
An upper bound on the radius-`6` circle controls both the sum of the orders
and the lower logarithmic modulus of the quotient on the closed radius-`3` disk. -/
public theorem exists_goodHeight_disk_factorization {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hc : f c ≠ 0) (hM : 1 ≤ M)
    (hbd : ∀ z ∈ Metric.sphere c 6, ‖f z‖ ≤ M) :
    ∃ (A : Finset ℂ) (n : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ z, f z = (∏ ρ ∈ A, (z - ρ) ^ n ρ) * g z) ∧
      (∑ ρ ∈ A, (n ρ : ℝ)) ≤ Real.log (M / ‖f c‖) / Real.log (6 / 5 : ℝ) ∧
      (∀ z ∈ Metric.closedBall c 3, g z ≠ 0 ∧
        Real.log ‖f c‖ - 8 - (8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ))) *
          Real.log (M / ‖f c‖) ≤ Real.log ‖g z‖) := by
  classical
  have htop (z : ℂ) : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial
      (x := c) (by rw [(hf c trivial).analyticOrderAt_eq_zero.mpr hc]; simp)
  let D := divisor f (closedBall c 5)
  let n (z : ℂ) := (analyticOrderAt f z).toNat
  have horder (z : ℂ) : (n z : ℕ∞) = analyticOrderAt f z := ENat.natCast_toNat (htop z)
  have hD (z : ℂ) (hz : z ∈ closedBall c 5) : D z = (n z : ℤ) := by
    rw [show D z = _ from (hf.mono (subset_univ (closedBall c 5))).divisor_apply hz,
      ← horder z]
    simp
  have hfin := D.finiteSupport (isCompact_closedBall c 5)
  let A := hfin.toFinset
  have hA (z : ℂ) : z ∈ A ↔ z ∈ closedBall c 5 ∧ f z = 0 := by
    rw [hfin.mem_toFinset]
    constructor
    · intro hz
      have hz' := D.supportWithinDomain hz
      refine ⟨hz', (hf z trivial).analyticOrderAt_ne_zero.mp ?_⟩
      have hne : D z ≠ 0 := hz
      rw [hD z hz'] at hne
      rw [← horder z]
      simpa using hne
    · rintro ⟨hz, hfz⟩
      change D z ≠ 0
      have hne := (hf z trivial).analyticOrderAt_ne_zero.mpr hfz
      rw [← horder z] at hne
      rw [hD z hz]
      simpa using hne
  have hdist (ρ : ℂ) (hρ : ρ ∈ A) : ‖ρ - c‖ ≤ 5 := by
    simpa [dist_eq_norm] using ((hA ρ).mp hρ).1
  let N : ℕ := ∑ ρ ∈ A, n ρ
  have hsum : (N : ℝ) = ∑ ρ ∈ A, (n ρ : ℝ) := by simp [N]
  have hcount : (N : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log (6 / 5 : ℝ) := by
    have hj := AnalyticOnNhd.sum_divisor_le (f := f) (c := c) (r := 5) (R := 6)
      (by norm_num) (by norm_num) hM (hf.mono (subset_univ _)) hc (by simpa using hbd)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at hj
    have hsumD : (∑ᶠ ρ, D ρ) = (N : ℤ) := by
      rw [finsum_eq_sum_of_support_subset _ (fun _ hρ ↦ hfin.mem_toFinset.mpr hρ)]
      push_cast [N]
      exact Finset.sum_congr rfl fun ρ hρ ↦ hD ρ ((hA ρ).mp hρ).1
    change ((∑ᶠ ρ, D ρ : ℤ) : ℝ) ≤ _ at hj
    simpa only [hsumD, Int.cast_natCast] using hj
  obtain ⟨g, hg, hgn, hfac⟩ := entire_extract_finset_factors hf A n fun ρ _ ↦ (horder ρ).symm
  have hn (z : ℂ) (hz : z ∈ closedBall c 5) : g z ≠ 0 := by
    intro hgz
    have hfz : f z = 0 := by rw [hfac z, hgz, mul_zero]
    exact hgn z ((hA z).mpr ⟨hz, hfz⟩) hgz
  have hgbd (z : ℂ) (hz : z ∈ closedBall c 6) : ‖g z‖ ≤ M := by
    have hdiff : Differentiable ℂ g := fun w ↦ (hg w trivial).differentiableAt
    have hcircle : ∀ w ∈ frontier (ball c 6), ‖g w‖ ≤ M := by
      rw [frontier_ball _ (by norm_num)]
      intro w hw
      have hw' : ‖w - c‖ = 6 := by simpa [dist_eq_norm] using hw
      have hp : 1 ≤ ∏ ρ ∈ A, ‖w - ρ‖ ^ n ρ := by
        apply Finset.one_le_prod₀
        intro ρ hρ
        have h := norm_add_le (w - ρ) (ρ - c)
        rw [sub_add_sub_cancel, hw'] at h
        exact one_le_pow₀ (by linarith [hdist ρ hρ])
      have h := hbd w hw
      rw [hfac w, norm_mul, norm_prod] at h
      simp only [norm_pow] at h
      exact (le_mul_of_one_le_left (norm_nonneg _) hp).trans h
    rw [← closure_ball c (by norm_num : (6 : ℝ) ≠ 0)] at hz
    exact norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff.diffContOnCl hcircle hz
  have hcenter : ‖f c‖ ≤ (5 : ℝ) ^ N * ‖g c‖ := by
    rw [hfac c, norm_mul, norm_prod]
    simp only [norm_pow]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [show N = ∑ ρ ∈ A, n ρ from rfl, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
    intro ρ hρ
    rw [norm_sub_rev]
    gcongr
    exact hdist ρ hρ
  have hgc := norm_pos_iff.mpr (hn c (mem_closedBall_self (by norm_num)))
  have hfpos := norm_pos_iff.mpr hc
  have hlogCenter : Real.log ‖f c‖ ≤ (N : ℝ) * Real.log 5 + Real.log ‖g c‖ := by
    have hlog := Real.log_le_log hfpos hcenter
    rwa [Real.log_mul (by positivity) hgc.ne', Real.log_pow] at hlog
  have hMpos : 0 < M := by linarith
  have hlogRatio : Real.log (M / ‖f c‖) = Real.log M - Real.log ‖f c‖ :=
    Real.log_div hMpos.ne' hfpos.ne'
  refine ⟨A, n, g, hfac, hsum ▸ hcount, fun z hz ↦ ⟨?_, ?_⟩⟩
  · exact hn z (closedBall_subset_closedBall (by norm_num) hz)
  · have hlower := log_norm_lower_on_inner_disk (hg.mono (subset_univ _))
      (fun w hw ↦ hn w (ball_subset_closedBall hw))
      (fun w hw ↦ hgbd w (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hw)))
      (closedBall_subset_closedBall (by norm_num : (3 : ℝ) ≤ 4) hz)
    have hcost := mul_le_mul_of_nonneg_right hcount (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5))
    have hcost' : (N : ℝ) * Real.log 5 ≤
        (Real.log 5 / Real.log (6 / 5 : ℝ)) * Real.log (M / ‖f c‖) := by
      rw [div_mul_eq_mul_div, mul_comm (Real.log 5), ← div_mul_eq_mul_div]
      exact hcost
    rw [hlogRatio] at hcost' ⊢
    linarith

end Masullo
