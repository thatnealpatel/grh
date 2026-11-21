module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Logarithmic derivatives on a zero-free disk

Normalize a holomorphic logarithm at the center, bound its real part by a
logarithmic modulus ratio, and use Borel–Carathéodory and Cauchy's estimate.
-/

open Complex Filter Metric Set
open scoped Topology

namespace Masullo

private theorem analytic_log_lift {U : Set ℂ} {g : ℂ → ℂ} (hU : IsOpen U)
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

/-- Cauchy's estimate for the logarithmic derivative of a zero-free analytic
function on the disk of radius five, in terms of its upper modulus bound and
its modulus at the center. The estimate includes the radius-three boundary. -/
public theorem norm_logDeriv_le_on_inner_ball {g : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball c 5)) (hn : ∀ z ∈ ball c 5, g z ≠ 0)
    (hM : ∀ z ∈ ball c 5, ‖g z‖ ≤ M) {z : ℂ} (hz : z ∈ closedBall c 3) :
    ‖logDeriv g z‖ ≤ 8 * (Real.log (M / ‖g c‖) + 1) := by
  have hc : c ∈ ball c 5 := mem_ball_self (by norm_num)
  have hgc : 0 < ‖g c‖ := norm_pos_iff.mpr (hn c hc)
  let B := Real.log (M / ‖g c‖) + 1
  have hB : 0 < B := by
    have := Real.log_nonneg ((one_le_div hgc).mpr (hM c hc))
    dsimp [B]
    linarith
  have hsc : IsSimplyConnected (ball c (5 : ℝ)) := by
    let := Metric.contractibleSpace_ball (x := c) (by norm_num : (0 : ℝ) < 5)
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hL, hexp⟩ := exists_continuousOn_eqOn_exp_comp hsc isOpen_ball hg.continuousOn
    (by rintro ⟨w, hw, hgw⟩; exact hn w hw hgw)
  let H (w : ℂ) := L w - L c
  have hH : AnalyticOnNhd ℂ H (ball c 5) := fun w hw ↦
    (analytic_log_lift isOpen_ball hg hL hexp w hw).sub analyticAt_const
  have hE (w : ℂ) (hw : w ∈ ball c 5) : exp (H w) = g w / g c := by
    change exp (L w - L c) = _
    rw [exp_sub, ← hexp hw, ← hexp hc]; rfl
  have hRe (w : ℂ) (hw : w ∈ ball c 5) : (H w).re ≤ B := by
    have he := congrArg norm (hE w hw)
    rw [norm_exp, norm_div] at he
    have hlog := Real.log_le_log (div_pos (norm_pos_iff.mpr (hn w hw)) hgc)
      (div_le_div_of_nonneg_right (hM w hw) hgc.le)
    rw [← he, Real.log_exp] at hlog
    exact hlog.trans (by dsimp [B]; linarith)
  -- Translate the center to zero for Borel–Carathéodory.
  let F (w : ℂ) := H (w + c)
  have htrans (w : ℂ) (hw : w ∈ ball (0 : ℂ) 5) : w + c ∈ ball c 5 := by
    simpa [mem_ball, dist_eq_norm] using hw
  have hdF : DifferentiableOn ℂ F (ball 0 5) := by
    intro w hw
    have hwc : DifferentiableAt ℂ (fun u : ℂ ↦ u + c) w := by fun_prop
    exact ((hH (w + c) (htrans w hw)).differentiableAt.comp w hwc).differentiableWithinAt
  have h4 (w : ℂ) (hw : w ∈ closedBall c 4) : ‖H w‖ ≤ 8 * B := by
    have hq : ‖w - c‖ ≤ 4 := by simpa [dist_eq_norm] using hw
    have hq' : w - c ∈ ball (0 : ℂ) 5 := mem_ball_zero_iff.mpr (by linarith)
    have hb := borelCaratheodory_zero hB hdF (fun u hu ↦ hRe (u + c) (htrans u hu))
      (by norm_num) hq' (by simp [F, H])
    simp only [F, sub_add_cancel] at hb
    refine hb.trans ?_
    apply (div_le_iff₀ (by linarith : 0 < 5 - ‖w - c‖)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hq hB.le]
  -- The unit disk about z fits in the closed radius-four disk.
  have hsub : closedBall z 1 ⊆ closedBall c 4 := by
    intro w hw
    exact mem_closedBall.mpr (by
      linarith [dist_triangle w z c, mem_closedBall.mp hw, mem_closedBall.mp hz])
  have h45 : closedBall c 4 ⊆ ball c 5 := closedBall_subset_ball (by norm_num)
  have hdiff : DiffContOnCl ℂ H (ball z 1) :=
    ⟨hH.differentiableOn.mono (ball_subset_closedBall.trans (hsub.trans h45)), by
      rw [closure_ball _ (by norm_num)]
      exact hH.continuousOn.mono (hsub.trans h45)⟩
  have hCauchy := norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1)
    hdiff (fun w hw ↦ h4 w (hsub (sphere_subset_closedBall hw)))
  have hz' : z ∈ ball c 5 := closedBall_subset_ball (by norm_num) hz
  have hd := (((hH z hz').differentiableAt.hasDerivAt.cexp).mul_const (g c)).congr_of_eventuallyEq
    (f₁ := g) (by
      filter_upwards [isOpen_ball.mem_nhds hz'] with w hw
      rw [hE w hw, div_mul_cancel₀ _ (hn c hc)])
  have hide : logDeriv g z = deriv H z := by
    rw [logDeriv_apply, hd.deriv, hE z hz']
    field_simp [hn z hz', hn c hc]
  simpa only [hide, div_one] using hCauchy

end Masullo
