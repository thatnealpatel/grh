module

public import Props.ZetaContourDisk
public import Mathlib.Analysis.Calculus.LogDeriv
import Lemmas.ZeroFreeDiskLogDeriv
import Lemmas.ZetaContourAnchor

/-!
# Local logarithmic derivative bound for Appendix B

For (B.4.2.1), p. 614, Masullo invokes Lang for completed
logarithmic-derivative estimates. Lang uses a global product comparison.
The rational replacement here uses the finite disk factorization, bounds
the logarithmic derivative of its zero-free quotient by
`norm_logDeriv_le_on_inner_ball`, and estimates the removed factors by
their full orders divided by the distance from the zeros.
-/

open Complex Metric Set

namespace Masullo

/-- A uniform estimate in the radius-three disk about `2 + it`, away from
all open-strip zeros by at least `δ`. This estimates the entire numerator;
the rational pole-clearing factors are not included in its derivative. -/
public theorem entireZeta_logDeriv_le_moving_disk :
    ∃ D K : ℝ, 0 < D ∧ 0 < K ∧ ∀ (t : ℝ), 1 ≤ |t| →
      ∀ z ∈ closedBall (2 + (t : ℂ) * I) 3, ∀ δ : ℝ, 0 < δ →
        (∀ ρ : criticalStripZetaZeros, δ ≤ ‖z - (ρ : ℂ)‖) →
        ‖logDeriv entireZeta z‖ ≤ D * (1 + |t|) + K * (1 + |t|) / δ := by
  classical
  obtain ⟨C, K, hC, hK, hfac⟩ := entireZeta_moving_disk_factorization
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  let D : ℝ := 8 * (C + 3 * Real.pi + (2 + Real.pi / 4 + K * Real.log 5))
  refine ⟨D, K, by dsimp [D]; positivity, hK, fun t ht z hz δ hδ hsep ↦ ?_⟩
  let c : ℂ := 2 + (t : ℂ) * I
  obtain ⟨A, g, _, hg, hprod, hgn, hgm, hcenter, hcount⟩ := hfac t ht
  let N : ℕ := ∑ ρ ∈ A, zetaZeroOrder ρ
  let M : ℝ := C * (1 + |t|) ^ 2
  have hc : c ∈ closedBall c 5 := mem_closedBall_self (by norm_num)
  have hgcp : 0 < ‖g c‖ := norm_pos_iff.mpr (hgn c hc)
  have hfcp : 0 < ‖entireZeta c‖ := by
    exact (by positivity : 0 < (3 * Real.pi)⁻¹ * Real.exp (-(Real.pi * |t| / 4))).trans_le
      (entireZeta_right_anchor_lower_bound t ht)
  have hMp : 0 < M := by dsimp [M]; positivity
  have h3pi : 0 < 3 * Real.pi := by positivity
  -- The cost at the center is the anchor loss plus N log 5.
  have hlogc := Real.log_le_log hfcp hcenter
  rw [Real.log_mul (by positivity) hgcp.ne', Real.log_pow] at hlogc
  have ha := Real.log_le_log (by positivity) (entireZeta_right_anchor_lower_bound t ht)
  rw [Real.log_mul (inv_ne_zero h3pi.ne') (Real.exp_ne_zero _), Real.log_inv, Real.log_exp] at ha
  change (∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ)) ≤ K * (1 + |t|) at hcount
  have hN : (N : ℝ) ≤ K * (1 + |t|) := by simpa [N] using hcount
  have hbudget : 8 * (Real.log (M / ‖g c‖) + 1) ≤ D * (1 + |t|) := by
    have hel : Real.log (1 + |t|) ≤ |t| := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |t|)
      linarith
    have hMlog : Real.log M ≤ C - 1 + 2 * |t| := by
      dsimp [M]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < C)]
    have hconst : 0 ≤ C + 3 * Real.pi := by positivity
    rw [Real.log_div hMp.ne' hgcp.ne']
    dsimp [D]
    have hNlog := mul_le_mul_of_nonneg_right hN hlog5
    have hπlog := Real.log_le_sub_one_of_pos h3pi
    have hconst' := mul_nonneg hconst (abs_nonneg t)
    change Real.log ‖entireZeta c‖ ≤ (N : ℝ) * Real.log 5 + Real.log ‖g c‖ at hlogc
    change -Real.log (3 * Real.pi) + -(Real.pi * |t| / 4) ≤ Real.log ‖entireZeta c‖ at ha
    nlinarith only [hMlog, hNlog, hπlog, hconst', ha, hlogc, Real.pi_pos,
      mul_nonneg hK.le hlog5]
  have hsub : ball c 5 ⊆ closedBall c 5 := ball_subset_closedBall
  have hsub' : ball c 5 ⊆ closedBall c 6 :=
    hsub.trans (closedBall_subset_closedBall (by norm_num))
  have hgderiv : ‖logDeriv g z‖ ≤ D * (1 + |t|) :=
    (norm_logDeriv_le_on_inner_ball (hg.mono (subset_univ _))
      (fun w hw ↦ hgn w (hsub hw)) (fun w hw ↦ hgm w (hsub' hw)) hz).trans hbudget
  -- The logarithmic derivative of the removed divisor is a finite sum.
  have hzρ (ρ : criticalStripZetaZeros) : z - (ρ : ℂ) ≠ 0 :=
    norm_pos_iff.mp (hδ.trans_le (hsep ρ))
  have hderiv : logDeriv entireZeta z =
      (∑ ρ ∈ A, (zetaZeroOrder ρ : ℂ) * (1 / (z - (ρ : ℂ)))) + logDeriv g z := by
    rw [show entireZeta = _ from funext hprod, logDeriv_fun_mul]
    · rw [logDeriv_fun_prod]
      · congr 1
        apply Finset.sum_congr rfl
        intro ρ _
        rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
        have hd : deriv (fun w : ℂ ↦ w - (ρ : ℂ)) z = 1 := by simp
        rw [hd]
      · exact fun ρ _ ↦ pow_ne_zero _ (hzρ ρ)
      · intro ρ _
        fun_prop
    · exact Finset.prod_ne_zero_iff.mpr (fun ρ _ ↦ pow_ne_zero _ (hzρ ρ))
    · exact hgn z (closedBall_subset_closedBall (by norm_num) hz)
    · exact DifferentiableAt.fun_finsetProd fun ρ _ ↦ by fun_prop
    · exact (hg z trivial).differentiableAt
  have hs : ‖∑ ρ ∈ A, (zetaZeroOrder ρ : ℂ) * (1 / (z - (ρ : ℂ)))‖ ≤ K * (1 + |t|) / δ := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ) / δ := by
        apply Finset.sum_le_sum
        intro ρ _
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast, mul_one_div]
        exact div_le_div_of_nonneg_left (by positivity) hδ (hsep ρ)
      _ ≤ _ := by rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hcount hδ.le
  rw [hderiv]
  exact (norm_add_le _ _).trans (by linarith)

end Masullo
