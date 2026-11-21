module

public import Lemmas.ZetaZeroOrders
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lemmas.CompletedZetaGrowth
import Lemmas.ZetaContourAnchor
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A multiplicity-weighted disk count for the rational zeros

This project estimate supports absolute summability for the multiplicities
in Masullo's (B.4.2.2), p. 614. The moving-disk estimate supplies a local
count for a replacement of the growth argument cited via Lang in (B.4.2.1).
Neither estimate uses the asymptotic residue formula.
-/

open Complex MeromorphicOn Metric Set
open scoped BigOperators

namespace Masullo

private theorem sum_zetaZeroOrder_le_divisor (c : ℂ) (r : ℝ)
    (A : Finset criticalStripZetaZeros) (hA : ∀ ρ ∈ A, ‖(ρ : ℂ) - c‖ ≤ r) :
    (∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ)) ≤
      ((∑ᶠ z, divisor entireZeta (closedBall c r) z : ℤ) : ℝ) := by
  classical
  let D := divisor entireZeta (closedBall c r)
  let B := A.map (Function.Embedding.subtype _)
  have hs := D.finiteSupport (isCompact_closedBall c r)
  let U := B ∪ hs.toFinset
  have hsum : ∑ᶠ z, D z = ∑ z ∈ U, D z :=
    finsum_eq_sum_of_support_subset _ fun _ hz ↦
      Finset.subset_union_right (hs.mem_toFinset.mpr hz)
  have hD : 0 ≤ D :=
    (entireZeta_analyticOnNhd.mono (subset_univ (closedBall c r))).divisor_nonneg
  have hcount : (∑ ρ ∈ A, (zetaZeroOrder ρ : ℤ)) ≤ ∑ᶠ z, D z := by
    calc
      _ = ∑ z ∈ B, D z := by
        dsimp only [B]
        rw [Finset.sum_map]
        exact Finset.sum_congr rfl fun ρ hρ ↦
          (divisor_entireZeta_apply ρ (by simpa [dist_eq_norm] using hA ρ hρ)).symm
      _ ≤ ∑ z ∈ U, D z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ ↦ hD z)
      _ = _ := hsum.symm
  exact_mod_cast hcount

/-- Jensen at center `1`, with inner radius `R` and outer radius `2R`, bounds
any finite subset of the closed inner disk, with its actual zeta orders. -/
public theorem sum_zetaZeroOrder_le_jensen :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (R : ℕ), 1 ≤ R → ∀ A : Finset criticalStripZetaZeros,
      (∀ ρ ∈ A, ‖(ρ : ℂ) - 1‖ ≤ (R : ℝ)) →
      (∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ)) ≤
        Real.log (1 + ((2 * R + 1 : ℕ) : ℝ) * (2 * (R : ℝ)) *
          (C * (((2 * R + 1).factorial : ℕ) : ℝ))) / Real.log 2 := by
  obtain ⟨C, hC, hgrowth⟩ := completedZeta₀_factorial_growth
  refine ⟨C, hC, fun R hR A hA ↦ ?_⟩
  let n : ℕ := 2 * R + 1
  let r : ℝ := R
  let M : ℝ := 1 + (n : ℝ) * (2 * r) * (C * (n.factorial : ℝ))
  have hr : 0 < r := by
    change 0 < (R : ℝ)
    exact_mod_cast (show 0 < R by omega)
  have hr' : 0 < 2 * r := by positivity
  have hn : (n : ℝ) = 2 * r + 1 := by push_cast [n, r]; rfl
  have hC₀ : 0 ≤ C := by linarith
  have hM : 1 ≤ M := le_add_of_nonneg_right (by positivity)
  have hbound : ∀ z ∈ sphere (1 : ℂ) |2 * r|, ‖entireZeta z‖ ≤ M := by
    intro z hz
    have hz₁ : ‖z - 1‖ = 2 * r := by simpa [dist_eq_norm, abs_of_pos hr'] using hz
    have hz₀ : ‖z‖ ≤ (n : ℝ) := by
      calc
        ‖z‖ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := by simpa using norm_add_le (z - 1) (1 : ℂ)
        _ = (n : ℝ) := by rw [hz₁, norm_one, hn]
    calc
      ‖entireZeta z‖ ≤ 1 + ‖z‖ * ‖z - 1‖ * ‖completedRiemannZeta₀ z‖ := by
        simpa [entireZeta, norm_mul] using
          norm_add_le (1 : ℂ) (z * (z - 1) * completedRiemannZeta₀ z)
      _ ≤ M := by
        rw [hz₁]
        dsimp [M]
        gcongr
        exact hgrowth n z ((Complex.abs_re_le_norm z).trans hz₀)
  have hj := AnalyticOnNhd.sum_divisor_le (f := entireZeta) (c := 1)
    (r := r) (R := 2 * r) (by simpa [abs_of_pos hr] using hr)
    (by rw [abs_of_pos hr, abs_of_pos hr']; linarith) hM
    (entireZeta_analyticOnNhd.mono (subset_univ _)) (by simp) hbound
  have hratio : 2 * r / r = 2 := mul_div_cancel_right₀ _ hr.ne'
  rw [abs_of_pos hr, hratio, entireZeta_one, norm_one, div_one] at hj
  exact (sum_zetaZeroOrder_le_divisor 1 r A hA).trans hj

/-- On the fixed outer circle about `2 + it`, the entire numerator grows
at most quadratically, uniformly in the height. -/
public theorem entireZeta_moving_circle_upper_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t : ℝ) (s : ℂ), s ∈ sphere (2 + (t : ℂ) * I) 6 →
      ‖entireZeta s‖ ≤ C * (1 + |t|) ^ 2 := by
  obtain ⟨C, hC, hgrowth⟩ := completedZeta₀_factorial_growth
  let D : ℝ := C * ((8 : ℕ).factorial : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + 72 * D, by linarith, fun t s hs ↦ ?_⟩
  let c : ℂ := 2 + (t : ℂ) * I
  have hsc : ‖s - c‖ = 6 := by simpa [c, dist_eq_norm] using hs
  have hcRe : c.re = 2 := by simp [c]
  have hsRe : |s.re| ≤ (8 : ℕ) := by
    calc
      |s.re| = |(s - c).re + c.re| := by rw [sub_re, sub_add_cancel]
      _ ≤ |(s - c).re| + |c.re| := abs_add_le ..
      _ ≤ (8 : ℕ) := by
        have h := Complex.abs_re_le_norm (s - c)
        rw [hsc] at h
        rw [hcRe]
        norm_num at h ⊢
        linarith
  have hc : ‖c‖ ≤ 2 + |t| := by
    simpa [c, norm_mul] using norm_add_le (2 : ℂ) ((t : ℂ) * I)
  have hs₀ : ‖s‖ ≤ 8 + |t| := by
    have h := norm_add_le (s - c) c
    rw [sub_add_cancel, hsc] at h
    linarith
  have hs₁ : ‖s - 1‖ ≤ 9 + |t| := by
    have h := norm_sub_le s (1 : ℂ)
    rw [norm_one] at h
    linarith
  have ht := abs_nonneg t
  calc
    ‖entireZeta s‖ ≤ 1 + ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ := by
      simpa [entireZeta, norm_mul] using
        norm_add_le (1 : ℂ) (s * (s - 1) * completedRiemannZeta₀ s)
    _ ≤ 1 + (8 * (1 + |t|)) * (9 * (1 + |t|)) * D := by
      gcongr
      · linarith
      · linarith
      · exact hgrowth 8 s hsRe
    _ ≤ (1 + 72 * D) * (1 + |t|) ^ 2 := by
      have h : 1 ≤ (1 + |t|) ^ 2 := by nlinarith
      linear_combination h

/-- Jensen's inequality on radii `5` and `6` bounds the full multiplicity
in the inner disk about `2 + it` by a uniform constant times `1 + |t|`. -/
public theorem sum_zetaZeroOrder_le_moving_disk :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ), 1 ≤ |t| → ∀ A : Finset criticalStripZetaZeros,
      (∀ ρ ∈ A, ‖(ρ : ℂ) - (2 + (t : ℂ) * I)‖ ≤ 5) →
      (∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ)) ≤ K * (1 + |t|) := by
  obtain ⟨C, hC, hbound⟩ := entireZeta_moving_circle_upper_bound
  let B : ℝ := Real.log C + Real.log (3 * Real.pi) + 2 + Real.pi / 4
  have hB : 0 < B := by
    have hp : 1 ≤ 3 * Real.pi := by linarith [Real.pi_gt_three]
    have hC' := Real.log_nonneg hC
    have hp' := Real.log_nonneg hp
    dsimp [B]
    linarith [Real.pi_pos]
  have hlog : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨B / Real.log (6 / 5 : ℝ), by positivity, fun t ht A hA ↦ ?_⟩
  let c : ℂ := 2 + (t : ℂ) * I
  let u : ℝ := 1 + |t|
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hu₀ : 0 < u := by linarith
  let M : ℝ := C * u ^ 2
  have hM : 1 ≤ M := by
    have h : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
    exact one_le_mul_of_one_le_of_one_le hC h
  have ha := entireZeta_right_anchor_lower_bound t ht
  change (3 * Real.pi)⁻¹ * Real.exp (-(Real.pi * |t| / 4)) ≤ ‖entireZeta c‖ at ha
  have hpi : 0 < 3 * Real.pi := by positivity
  have hpos : 0 < (3 * Real.pi)⁻¹ * Real.exp (-(Real.pi * |t| / 4)) := by positivity
  have hf : 0 < ‖entireZeta c‖ := hpos.trans_le ha
  have hj := AnalyticOnNhd.sum_divisor_le (f := entireZeta) (c := c)
    (r := 5) (R := 6) (by norm_num) (by norm_num) hM
    (entireZeta_analyticOnNhd.mono (subset_univ _)) (norm_pos_iff.mp hf)
    (by simpa using hbound t)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at hj
  have hlogf : -Real.log ‖entireZeta c‖ ≤ Real.log (3 * Real.pi) + Real.pi * |t| / 4 := by
    have h := Real.log_le_log hpos ha
    rw [Real.log_mul (inv_ne_zero hpi.ne') (Real.exp_ne_zero _), Real.log_inv, Real.log_exp] at h
    linarith
  have hlogu : Real.log u ≤ |t| := by simpa [u] using Real.log_le_sub_one_of_pos hu₀
  have hnum : Real.log (M / ‖entireZeta c‖) ≤ B * u := by
    rw [Real.log_div (by linarith : M ≠ 0) hf.ne']
    dsimp only [M]
    rw [Real.log_mul (by linarith : C ≠ 0) (pow_ne_zero _ hu₀.ne'), Real.log_pow]
    push_cast
    calc
      _ ≤ Real.log C + Real.log (3 * Real.pi) + (2 + Real.pi / 4) * |t| := by
        linarith
      _ ≤ B * u := by
        have hc' := Real.log_nonneg hC
        have hp' : 0 ≤ Real.log (3 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
        dsimp [B, u]
        nlinarith [mul_nonneg hc' (abs_nonneg t), mul_nonneg hp' (abs_nonneg t), Real.pi_pos]
  calc
    _ ≤ Real.log (M / ‖entireZeta c‖) / Real.log (6 / 5 : ℝ) :=
      (sum_zetaZeroOrder_le_divisor c 5 A hA).trans hj
    _ ≤ _ := by rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hnum hlog.le

end Masullo
