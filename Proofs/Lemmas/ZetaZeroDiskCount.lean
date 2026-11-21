module

public import Lemmas.ZetaZeroOrders
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lemmas.CompletedZetaGrowth
import Mathlib.Analysis.Complex.JensenFormula

/-!
# A multiplicity-weighted disk count for the rational zeros

This project estimate supports absolute summability for the multiplicities
in Masullo's (B.4.2.2), p. 614. It does not use the asymptotic residue formula.
-/

open Complex MeromorphicOn Metric Set
open scoped BigOperators

namespace Masullo

private theorem sum_zetaZeroOrder_le_divisor (r : ℝ)
    (A : Finset criticalStripZetaZeros) (hA : ∀ ρ ∈ A, ‖(ρ : ℂ) - 1‖ ≤ r) :
    (∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ)) ≤
      ((∑ᶠ z, divisor entireZeta (closedBall (1 : ℂ) r) z : ℤ) : ℝ) := by
  classical
  let D := divisor entireZeta (closedBall (1 : ℂ) r)
  let B := A.map (Function.Embedding.subtype _)
  have hs := D.finiteSupport (isCompact_closedBall (1 : ℂ) r)
  let U := B ∪ hs.toFinset
  have hsum : ∑ᶠ z, D z = ∑ z ∈ U, D z :=
    finsum_eq_sum_of_support_subset _ fun _ hz ↦
      Finset.subset_union_right (hs.mem_toFinset.mpr hz)
  have hD : 0 ≤ D :=
    (entireZeta_analyticOnNhd.mono (subset_univ (closedBall (1 : ℂ) r))).divisor_nonneg
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
  exact (sum_zetaZeroOrder_le_divisor r A hA).trans hj

end Masullo
