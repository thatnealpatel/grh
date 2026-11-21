module

public import Lemmas.ZetaZeroDiskCount
import Lemmas.CompletedZetaOrders
import Lemmas.EntireFiniteFactors
import Lemmas.RationalCompletedZetaZeros
import Mathlib.Analysis.Complex.AbsMax

/-!
# The zero-free factor on the contour disk

Masullo invokes Lang for growth of the completed logarithmic derivative in
(B.4.2.1), p. 614. Lang compares logarithmic derivatives via a global product.
Here we prepare a local replacement: Divide out the full divisor of the
closed inner disk, and control the quotient by the existing circle and count
estimates. This does not yet bound the logarithmic derivative.
-/

open Complex Metric Set

namespace Masullo

private theorem entireZeta_zero_iff {z : ℂ} :
    entireZeta z = 0 ↔ z ∈ criticalStripZetaZeros := by
  rcases eq_or_ne z 0 with rfl | h₀
  · simp [entireZeta, mem_criticalStripZetaZeros]
  rcases eq_or_ne z 1 with rfl | h₁
  · simp [mem_criticalStripZetaZeros]
  rw [← completedZeta_eq_zero_iff_mem_criticalStripZetaZeros h₀ h₁,
    completedZeta_eq_quotient h₀ h₁]
  simp [div_eq_zero_iff, h₀, sub_ne_zero.mpr h₁]

/-- On the radius-five disk about `2 + it`, remove precisely the zeros in the
closed disk, with their full orders. The entire quotient is zero-free on that
closed disk, retains an upper bound out to radius six, and loses at most `5^N`
in modulus at the center, where `N` is the total order removed. -/
public theorem entireZeta_moving_disk_factorization :
    ∃ C K : ℝ, 1 ≤ C ∧ 0 < K ∧ ∀ (t : ℝ), 1 ≤ |t| →
      let c : ℂ := 2 + (t : ℂ) * I
      ∃ (A : Finset criticalStripZetaZeros) (g : ℂ → ℂ),
        (∀ ρ : criticalStripZetaZeros, ρ ∈ A ↔ (ρ : ℂ) ∈ closedBall c 5) ∧
        AnalyticOnNhd ℂ g univ ∧
        (∀ z, entireZeta z = (∏ ρ ∈ A, (z - (ρ : ℂ)) ^ zetaZeroOrder ρ) * g z) ∧
        (∀ z ∈ closedBall c 5, g z ≠ 0) ∧
        (∀ z ∈ closedBall c 6, ‖g z‖ ≤ C * (1 + |t|) ^ 2) ∧
        ‖entireZeta c‖ ≤ (5 : ℝ) ^ (∑ ρ ∈ A, zetaZeroOrder ρ) * ‖g c‖ ∧
        (∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ)) ≤ K * (1 + |t|) := by
  classical
  obtain ⟨C, hC, hcircle⟩ := entireZeta_moving_circle_upper_bound
  obtain ⟨K, hK, hcount⟩ := sum_zetaZeroOrder_le_moving_disk
  refine ⟨C, K, hC, hK, fun t ht ↦ ?_⟩
  dsimp only
  let c : ℂ := 2 + (t : ℂ) * I
  have hfin : {ρ : criticalStripZetaZeros | (ρ : ℂ) ∈ closedBall c 5}.Finite := by
    refine ((isCompact_closedBall c 5).inter_riemannZetaZeros_finite.preimage
      Subtype.val_injective.injOn).subset ?_
    exact fun ρ hρ ↦ ⟨hρ, mem_riemannZetaZeros.mpr (mem_criticalStripZetaZeros.mp ρ.property).1⟩
  let A := hfin.toFinset
  have hA (ρ : criticalStripZetaZeros) : ρ ∈ A ↔ (ρ : ℂ) ∈ closedBall c 5 := hfin.mem_toFinset
  let B := A.map (Function.Embedding.subtype _)
  let m (z : ℂ) := (analyticOrderAt entireZeta z).toNat
  obtain ⟨g, hg, hgn, hfac⟩ := entire_extract_finset_factors entireZeta_analyticOnNhd B m
    fun z _ ↦ (ENat.natCast_toNat (analyticOrderAt_entireZeta_ne_top z)).symm
  have hm (ρ : criticalStripZetaZeros) : m ρ = zetaZeroOrder ρ := by
    obtain ⟨_, hp, hq⟩ := mem_criticalStripZetaZeros.mp ρ.property
    dsimp only [m]
    rw [analyticOrderAt_entireZeta_eq hp hq, ← zetaZeroOrder_cast_eq ρ]
    simp
  have hprod (z : ℂ) :
      entireZeta z = (∏ ρ ∈ A, (z - (ρ : ℂ)) ^ zetaZeroOrder ρ) * g z := by
    simpa [B, Finset.prod_map, hm] using hfac z
  have hdist (ρ) (hρ : ρ ∈ A) : ‖(ρ : ℂ) - c‖ ≤ 5 := by
    simpa [dist_eq_norm] using (hA ρ).mp hρ
  refine ⟨A, g, hA, hg, hprod, ?_, ?_, ?_, hcount t ht A hdist⟩
  · intro z hz hgz
    have hfz : entireZeta z = 0 := by simp [hprod z, hgz]
    let ρ : criticalStripZetaZeros := ⟨z, entireZeta_zero_iff.mp hfz⟩
    have hρ : ρ ∈ A := (hA ρ).mpr hz
    exact hgn z (Finset.mem_map.mpr ⟨ρ, hρ, rfl⟩) hgz
  · have hdiff : Differentiable ℂ g := fun z ↦ (hg z trivial).differentiableAt
    have hbd : ∀ z ∈ frontier (ball c 6), ‖g z‖ ≤ C * (1 + |t|) ^ 2 := by
      rw [frontier_ball _ (by norm_num)]
      intro z hz
      have hz' : ‖z - c‖ = 6 := by simpa [dist_eq_norm] using hz
      have hp : 1 ≤ ∏ ρ ∈ A, ‖z - (ρ : ℂ)‖ ^ zetaZeroOrder ρ := by
        apply Finset.one_le_prod₀
        intro ρ hρ
        have h := norm_add_le (z - (ρ : ℂ)) ((ρ : ℂ) - c)
        rw [sub_add_sub_cancel, hz'] at h
        exact one_le_pow₀ (by linarith [hdist ρ hρ])
      have h := hcircle t z hz
      rw [hprod z, norm_mul, norm_prod] at h
      simp only [norm_pow] at h
      exact (le_mul_of_one_le_left (norm_nonneg _) hp).trans h
    intro z hz
    rw [← closure_ball c (by norm_num : (6 : ℝ) ≠ 0)] at hz
    exact norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff.diffContOnCl hbd hz
  · rw [hprod c, norm_mul, norm_prod]
    simp only [norm_pow]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
    intro ρ hρ
    rw [norm_sub_rev]
    gcongr
    exact hdist ρ hρ

end Masullo
