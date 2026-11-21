module

public import Lemmas.ShiftedZetaZeros
import Lemmas.RationalCompletedZetaZeros
import Lemmas.ZetaZeroSummability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Separated heights for the rational completed-zeta contour

Masullo (B.4.2.1), p. 614, invokes Lang's choice of well-separated
heights for the growth hypothesis of the asymptotic residue theorem.
For polynomial bounds with Schwartz tests, a polynomial separation
margin suffices in place of Lang's logarithmic margin. We obtain that
margin from the checked quadratically weighted zero count. The bound
for the logarithmic derivative on these segments is a separate step.
-/

open MeasureTheory Set

namespace Masullo

private theorem shiftedZetaZero_denom_le_of_im_bounds (ρ : criticalStripZetaZeros)
    {x : ℝ} (hl : x - 1 < (ρ : ℂ).im) (hu : (ρ : ℂ).im < x + 2) :
    1 + ‖shiftedZetaZero ρ‖ ^ 2 ≤ 6 * (1 + |x|) ^ 2 := by
  have hre := abs_re_shiftedZetaZero_lt ρ
  have him : (shiftedZetaZero ρ).im = (ρ : ℂ).im := by simp [shiftedZetaZero]
  have hi : |(shiftedZetaZero ρ).im| ≤ |x| + 2 := by
    rw [him, abs_le]
    constructor <;> linarith [neg_abs_le x, le_abs_self x]
  have hr₂ := pow_le_pow_left₀ (abs_nonneg _) hre.le 2
  have hi₂ := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [sq_abs] at hr₂ hi₂
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [abs_nonneg x, sq_nonneg |x|]

/-- Each interval `(m, m + 1)` admits a height with a uniform quadratic
separation margin from all open critical-strip zero ordinates. The single
constant works for positive and negative `m`. -/
public theorem exists_height_separated_from_zeta_zeros :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℤ, ∃ t : ℝ,
      (m : ℝ) < t ∧ t < (m : ℝ) + 1 ∧ ∀ ρ : criticalStripZetaZeros,
        c / (1 + |(m : ℝ)|) ^ 2 ≤ |t - (ρ : ℂ).im| := by
  classical
  let w (ρ : criticalStripZetaZeros) : ℝ :=
    (zetaZeroOrder ρ : ℝ) / (1 + ‖shiftedZetaZero ρ‖ ^ 2)
  have hw (ρ : criticalStripZetaZeros) : 0 ≤ w ρ := by dsimp [w]; positivity
  have hs : Summable w := summable_zetaZeroOrder_div_one_add_norm_sq
  let S := ∑' ρ, w ρ
  have hS : 0 ≤ S := tsum_nonneg hw
  let c : ℝ := 1 / (24 * (S + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, fun m ↦ ?_⟩
  let x : ℝ := m
  let R : ℝ := (1 + |x|) ^ 2
  have hR : 1 ≤ R := by dsimp [R]; nlinarith [abs_nonneg x, sq_nonneg |x|]
  let δ := c / R
  have hδ : 0 < δ := div_pos hc (by linarith)
  have hδ₁ : δ ≤ 1 := by
    change c / R ≤ 1
    rw [div_le_one (by linarith : 0 < R)]
    exact (show c ≤ 1 by dsimp [c]; rw [div_le_one (by positivity)]; linarith).trans hR
  -- Only zeros in the enlarged interval can cut out any of `(x, x + 1)`.
  let F := (criticalStripZetaZeros_boundedIm_finite (x - 1) (x + 2)).toFinset
  have hmem (ρ : criticalStripZetaZeros) :
      ρ ∈ F ↔ x - 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im < x + 2 := by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hD : 0 < 6 * R := by linarith
  have hcount : (F.card : ℝ) ≤ 6 * R * S := by
    rw [mul_comm (6 * R) S]
    apply (div_le_iff₀ hD).mp
    calc
      (F.card : ℝ) / (6 * R) = ∑ ρ ∈ F, 1 / (6 * R) := by simp [div_eq_mul_inv]
      _ ≤ ∑ ρ ∈ F, w ρ := Finset.sum_le_sum fun ρ hρ ↦ by
        obtain ⟨hl, hu⟩ := (hmem ρ).mp hρ
        have hn : (1 : ℝ) ≤ zetaZeroOrder ρ := by
          exact_mod_cast Nat.succ_le_of_lt (zetaZeroOrder_pos ρ)
        exact (div_le_div_of_nonneg_left zero_le_one (by positivity)
          (shiftedZetaZero_denom_le_of_im_bounds ρ hl hu)).trans
          (div_le_div_of_nonneg_right hn (by positivity))
      _ ≤ S := hs.sum_le_tsum F fun ρ _ ↦ hw ρ
  -- The union of the bad intervals has measure at most half of the unit interval.
  let J (ρ : criticalStripZetaZeros) := Ioo ((ρ : ℂ).im - δ) ((ρ : ℂ).im + δ)
  let B := ⋃ ρ ∈ F, J ρ
  have hB : volume B ≤ ENNReal.ofReal (1 / 2) := by
    calc
      volume B ≤ ∑ ρ ∈ F, volume (J ρ) := measure_biUnion_finset_le F J
      _ = ENNReal.ofReal (2 * δ * (F.card : ℝ)) := by
        simp only [J, Real.volume_Ioo, show ∀ y : ℝ, y + δ - (y - δ) = 2 * δ by intro; ring]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
        simp [mul_comm]
      _ ≤ ENNReal.ofReal (1 / 2) := by
        refine ENNReal.ofReal_le_ofReal (show 2 * δ * (F.card : ℝ) ≤ (1 / 2 : ℝ) from ?_)
        calc
          _ ≤ 2 * δ * (6 * R * S) := mul_le_mul_of_nonneg_left hcount (by positivity)
          _ = S / (2 * (S + 1)) := by
            dsimp only [δ, c]
            field_simp [show R ≠ 0 by linarith]
            ring
          _ ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨t, ht, htB⟩ : ∃ t ∈ Ioo x (x + 1), t ∉ B := by
    by_contra! h
    have hle := (measure_mono h).trans hB
    rw [Real.volume_Ioo, show x + 1 - x = 1 by ring] at hle
    exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by norm_num))) hle
  refine ⟨t, ht.1, ht.2, fun ρ ↦ ?_⟩
  change δ ≤ |t - (ρ : ℂ).im|
  by_contra! hclose
  obtain ⟨hl, hu⟩ := abs_lt.mp hclose
  have hρ : ρ ∈ F := (hmem ρ).2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact htB (mem_biUnion hρ ⟨by linarith, by linarith⟩)

end Masullo
