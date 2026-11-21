module

public import Lemmas.CompactTestLaplace
public import Lemmas.ZetaZeroOrders
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Lemmas.ZetaZeroDiskCount
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic summability of the rational zeta divisor

This project estimate supplies the weight needed by `ZeroMassUniqueness` for
comparison of the full divisor in Masullo's (B.4.2.2), p. 614, with the capped
sum in (13.3.1.3), p. 522. It does not use either distribution formula.
-/

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace Masullo

private theorem norm_sub_one_le_shift (ρ : criticalStripZetaZeros) :
    ‖(ρ : ℂ) - 1‖ ≤ ‖shiftedZetaZero ρ‖ + 1 / 2 := by
  have h : shiftedZetaZero ρ - 1 / 2 = (ρ : ℂ) - 1 := by
    unfold shiftedZetaZero
    ring
  rw [← h]
  simpa [Complex.norm_div] using norm_sub_le (shiftedZetaZero ρ) (1 / 2 : ℂ)

/-- The Jensen count at radius `2^(j+1)+1` grows at most like `(j+3) * 2^j`. -/
private theorem sum_zetaZeroOrder_le_dyadic :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℕ) (A : Finset criticalStripZetaZeros),
      (∀ ρ ∈ A, ‖shiftedZetaZero ρ‖ < (2 : ℝ) ^ (j + 1)) →
      (∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ)) ≤ K * ((j : ℝ) + 3) * 2 ^ j := by
  obtain ⟨C, hC, hjensen⟩ := sum_zetaZeroOrder_le_jensen
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC₀ : 0 ≤ C := by linarith
  let a := Real.log (C + 1) / Real.log 2
  have ha : 0 ≤ a := div_nonneg (Real.log_nonneg (by linarith)) hlog.le
  refine ⟨a + 16, by linarith, fun j A hA ↦ ?_⟩
  let R : ℕ := 2 ^ (j + 1) + 1
  let n : ℕ := 2 * R + 1
  have hR : 1 ≤ R := Nat.succ_le_succ (Nat.zero_le _)
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by dsimp [n]; omega)
  have hRcast : (R : ℝ) = 2 ^ (j + 1) + 1 := by simp [R]
  have hA' (ρ) (hρ : ρ ∈ A) : ‖(ρ : ℂ) - 1‖ ≤ (R : ℝ) := by
    rw [hRcast]
    linarith [norm_sub_one_le_shift ρ, hA ρ hρ]
  have hpow : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hncast : (n : ℝ) = 4 * 2 ^ j + 3 := by
    simp only [n, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, hRcast, pow_succ]
    ring
  have hn₁ : (n : ℝ) ≤ 2 ^ (j + 3) := by
    rw [hncast, pow_add]
    norm_num
    linarith
  have hn₂ : (n : ℝ) + 2 ≤ 16 * 2 ^ j := by rw [hncast]; linarith
  have hRle : 2 * (R : ℝ) ≤ (n : ℝ) := by simp [n]
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  let M : ℝ := 1 + (n : ℝ) * (2 * (R : ℝ)) * (C * (n.factorial : ℝ))
  have hM : M ≤ (C + 1) * ((n : ℝ) ^ (n + 2)) := by
    have hbig : (1 : ℝ) ≤ (n : ℝ) ^ (n + 2) := one_le_pow₀ hn
    calc
      M ≤ 1 + (n : ℝ) * (n : ℝ) * (C * (n : ℝ) ^ n) := by
        dsimp [M]
        gcongr
      _ = 1 + C * (n : ℝ) ^ (n + 2) := by rw [pow_add]; ring
      _ ≤ (C + 1) * (n : ℝ) ^ (n + 2) := by linarith
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hlogn : Real.log (n : ℝ) ≤ ((j : ℝ) + 3) * Real.log 2 := by
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_ofNat] using
      Real.log_le_log (show 0 < (n : ℝ) by linarith) hn₁
  have hpoly : (n : ℝ) + 2 ≥ 0 := by positivity
  calc
    _ ≤ Real.log M / Real.log 2 := hjensen R hR A hA'
    _ ≤ Real.log ((C + 1) * ((n : ℝ) ^ (n + 2))) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog).2 (Real.log_le_log hMpos hM)
    _ ≤ (Real.log (C + 1) + ((n : ℝ) + 2) * (((j : ℝ) + 3) * Real.log 2)) /
        Real.log 2 := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow, Nat.cast_add, Nat.cast_ofNat]
      exact (div_le_div_iff_of_pos_right hlog).2
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogn hpoly))
    _ = a + ((n : ℝ) + 2) * ((j : ℝ) + 3) := by
      dsimp [a]
      field_simp
    _ ≤ a + (16 * 2 ^ j) * ((j : ℝ) + 3) := by gcongr
    _ ≤ (a + 16) * ((j : ℝ) + 3) * 2 ^ j := by
      have hj : 1 ≤ ((j : ℝ) + 3) * 2 ^ j :=
        one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) j]) hpow
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hj)]

private theorem exists_dyadic_upper (x : ℝ) : ∃ j : ℕ, x < (2 : ℝ) ^ (j + 1) := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt x (show (1 : ℝ) < 2 by norm_num)
  refine ⟨j, hj.trans_le ?_⟩
  rw [pow_succ]
  linarith [show 0 ≤ (2 : ℝ) ^ j by positivity]

/-- The least upper dyadic radius assigns the entire disk `‖w‖ < 2` to shell zero. -/
private noncomputable def dyadicShell (ρ : criticalStripZetaZeros) : ℕ :=
  Nat.find (exists_dyadic_upper ‖shiftedZetaZero ρ‖)

private theorem norm_lt_dyadic_upper (ρ : criticalStripZetaZeros) :
    ‖shiftedZetaZero ρ‖ < (2 : ℝ) ^ (dyadicShell ρ + 1) :=
  Nat.find_spec (exists_dyadic_upper ‖shiftedZetaZero ρ‖)

private theorem dyadic_sq_le_weight_denom (ρ : criticalStripZetaZeros) :
    ((2 : ℝ) ^ dyadicShell ρ) ^ 2 ≤ 1 + ‖shiftedZetaZero ρ‖ ^ 2 := by
  cases h : dyadicShell ρ with
  | zero => simp
  | succ j =>
    have hj : j < Nat.find (exists_dyadic_upper ‖shiftedZetaZero ρ‖) := by
      change j < dyadicShell ρ
      rw [h]
      exact Nat.lt_succ_self _
    have hnorm : (2 : ℝ) ^ (j + 1) ≤ ‖shiftedZetaZero ρ‖ :=
      le_of_not_gt (Nat.find_min _ hj)
    exact (pow_le_pow_left₀ (by positivity) hnorm 2).trans (le_add_of_nonneg_left zero_le_one)

/-- The full multiplicity at each distinct open critical-strip zero is summable
against the exact quadratic weight centered on the critical line. -/
public theorem summable_zetaZeroOrder_div_one_add_norm_sq :
    Summable (fun ρ : criticalStripZetaZeros ↦
      (zetaZeroOrder ρ : ℝ) / (1 + ‖shiftedZetaZero ρ‖ ^ 2)) := by
  classical
  obtain ⟨K, hK, hcount⟩ := sum_zetaZeroOrder_le_dyadic
  let W (ρ : criticalStripZetaZeros) := (zetaZeroOrder ρ : ℝ) / (1 + ‖shiftedZetaZero ρ‖ ^ 2)
  let B (j : ℕ) := K * ((j : ℝ) + 3) * (1 / 2 : ℝ) ^ j
  have hgeom : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hB : Summable B := by
    have h₁ := summable_pow_mul_geometric_of_norm_lt_one 1 hgeom
    have h₂ := (summable_geometric_of_norm_lt_one hgeom).mul_left (3 : ℝ)
    simpa [B, pow_one, add_mul, mul_assoc] using (h₁.add h₂).mul_left K
  -- It suffices to use the finite intersections of each shell with an arbitrary finite set.
  have hblock (j : ℕ) (A : Finset criticalStripZetaZeros)
      (hA : ∀ ρ ∈ A, dyadicShell ρ = j) : ∑ ρ ∈ A, W ρ ≤ B j := by
    let q : ℝ := (2 : ℝ) ^ j
    have hq : 0 < q := by dsimp [q]; positivity
    calc
      _ ≤ ∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ) / q ^ 2 := by
        apply Finset.sum_le_sum
        intro ρ hρ
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        simpa only [q, hA ρ hρ] using dyadic_sq_le_weight_denom ρ
      _ = (∑ ρ ∈ A, (zetaZeroOrder ρ : ℝ)) / q ^ 2 := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ K * ((j : ℝ) + 3) * q / q ^ 2 := by
        apply (div_le_div_iff_of_pos_right (by positivity)).2
        exact hcount j A (fun ρ hρ ↦ hA ρ hρ ▸ norm_lt_dyadic_upper ρ)
      _ = B j := by
        have hqi : (1 / 2 : ℝ) ^ j = q⁻¹ := by simp only [q, one_div, inv_pow]
        dsimp only [B]
        rw [hqi]
        field_simp
  apply summable_of_sum_le (f := W) (c := ∑' j, B j) (fun _ ↦ by dsimp [W]; positivity)
  intro A
  calc
    ∑ ρ ∈ A, W ρ = ∑ j ∈ A.image dyadicShell, ∑ ρ ∈ A with dyadicShell ρ = j, W ρ :=
      (Finset.sum_fiberwise_of_maps_to (fun _ hρ ↦ Finset.mem_image_of_mem dyadicShell hρ) W).symm
    _ ≤ ∑ j ∈ A.image dyadicShell, B j :=
      Finset.sum_le_sum fun j _ ↦ hblock j _ (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
    _ ≤ ∑' j, B j := hB.sum_le_tsum _ (fun j _ ↦ by dsimp [B]; positivity)

/-- On every smooth compact positive-log test, any zero weights dominated by the
full zeta orders yield an absolutely convergent test sum. No mass condition is needed. -/
public theorem summable_norm_zetaZero_mul_positiveLaplaceTest
    {d : criticalStripZetaZeros → ℂ} (hd : ∀ ρ, ‖d ρ‖ ≤ (zetaZeroOrder ρ : ℝ))
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ht : tsupport f ⊆ Ioi (0 : ℝ)) :
    Summable fun ρ ↦ ‖d ρ * positiveLaplaceTest (shiftedZetaZero ρ) f‖ := by
  let a : ℝ := 1 / 2
  let C := (∫ x in Ioi (0 : ℝ), Real.exp (a * x) * ‖f x‖) +
    (∫ x in Ioi (0 : ℝ), Real.exp (a * x) * ‖deriv (deriv f) x‖)
  have hs : Summable (fun ρ ↦ ‖d ρ‖ / (1 + ‖shiftedZetaZero ρ‖ ^ 2)) :=
    summable_zetaZeroOrder_div_one_add_norm_sq.of_nonneg_of_le (fun _ ↦ by positivity)
      (fun ρ ↦ div_le_div_of_nonneg_right (hd ρ) (by positivity))
  refine (hs.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun ρ ↦ ?_
  have ha : (shiftedZetaZero ρ).re ≤ a :=
    ((le_abs_self _).trans_lt (abs_re_shiftedZetaZero_lt ρ)).le
  exact norm_mul_positiveLaplaceTest_le ha hf hc ht (le_refl C)

end Masullo
