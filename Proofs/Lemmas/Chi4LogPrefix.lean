module

public import Lemmas.Chi4Divisor
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Character prefixes and logarithmic sums modulo four -/

open Finset

namespace Chi4Divisor

private theorem chi_eq (n : ℕ) :
    chi n = if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0 := by
  have h : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rw [chi, ZMod.χ₄_nat_eq_if_mod_four, ← Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)]
  rcases h with h | h | h | h <;> simp [h]

private theorem M_succ (t : ℕ) : M (t + 1) = M t + chi (t + 1) :=
  sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le t)) chi

private theorem A_succ (t : ℕ) : A (t + 1) = A t + chi (t + 1) * Real.log (t + 1 : ℕ) :=
  sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le t)) fun n ↦ chi n * Real.log n

/-- The character prefix is `1` in residues `1` and `2`, and `0` otherwise. -/
public theorem M_eq (t : ℕ) : M t = if t % 4 = 1 ∨ t % 4 = 2 then 1 else 0 := by
  induction t with
  | zero => simp [M]
  | succ t ih =>
    rw [M_succ, ih, chi_eq]
    have h : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
    rcases h with h | h | h | h
    · simp [h, show (t + 1) % 4 = 1 by omega]
    · simp [h, show (t + 1) % 4 = 2 by omega]
    · simp [h, show (t + 1) % 4 = 3 by omega]
    · simp [h, show (t + 1) % 4 = 0 by omega]

/-- The boundary-term-subtracted sum from discrete summation by parts. -/
private noncomputable def abelRemainder (t : ℕ) : ℝ := A t - M t * Real.log t

private theorem abelRemainder_succ (t : ℕ) :
    abelRemainder (t + 1) = abelRemainder t - M t * (Real.log (t + 1 : ℕ) - Real.log t) := by
  unfold abelRemainder
  rw [A_succ, M_succ]
  ring

private theorem abelRemainder_bounds (t : ℕ) (ht : 1 ≤ t) :
    -Real.log t ≤ abelRemainder t ∧ abelRemainder t ≤ 0 := by
  induction t, ht using Nat.le_induction with
  | base => simp [abelRemainder, A, Nat.cast_one, Real.log_one]
  | succ t ht ih =>
    have hlog : Real.log (t : ℝ) ≤ Real.log (t + 1 : ℕ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < t by omega))
        (by exact_mod_cast Nat.le_succ t)
    rw [abelRemainder_succ, M_eq]
    split <;> simp only [one_mul, zero_mul, sub_zero] <;> constructor <;>
      linarith [ih.1, ih.2]

/-- The logarithmically weighted character prefix has magnitude at most `log X`. -/
public theorem abs_A_le_log {X : ℕ} (hX : 1 ≤ X) : |A X| ≤ Real.log X := by
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  obtain ⟨hlo, hhi⟩ := abelRemainder_bounds X hX
  rw [abelRemainder, M_eq] at hlo hhi
  rw [abs_le]
  by_cases h : X % 4 = 1 ∨ X % 4 = 2 <;>
    simp only [h, ite_true, ite_false, one_mul, zero_mul, sub_zero] at hlo hhi <;>
    constructor <;> linarith

end Chi4Divisor
