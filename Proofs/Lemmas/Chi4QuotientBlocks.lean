module

public import Lemmas.Chi4LogPrefix
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

/-! # Quotient blocks of the signed mod-four divisor sum

The active quotients `1` and `2` give a difference of inclusive prefixes.
The remaining active quotients are separated at `Nat.sqrt X`, with equality
on the small-divisor side.
-/

namespace Chi4Divisor

open Finset

/-- The signed contribution of active quotients at least `5` from small divisors. -/
@[expose] public noncomputable def S (X : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 X).filter (fun d ↦ d ≤ Nat.sqrt X ∧ 5 ≤ X / d ∧
      ((X / d) % 4 = 1 ∨ (X / d) % 4 = 2)), w d

/-- The signed contribution of active quotients at least `5` from large divisors. -/
@[expose] public noncomputable def B (X : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 X).filter (fun d ↦ Nat.sqrt X < d ∧ 5 ≤ X / d ∧
      ((X / d) % 4 = 1 ∨ (X / d) % 4 = 2)), w d

private theorem prefix_split (X : ℕ) :
    (∑ d ∈ Icc 1 X, w d) =
      (∑ d ∈ (Icc 1 X).filter (fun d ↦ X / 3 < d), w d) + ∑ d ∈ Icc 1 (X / 3), w d := by
  have h : (Icc 1 X).filter (fun d ↦ d ≤ X / 3) = Icc 1 (X / 3) := by
    ext d
    simp only [mem_filter, mem_Icc]
    exact ⟨fun ⟨⟨hl, _⟩, hr⟩ ↦ ⟨hl, hr⟩,
      fun ⟨hl, hr⟩ ↦ ⟨⟨hl, hr.trans (Nat.div_le_self X 3)⟩, hr⟩⟩
  simpa only [not_le, h] using
    (sum_filter_not_add_sum_filter (Icc 1 X) (fun d ↦ d ≤ X / 3) w).symm

/-- The large active quotients leave a difference of two inclusive twisted prefixes. -/
public theorem recurrence (X : ℕ) :
    TerminalTriangle.D (X : ℝ) - TerminalTriangle.D ((X / 3 : ℕ) : ℝ) = A X - S X - B X := by
  have hA : A X =
      (∑ d ∈ (Icc 1 X).filter (fun d ↦ X / 3 < d), w d) + S X + B X := by
    rw [divisor_identity, S, B, sum_filter, sum_filter, sum_filter,
      ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    obtain ⟨hd₀, hdX⟩ := mem_Icc.mp hd
    have hpos : 0 < X / d := Nat.div_pos hdX hd₀
    -- For a positive quotient, being below `3` means it is one of the two
    -- active quotients below `5`, namely `1` or `2`.
    have hlow : X / 3 < d ↔ X / d < 5 ∧ ((X / d) % 4 = 1 ∨ (X / d) % 4 = 2) := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 3), mul_comm d 3, ← Nat.div_lt_iff_lt_mul hd₀]
      omega
    simp only [hlow, M_eq]
    by_cases ha : (X / d) % 4 = 1 ∨ (X / d) % 4 = 2
    · by_cases ht : 5 ≤ X / d
      · by_cases hs : d ≤ Nat.sqrt X <;> simp [ha, ht, not_lt_of_ge ht, hs, lt_iff_not_ge]
      · simp [ha, ht, Nat.lt_of_not_ge ht]
    · simp [ha]
  rw [D_nat, D_nat, hA, prefix_split X]
  ring

/-- The large divisors whose quotients lie in `[4j+1, 4j+3)`. -/
@[expose] public def block (X j : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun d ↦ Nat.sqrt X < d ∧ (4*j+1)*d ≤ X ∧ X < (4*j+3)*d)

/-- For a positive divisor, the product inequalities are precisely the two quotient bounds. -/
public theorem quotient_block_iff {X d j : ℕ} (hd : 0 < d) :
    (4*j+1)*d ≤ X ∧ X < (4*j+3)*d ↔ 4*j+1 ≤ X / d ∧ X / d < 4*j+3 := by
  rw [Nat.le_div_iff_mul_le hd, Nat.div_lt_iff_lt_mul hd]

private theorem div_four_eq_of_mem_block {X d j : ℕ} (h : d ∈ block X j) : X / d / 4 = j := by
  obtain ⟨hd, _, hb⟩ := mem_filter.mp h
  have hq := (quotient_block_iff (mem_Icc.mp hd).1).mp hb
  omega

/-- Distinct quotient blocks have no common divisor. -/
public theorem block_disjoint (X : ℕ) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (block X j) (block X k) := by
  apply disjoint_left.mpr
  intro d hdj hdk
  exact hjk ((div_four_eq_of_mem_block hdj).symm.trans (div_four_eq_of_mem_block hdk))

/-- The large active divisors are covered exactly once by the finite block family. -/
public theorem large_active_iff_existsUnique_block {X d : ℕ} :
    (d ∈ Icc 1 X ∧ Nat.sqrt X < d ∧ 5 ≤ X / d ∧
      ((X / d) % 4 = 1 ∨ (X / d) % 4 = 2)) ↔
    ∃! j, j ∈ Icc 1 (Nat.sqrt X / 4) ∧ d ∈ block X j := by
  constructor
  · rintro ⟨hd, hds, ht, ha⟩
    have hd₀ : 0 < d := (mem_Icc.mp hd).1
    -- A divisor above the square root has quotient at most `Nat.sqrt X`.
    have hq : X / d ≤ Nat.sqrt X := by
      apply Nat.lt_succ_iff.mp
      exact (Nat.div_lt_iff_lt_mul hd₀).mpr
        ((Nat.lt_succ_sqrt X).trans_le (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hds)))
    refine ⟨X / d / 4, ⟨mem_Icc.mpr ⟨by omega, Nat.div_le_div_right hq⟩, ?_⟩,
      fun j hj ↦ (div_four_eq_of_mem_block hj.2).symm⟩
    exact mem_filter.mpr ⟨hd, hds, (quotient_block_iff hd₀).mpr (by omega)⟩
  · rintro ⟨j, ⟨hj, hdj⟩, _⟩
    obtain ⟨hd, hds, hb⟩ := mem_filter.mp hdj
    have hq := (quotient_block_iff (mem_Icc.mp hd).1).mp hb
    have hj₁ := (mem_Icc.mp hj).1
    exact ⟨hd, hds, by omega, by omega⟩

/-- Regroup `B` as a sum of signed block sums, without changing any weight. -/
public theorem B_eq_sum_blocks (X : ℕ) :
    B X = ∑ j ∈ Icc 1 (Nat.sqrt X / 4), ∑ d ∈ block X j, w d := by
  let J := Icc 1 (Nat.sqrt X / 4)
  have hdis : (J : Set ℕ).PairwiseDisjoint (block X) :=
    fun _ _ _ _ hjk ↦ block_disjoint X hjk
  have hcover : (Icc 1 X).filter (fun d ↦ Nat.sqrt X < d ∧ 5 ≤ X / d ∧
      ((X / d) % 4 = 1 ∨ (X / d) % 4 = 2)) = J.disjiUnion (block X) hdis := by
    ext d
    rw [mem_filter, mem_disjiUnion]
    constructor
    · intro hd
      obtain ⟨j, hj, _⟩ := large_active_iff_existsUnique_block.mp hd
      exact ⟨j, hj⟩
    · rintro ⟨j, hj, hdj⟩
      apply large_active_iff_existsUnique_block.mpr
      exact ⟨j, ⟨hj, hdj⟩, fun k hk ↦
        (div_four_eq_of_mem_block hk.2).symm.trans (div_four_eq_of_mem_block hdj)⟩
  rw [B, hcover, sum_disjiUnion]

private theorem abs_chi_bound (d : ℕ) : |chi d| ≤ 1 := by
  rw [chi, ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

/-- There are at most `Nat.sqrt X` small divisors, each of weight at most `log X`. -/
public theorem abs_S_le {X : ℕ} (hX : 1 ≤ X) : |S X| ≤ Real.sqrt X * Real.log X := by
  let s := (Icc 1 X).filter (fun d ↦ d ≤ Nat.sqrt X ∧ 5 ≤ X / d ∧
      ((X / d) % 4 = 1 ∨ (X / d) % 4 = 2))
  have hc : s.card ≤ Nat.sqrt X := by
    calc
      s.card ≤ (Icc 1 (Nat.sqrt X)).card := by
        apply card_le_card
        intro d hd
        obtain ⟨hm, hs, _⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hs⟩
      _ = Nat.sqrt X := by simp [Nat.card_Icc]
  have hc' : (s.card : ℝ) ≤ Real.sqrt X :=
    (show (s.card : ℝ) ≤ (Nat.sqrt X : ℝ) by exact_mod_cast hc).trans Real.nat_sqrt_le_real_sqrt
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  change |∑ d ∈ s, w d| ≤ _
  calc
    _ ≤ ∑ d ∈ s, |w d| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _d ∈ s, Real.log (X : ℝ) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hd₀, hdX⟩ := mem_Icc.mp (mem_filter.mp hd).1
      rw [w, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc
        _ ≤ ArithmeticFunction.vonMangoldt d * 1 :=
          mul_le_mul_of_nonneg_left (abs_chi_bound d) ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ Real.log (d : ℝ) := by simpa only [mul_one] using ArithmeticFunction.vonMangoldt_le_log
        _ ≤ Real.log (X : ℝ) := Real.log_le_log (by exact_mod_cast hd₀) (by exact_mod_cast hdX)
    _ = (s.card : ℝ) * Real.log (X : ℝ) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc' hlog

end Chi4Divisor
