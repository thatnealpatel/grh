module

public import Lemmas.SpacedGapIncidences
public import Lemmas.AdaptivePlaneSmoothPrice
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# The smooth-number price of spaced-gap incidences

Source: `a9dedc89666e:.godel/alice/spaced-product-cut.md:15–23`, unchanged from
`ece3826d8144`; consumer: `.godel/alice/forced-output-cuts.md:57`.

Scope: the finite `s ≤ L` branch, counting the actual pairs of a crossing
modulus and a nonvanishing affine solution in the translated box. The bound
keeps the divisor bound and the reciprocal sums explicit. It gives neither a
`q`-asymptotic estimate nor a column count.

Owning check session: `01a20fa3-d781-7816-bdbd-149ebe36b7b4`.
-/

open scoped BigOperators

namespace SpacedGapIncidences

open SpacedGapModuli AdaptivePlaneBin

private theorem card_le_smoothEulerPrice_of_smooth {S : Finset ℕ} {Y : ℝ} {X : ℕ}
    (hY : 0 ≤ Y) (hS : ∀ n ∈ S, (n : ℝ) ≤ Y ∧ n ∈ Nat.smoothNumbers (X + 1)) :
    (S.card : ℝ) ≤ √Y * smoothEulerPrice X := by
  have hsub : S ⊆ smallDividedR Y X := by
    intro n hn
    obtain ⟨hnY, hns⟩ := hS n hn
    refine (mem_smallDividedR hY).mpr ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hns),
      hnY, fun p hp => ?_⟩
    exact Nat.lt_succ_iff.mp
      (Nat.mem_primesBelow.mp (Nat.primeFactors_subset_of_mem_smoothNumbers hns hp)).1
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (card_smallDividedR_le_smoothEulerPrice hY X)

/-- The actual finite incidence count, with the two smooth modulus menus priced
by the same half-power Euler product. The occupancy tail retains its original
index sets, including when either sum is empty. -/
public theorem incidenceCount_le_smoothEulerPrice
    {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {X D : ℕ}
    (hL : 1 ≤ L) (hLH : L ≤ H) (hs : 1 ≤ s) (hsL : (s : ℝ) ≤ L)
    (hA : 2 * H < (A : ℝ)) (hB : B ≠ 0) (hAB : IsCoprime A B) :
    let U := L / (s : ℝ)
    let M := (integerBox j₀ b₀ U H).card
    let C := √(8 * (X : ℝ) * U * H) * smoothEulerPrice X
    (∀ m ∈ Finset.Ico 2 M, ∀ k ∈ multiplierMenu U m, ∀ t ∈ crossingMenu B U H X m k,
      ∀ v, Direction A B s U H m k t v → (directionForm A B s v).natAbs.divisors.card ≤ D) →
    (incidenceCount a₀ s A B j₀ b₀ L H X : ℝ) ≤
      2 * C * (1 + (D : ℝ) * ∑ m ∈ Finset.Ico 2 M,
        (1 / (m : ℝ)) * ∑ k ∈ multiplierMenu U m, 1 / (k : ℝ)) := by
  intro U M C hD
  let Y : ℝ := 8 * (X : ℝ) * U * H
  have hs₀ : (0 : ℝ) ≤ s := (Int.cast_pos.mpr (show 0 < s from hs)).le
  have hU : 0 ≤ U := div_nonneg (zero_le_one.trans hL) hs₀
  have hH : 0 ≤ H := zero_le_one.trans (hL.trans hLH)
  have hY : 0 ≤ Y := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg X)) hU) hH
  have hF : ((eligibleModuli A B U H X).card : ℝ) ≤ C :=
    card_le_smoothEulerPrice_of_smooth hY fun _ hf => (mem_eligibleModuli.mp hf).1
  -- The second crossing divides the smooth upper cutoff by `(m*k)^2`.
  have hcross (m : ℕ) (hm : m ∈ Finset.Ico 2 M) (k : ℕ) (hk : k ∈ multiplierMenu U m) :
      ((crossingMenu B U H X m k).card : ℝ) ≤ C * ((1 / (m : ℝ)) * (1 / (k : ℝ))) := by
    have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) (Finset.mem_Ico.mp hm).1)
    have hk₀ : (0 : ℝ) < k := Nat.cast_pos.mpr (Finset.mem_Icc.mp hk).1
    have hcutoff : (X : ℝ) * threshold U H m k = Y / ((m : ℝ) * (k : ℝ)) ^ 2 := by
      dsimp [threshold, Y]
      ring
    have hcutoff₀ : 0 ≤ (X : ℝ) * threshold U H m k :=
      hcutoff ▸ div_nonneg hY (sq_nonneg _)
    calc
      _ ≤ √((X : ℝ) * threshold U H m k) * smoothEulerPrice X :=
        card_le_smoothEulerPrice_of_smooth hcutoff₀ fun _ ht => (mem_crossingMenu.mp ht).1
      _ = _ := by
        rw [hcutoff, Real.sqrt_div hY, Real.sqrt_sq (mul_pos hm₀ hk₀).le]
        dsimp [C, Y]
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
        ring
  have hcount := incidenceCount_le (a₀ := a₀) (j₀ := j₀) (b₀ := b₀) (X := X)
    hL hLH hs hsL hA hB hAB hD
  calc
    _ ≤ 2 * ((eligibleModuli A B U H X).card : ℝ) + ∑ m ∈ Finset.Ico 2 M,
        ∑ k ∈ multiplierMenu U m, ((crossingMenu B U H X m k).card : ℝ) * 2 * (D : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using
        (Nat.cast_le (α := ℝ)).mpr hcount
    _ ≤ 2 * C + ∑ m ∈ Finset.Ico 2 M, ∑ k ∈ multiplierMenu U m,
        2 * C * ((D : ℝ) * ((1 / (m : ℝ)) * (1 / (k : ℝ)))) := by
      refine add_le_add (mul_le_mul_of_nonneg_left hF zero_le_two) ?_
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ (C * ((1 / (m : ℝ)) * (1 / (k : ℝ)))) * 2 * (D : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcross m hm k hk) zero_le_two)
            (Nat.cast_nonneg D)
        _ = _ := by ring
    _ = _ := by simp only [mul_add, mul_one, Finset.mul_sum]

end SpacedGapIncidences
