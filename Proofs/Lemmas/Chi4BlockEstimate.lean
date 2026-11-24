module

public import Lemmas.Chi4QuotientBlocks
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # The signed block estimate is equivalent to the twisted Mangoldt estimate

Neither growth estimate is asserted. All asymptotics here are at natural cutoffs.
-/

namespace Chi4Divisor

open Filter Asymptotics Finset

private theorem div_pow_le (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ((n / 3 : ℕ) : ℝ) ^ θ ≤ (n : ℝ) ^ θ / (3 : ℝ) ^ θ := by
  rw [← Real.div_rpow (Nat.cast_nonneg n) (by norm_num)]
  apply Real.rpow_le_rpow (by positivity) _ hθ
  exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := n) (n := 3))

/-- For any positive exponent, bounding the difference at the third-quotient
is equivalent to bounding the original sequence. -/
public theorem third_difference_isBigO_iff (f : ℕ → ℝ) {θ : ℝ} (hθ : 0 < θ) :
    (fun n ↦ f n - f (n / 3)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ θ) ↔
    f =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ θ) := by
  have hp (n : ℕ) : 0 ≤ (n : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg n) _
  constructor
  · intro h
    obtain ⟨c, hc, H⟩ := h.exists_pos
    obtain ⟨N, hN⟩ := eventually_atTop.mp H.bound
    -- Start the recurrence only where the difference bound applies and `n / 3 ≥ 1`.
    let k := max N 3
    let q := (3 : ℝ) ^ θ
    have hq : 1 < q := Real.one_lt_rpow (by norm_num) hθ
    -- The prefix covers the base cases; the second term pays the geometric tail.
    let K := (∑ i ∈ range k, |f i|) + c * q / (q - 1)
    have hcost : 0 ≤ c * q / (q - 1) := by positivity
    have hsum : 0 ≤ ∑ i ∈ range k, |f i| := sum_nonneg fun _ _ ↦ abs_nonneg _
    have hK : 0 ≤ K := add_nonneg hsum hcost
    have hcontract : c + K / q ≤ K := by
      have hbudget : c * q ≤ K * (q - 1) := (div_le_iff₀ (by linarith : 0 < q - 1)).mp
        (show c * q / (q - 1) ≤ K by dsimp [K]; linarith)
      rw [← le_sub_iff_add_le', div_le_iff₀ (by linarith : 0 < q)]
      linarith
    have hbound (n : ℕ) (hn : 1 ≤ n) : |f n| ≤ K * (n : ℝ) ^ θ := by
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        by_cases hnk : n < k
        · have hfn : |f n| ≤ ∑ i ∈ range k, |f i| :=
            single_le_sum (fun i _ ↦ abs_nonneg (f i)) (mem_range.mpr hnk)
          have hone := Real.one_le_rpow (show 1 ≤ (n : ℝ) by exact_mod_cast hn) hθ.le
          exact (hfn.trans (le_add_of_nonneg_right hcost)).trans (le_mul_of_one_le_right hK hone)
        · have hNn : N ≤ n := (le_max_left ..).trans (le_of_not_gt hnk)
          have h3 : 3 ≤ n := (le_max_right ..).trans (le_of_not_gt hnk)
          have hdiff : |f n - f (n / 3)| ≤ c * (n : ℝ) ^ θ := by
            simpa [Real.norm_eq_abs, abs_of_nonneg (hp n)] using hN n hNn
          have hsmall := ih (n / 3) (Nat.div_lt_self (by omega) (by decide)) (by omega)
          calc
            |f n| = |(f n - f (n / 3)) + f (n / 3)| := by rw [sub_add_cancel]
            _ ≤ |f n - f (n / 3)| + |f (n / 3)| := abs_add_le ..
            _ ≤ c * (n : ℝ) ^ θ + K * ((n : ℝ) ^ θ / q) :=
              add_le_add hdiff (hsmall.trans (mul_le_mul_of_nonneg_left (div_pow_le n hθ.le) hK))
            _ = (c + K / q) * (n : ℝ) ^ θ := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hcontract (hp n)
    apply isBigO_iff.mpr ⟨K, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    simpa [Real.norm_eq_abs, abs_of_nonneg (hp n)] using hbound n hn
  · intro h
    apply h.sub
    obtain ⟨c, hc, H⟩ := h.exists_pos
    obtain ⟨N, hN⟩ := eventually_atTop.mp H.bound
    apply isBigO_iff.mpr ⟨c, eventually_atTop.mpr ⟨3 * N, ?_⟩⟩
    intro n hn
    have hq := hN (n / 3) (by omega)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hp _)] at hq ⊢
    exact hq.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.div_le_self n 3) hθ.le) hc.le)

private theorem prefix_error_isBigO {θ : ℝ} (hθ : 1 / 2 < θ) :
    (fun n ↦ A n - S n) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ θ) := by
  let ε := θ - 1 / 2
  have hε : 0 < ε := sub_pos.mpr hθ
  apply isBigO_iff.mpr ⟨2 / ε, eventually_atTop.mpr ⟨1, ?_⟩⟩
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hlog := Real.log_nonneg hn'
  have hsqrt : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn'
  have hpow : 0 ≤ (n : ℝ) ^ θ := Real.rpow_nonneg hn0.le _
  simp only [Real.norm_eq_abs, abs_of_nonneg hpow]
  calc
    |A n - S n| ≤ |A n| + |S n| := abs_sub ..
    _ ≤ Real.log n + Real.sqrt n * Real.log n := add_le_add (abs_A_le_log hn) (abs_S_le hn)
    _ ≤ 2 * (Real.sqrt n * Real.log n) := by nlinarith [mul_le_mul_of_nonneg_right hsqrt hlog]
    _ ≤ 2 * (Real.sqrt n * ((n : ℝ) ^ ε / ε)) := by
      gcongr
      exact Real.log_le_rpow_div hn0.le hε
    _ = _ := by
      rw [Real.sqrt_eq_rpow, show θ = 1 / 2 + ε by dsimp [ε]; ring, Real.rpow_add hn0]
      ring

/-- For each fixed exponent above one half, cancellation of the signed quotient
blocks is precisely as strong as the corresponding twisted Chebyshev bound. -/
public theorem B_isBigO_iff_D_isBigO {θ : ℝ} (hθ : 1 / 2 < θ) :
    B =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ θ) ↔
    (fun n : ℕ ↦ TerminalTriangle.D (n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ θ) := by
  rw [← third_difference_isBigO_iff (fun n : ℕ ↦ TerminalTriangle.D (n : ℝ)) (by linarith : 0 < θ)]
  constructor
  · intro h
    exact ((prefix_error_isBigO hθ).sub h).congr (fun n ↦ (recurrence n).symm) (fun _ ↦ rfl)
  · intro h
    apply ((prefix_error_isBigO hθ).sub h).congr _ (fun _ ↦ rfl)
    intro n
    change A n - S n - (TerminalTriangle.D _ - TerminalTriangle.D _) = B n
    rw [recurrence n]
    ring

end Chi4Divisor
