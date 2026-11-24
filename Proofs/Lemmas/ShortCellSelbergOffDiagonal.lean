module

public import Lemmas.SelbergIntervalDiagonal
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lemmas.ShortCellLcmMoment
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The short-cell Selberg off-diagonal bound

Source: `8058479edd84:.godel/bob/short-cell-weil-list.md:23–37`, checked at
`03fd044fb601`. This supplies the off-diagonal input to the cell Gram bound (2),
conditional only on the ordinary interval estimates at the rescaled cells. It
does not prove a character-sum estimate or make a Burgess claim on primes.

Owning check session: `01a20fbf-64d4-7ae0-ac41-09f991160e63`.
-/

open Finset SelbergIntervalDiagonal

namespace ShortCellSelbergOffDiagonal

/-- The pinned Selberg square, with divisibility on signed integers. -/
@[expose] public noncomputable def weight (z n : ℤ) : ℝ :=
  (∑ k ∈ (cutoff z).filter (fun (k : ℕ) ↦ (k : ℤ) ∣ n), lambda z k) ^ 2

/-- On natural inputs `weight` is exactly the square in `interval_error_le`. -/
public theorem weight_natCast (z : ℤ) (n : ℕ) :
    weight z (n : ℤ) = (∑ k ∈ (cutoff z).filter (fun k ↦ k ∣ n), lambda z k) ^ 2 := by
  simp only [weight, Int.natCast_dvd_natCast]

private theorem cast_lcm_dvd_iff {d e : ℕ} {n : ℤ} :
    (d.lcm e : ℤ) ∣ n ↔ (d : ℤ) ∣ n ∧ (e : ℤ) ∣ n := by
  rw [← Int.lcm_natCast_natCast, Int.coe_lcm_dvd_iff]

-- Euclidean division by a positive m gives the quotient endpoints even for negative a.
private theorem sum_multiples (a b : ℤ) {m : ℤ} (hm : 0 < m) (f : ℤ → ℂ) :
    (∑ n ∈ (Ioc a b).filter (fun n ↦ m ∣ n), f n) =
      ∑ q ∈ Ioc (a / m) (b / m), f (m * q) := by
  symm
  refine Finset.sum_bij (fun q _ ↦ m * q) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro q hq
    obtain ⟨ha, hb⟩ := mem_Ioc.mp hq
    exact mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨by simpa only [mul_comm] using (Int.ediv_lt_iff_lt_mul hm).mp ha,
       by simpa only [mul_comm] using (Int.le_ediv_iff_mul_le hm).mp hb⟩,
      dvd_mul_right m q⟩
  · exact fun _ _ _ _ h ↦ mul_right_injective₀ hm.ne' h
  · intro n hn
    obtain ⟨hn, hd⟩ := mem_filter.mp hn
    obtain ⟨ha, hb⟩ := mem_Ioc.mp hn
    have hq := Int.ediv_mul_cancel hd
    refine ⟨n / m, mem_Ioc.mpr ⟨?_, ?_⟩, by simpa only [mul_comm] using hq⟩
    · apply (Int.ediv_lt_iff_lt_mul hm).mpr
      rwa [hq]
    · apply (Int.le_ediv_iff_mul_le hm).mpr
      rwa [hq]

private theorem weight_mul_eq (z n : ℤ) (ψ : ℤ → ℂ) :
    (weight z n : ℂ) * ψ n = ∑ d ∈ cutoff z, ∑ e ∈ cutoff z,
      if (d.lcm e : ℤ) ∣ n then (↑(lambda z d * lambda z e) : ℂ) * ψ n else 0 := by
  have h : weight z n = ∑ d ∈ cutoff z, ∑ e ∈ cutoff z,
      if (d.lcm e : ℤ) ∣ n then lambda z d * lambda z e else 0 := by
    simp only [weight, pow_two, Finset.sum_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
    by_cases hd : (d : ℤ) ∣ n <;> by_cases he : (e : ℤ) ∣ n <;>
      simp [cast_lcm_dvd_iff, hd, he]
  rw [h]
  simp only [Complex.ofReal_sum, Finset.sum_mul, apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]

private theorem weighted_sum_eq (z a b : ℤ) (ψ : ℤ → ℂ)
    (hmul : ∀ x y, ψ (x * y) = ψ x * ψ y) :
    (∑ n ∈ Ioc a b, (weight z n : ℂ) * ψ n) =
      ∑ d ∈ cutoff z, ∑ e ∈ cutoff z,
        ((↑(lambda z d * lambda z e) : ℂ) * ψ (d.lcm e : ℤ)) *
          ∑ q ∈ Ioc (a / (d.lcm e : ℤ)) (b / (d.lcm e : ℤ)), ψ q := by
  simp_rw [weight_mul_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have hm : 0 < (d.lcm e : ℤ) := by
    exact_mod_cast Nat.lcm_pos (mem_Icc.mp hd).1 (mem_Icc.mp he).1
  rw [← Finset.sum_filter, sum_multiples a b hm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦ by rw [hmul, mul_assoc]

/-- Transfer ordinary interval bounds at the exact rescaled lengths `h / lcm(d,e)`
to the Selberg-weighted sum. The integer quotient endpoints are not obtained by
rounding the length separately. The constant is uniform in the cell, cutoff,
and completely multiplicative function, whose values may be zero. -/
public theorem weighted_sum_norm_le (r : ℤ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z a : ℤ) (h : ℕ) (K : ℝ) (ψ : ℤ → ℂ),
      1 ≤ z → z ^ 2 ≤ (h : ℤ) → 0 ≤ K →
      (∀ x y, ψ (x * y) = ψ x * ψ y) → (∀ n, ‖ψ n‖ ≤ 1) →
      (∀ d ∈ cutoff z, ∀ e ∈ cutoff z, 1 ≤ (h : ℝ) / (d.lcm e : ℝ) →
        ‖∑ q ∈ Ioc (a / (d.lcm e : ℤ)) ((a + h) / (d.lcm e : ℤ)), ψ q‖ ≤
          K * ((h : ℝ) / (d.lcm e : ℝ)) ^ (1 - 1 / (r : ℝ))) →
      ‖∑ n ∈ Ioc a (a + h), (weight z n : ℂ) * ψ n‖ ≤
        C * K * (h : ℝ) ^ (1 - 1 / (r : ℝ)) * (z : ℝ) ^ (2 / (r : ℝ)) := by
  obtain ⟨C, hC, hmoment⟩ := ShortCellLcmMoment.lcm_moment_natCutoff r hr
  refine ⟨C, hC, ?_⟩
  intro z a h K ψ hz hh hK hmul hψ hinterval
  have hz_int : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (zero_le_one.trans hz)
  have hz_real : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hz_int
  have hz_nat : 1 ≤ z.toNat := by
    exact_mod_cast (show (1 : ℤ) ≤ (z.toNat : ℤ) by simpa only [hz_int] using hz)
  have hh_nat : z.toNat ^ 2 ≤ h := by
    exact_mod_cast (show (z.toNat : ℤ) ^ 2 ≤ (h : ℤ) by simpa only [hz_int] using hh)
  let p : ℝ := 1 - 1 / (r : ℝ)
  let A (d e : ℕ) : ℂ := ((↑(lambda z d * lambda z e) : ℂ) * ψ (d.lcm e : ℤ)) *
    ∑ q ∈ Ioc (a / (d.lcm e : ℤ)) ((a + h) / (d.lcm e : ℤ)), ψ q
  have hA {d e : ℕ} (hd : d ∈ cutoff z) (he : e ∈ cutoff z) :
      ‖A d e‖ ≤ (K * (h : ℝ) ^ p) * (d.lcm e : ℝ) ^ (-1 + 1 / (r : ℝ)) := by
    obtain ⟨hd₀, hdz⟩ := mem_Icc.mp hd
    obtain ⟨he₀, hez⟩ := mem_Icc.mp he
    have hm : 0 < (d.lcm e : ℝ) := by exact_mod_cast Nat.lcm_pos hd₀ he₀
    have hm_le : d.lcm e ≤ h := calc
      d.lcm e ≤ d * e := Nat.le_of_dvd (Nat.mul_pos hd₀ he₀) (Nat.lcm_dvd_mul d e)
      _ ≤ z.toNat ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hdz hez
      _ ≤ h := hh_nat
    have hT : 1 ≤ (h : ℝ) / (d.lcm e : ℝ) := by
      apply (le_div_iff₀ hm).2
      rw [one_mul]
      exact_mod_cast hm_le
    have hc : ‖(↑(lambda z d * lambda z e) : ℂ) * ψ (d.lcm e : ℤ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ 1 * 1 * 1 := mul_le_mul
          (mul_le_mul (abs_lambda_le_one hz hd) (abs_lambda_le_one hz he)
            (abs_nonneg _) zero_le_one) (hψ _) (norm_nonneg _) (by positivity)
        _ = 1 := by rw [one_mul, one_mul]
    calc
      ‖A d e‖ ≤ K * ((h : ℝ) / (d.lcm e : ℝ)) ^ p := by
        dsimp only [A]
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans
          (by rw [one_mul]; exact hinterval d hd e he hT)
      _ = _ := by
        rw [Real.div_rpow (Nat.cast_nonneg _) hm.le, div_eq_mul_inv, ← Real.rpow_neg hm.le,
          ← mul_assoc, show -p = -1 + 1 / (r : ℝ) by dsimp [p]; ring]
  rw [weighted_sum_eq z a (a + h) ψ hmul]
  change ‖∑ d ∈ cutoff z, ∑ e ∈ cutoff z, A d e‖ ≤ _
  calc
    _ ≤ ∑ d ∈ cutoff z, ∑ e ∈ cutoff z, ‖A d e‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _)
    _ ≤ ∑ d ∈ cutoff z, ∑ e ∈ cutoff z,
          (K * (h : ℝ) ^ p) * (d.lcm e : ℝ) ^ (-1 + 1 / (r : ℝ)) :=
      Finset.sum_le_sum fun _ hd ↦ Finset.sum_le_sum fun _ he ↦ hA hd he
    _ = (K * (h : ℝ) ^ p) *
          (∑ d ∈ cutoff z, ∑ e ∈ cutoff z, (d.lcm e : ℝ) ^ (-1 + 1 / (r : ℝ))) := by
      simp only [Finset.mul_sum]
    _ ≤ (K * (h : ℝ) ^ p) * (C * (z : ℝ) ^ (2 / (r : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [cutoff, hz_real] using hmoment z.toNat hz_nat
    _ = _ := by change _ = C * K * (h : ℝ) ^ p * (z : ℝ) ^ (2 / (r : ℝ)); ring

/-- A positive real cutoff uses the same coefficients at its integer floor,
which selects exactly the positive integer indices at most `z`. -/
public theorem weighted_sum_norm_le_realCutoff (r : ℤ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℝ) (a : ℤ) (h : ℕ) (K : ℝ) (ψ : ℤ → ℂ),
      0 < z → z ^ 2 ≤ (h : ℝ) → 0 ≤ K →
      (∀ x y, ψ (x * y) = ψ x * ψ y) → (∀ n, ‖ψ n‖ ≤ 1) →
      (∀ d ∈ cutoff ⌊z⌋, ∀ e ∈ cutoff ⌊z⌋, 1 ≤ (h : ℝ) / (d.lcm e : ℝ) →
        ‖∑ q ∈ Ioc (a / (d.lcm e : ℤ)) ((a + h) / (d.lcm e : ℤ)), ψ q‖ ≤
          K * ((h : ℝ) / (d.lcm e : ℝ)) ^ (1 - 1 / (r : ℝ))) →
      ‖∑ n ∈ Ioc a (a + h), (weight ⌊z⌋ n : ℂ) * ψ n‖ ≤
        C * K * (h : ℝ) ^ (1 - 1 / (r : ℝ)) * z ^ (2 / (r : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := weighted_sum_norm_le r hr
  refine ⟨C, hC, ?_⟩
  intro z a h K ψ hz hh hK hmul hψ hinterval
  have hf₀ : 0 ≤ ⌊z⌋ := Int.floor_nonneg.mpr hz.le
  by_cases hz₁ : 1 ≤ z
  · have hf₁ : 1 ≤ ⌊z⌋ := Int.le_floor.mpr (by simpa only [Int.cast_one] using hz₁)
    have hfR : 0 ≤ (⌊z⌋ : ℝ) := by exact_mod_cast hf₀
    have hfh : ⌊z⌋ ^ 2 ≤ (h : ℤ) := by
      exact_mod_cast (show (⌊z⌋ : ℝ) ^ 2 ≤ (h : ℝ) from
        (pow_le_pow_left₀ hfR (Int.floor_le z) 2).trans hh)
    have hrR : 0 ≤ (r : ℝ) := by exact_mod_cast (show 0 ≤ r from (by decide : (0 : ℤ) ≤ 2).trans hr)
    exact (hbound ⌊z⌋ a h K ψ hf₁ hfh hK hmul hψ hinterval).trans <|
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hfR (Int.floor_le z) (by positivity))
        (by positivity)
  · have hflt : ⌊z⌋ < 1 := Int.floor_lt.mpr (by simpa only [Int.cast_one] using lt_of_not_ge hz₁)
    have hf : ⌊z⌋ = 0 := by omega
    have hcut : cutoff ⌊z⌋ = ∅ := by
      rw [hf, cutoff]
      exact Finset.Icc_eq_empty_of_lt (by decide)
    have hw (n : ℤ) : weight ⌊z⌋ n = 0 := by simp [weight, hcut]
    simp only [hw, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, norm_zero]
    positivity

end ShortCellSelbergOffDiagonal
