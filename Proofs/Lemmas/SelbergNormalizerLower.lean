module

public import Lemmas.SelbergIntervalDiagonal
public import Mathlib.NumberTheory.Harmonic.Bounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Lower bounds for the finite Selberg normalizer

Sources: `8058479edd84:.godel/bob/short-cell-weil-list.md:21–37` and
`3e5e4276933b:.godel/bob/sieved-height-gram.md:27–29`. The normalizer is
`SelbergIntervalDiagonal.J` from `ece3826d8144`.

Scope: the exact harmonic lower bound for the integer cutoff and the resulting
`log z` lower bound at the real cutoff `z ≥ 1`. This does not reprove the
interval diagonal or address the Gram form.

Owning check session: `01a20fa3-d781-7816-bdbd-149ebe36b7b4`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace SelbergIntervalDiagonal

private def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

-- For a fixed radical `r`, take `M = r ^ N`. Each index `n` in the fiber divides
-- `M`, and `(M / n) * r` is a distinct divisor of `M` with totient
-- `(M / n) * φ(r)`. The divisor sum of the totient bounds the whole fiber.
private theorem sum_rad_fiber_le {N r : ℕ} (hN : 0 < N) (hr : Squarefree r) :
    (∑ n ∈ (Icc 1 N).filter (fun n ↦ rad n = r), (n : ℝ)⁻¹) ≤ (r.totient : ℝ)⁻¹ := by
  let S := (Icc 1 N).filter (fun n ↦ rad n = r)
  let M := r ^ N
  let f (n : ℕ) := M / n * r
  have hr₀ := Nat.pos_of_ne_zero hr.ne_zero
  have hM : 0 < M := pow_pos hr₀ _
  have hn_dvd {n : ℕ} (hn : n ∈ S) : n ∣ M := by
    obtain ⟨hn, hrad⟩ := mem_filter.mp hn
    exact (hrad ▸ Nat.dvd_prod_primeFactors_pow_self (Nat.ne_of_gt (mem_Icc.mp hn).1) :
      n ∣ r ^ n).trans (pow_dvd_pow r (mem_Icc.mp hn).2)
  have hr_dvd {n : ℕ} (hn : n ∈ S) : r ∣ n := by
    rw [← (mem_filter.mp hn).2]
    exact Nat.prod_primeFactors_dvd n
  have hf_dvd {n : ℕ} (hn : n ∈ S) : f n ∣ M := by
    obtain ⟨k, hk⟩ := hr_dvd hn
    refine ⟨k, (Nat.div_mul_cancel (hn_dvd hn)).symm.trans ?_⟩
    change M / n * n = M / n * r * k
    rw [mul_assoc, ← hk]
  have hf₀ {n : ℕ} (hn : n ∈ S) : 0 < f n := Nat.pos_of_dvd_of_pos (hf_dvd hn) hM
  have hf_inj : Set.InjOn f (↑S : Set ℕ) := by
    have hmul {n : ℕ} (hn : n ∈ S) : f n * n = M * r := by
      calc
        _ = (M / n * n) * r := mul_right_comm ..
        _ = _ := by rw [Nat.div_mul_cancel (hn_dvd hn)]
    intro a ha b hb hab
    apply Nat.mul_left_cancel (hf₀ ha)
    rw [hmul ha, hab, hmul hb]
  have hf_totient {n : ℕ} (hn : n ∈ S) : (f n).totient = (M / n) * r.totient := by
    have hpf : (f n).primeFactors = r.primeFactors := by
      apply Subset.antisymm
      · exact (Nat.primeFactors_mono (hf_dvd hn) hM.ne').trans_eq
          (Nat.primeFactors_pow r hN.ne')
      · exact Nat.primeFactors_mono (dvd_mul_left r (M / n)) (hf₀ hn).ne'
    have hrt : r.totient = ∏ p ∈ r.primeFactors, (p - 1) := by
      rw [Nat.totient_eq_div_primeFactors_mul r, Nat.prod_primeFactors_of_squarefree hr,
        Nat.div_self hr₀, one_mul]
    rw [Nat.totient_eq_div_primeFactors_mul (f n), hpf, Nat.prod_primeFactors_of_squarefree hr, hrt]
    change (M / n * r / r) * _ = _
    rw [Nat.mul_div_cancel _ hr₀]
  have hsum : (∑ n ∈ S, ((f n).totient : ℝ)) ≤ (M : ℝ) := by
    rw [← Finset.sum_image (f := fun d : ℕ ↦ (d.totient : ℝ)) hf_inj]
    calc
      _ ≤ ∑ d ∈ M.divisors, (d.totient : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun d _ _ ↦ by positivity)
        rintro d hd
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hd
        exact Nat.mem_divisors.mpr ⟨hf_dvd hn, hM.ne'⟩
      _ = _ := by exact_mod_cast Nat.sum_totient M
  have hMφ : 0 < (M : ℝ) * (r.totient : ℝ) :=
    mul_pos (by exact_mod_cast hM) (by exact_mod_cast Nat.totient_pos.mpr hr₀)
  change (∑ n ∈ S, (n : ℝ)⁻¹) ≤ _
  calc
    _ = (∑ n ∈ S, ((f n).totient : ℝ)) / ((M : ℝ) * (r.totient : ℝ)) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hn₀ : (n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hn).1).1
      rw [hf_totient hn, Nat.cast_mul, Nat.cast_div (hn_dvd hn) hn₀]
      field_simp
    _ ≤ (M : ℝ) / ((M : ℝ) * (r.totient : ℝ)) := div_le_div_of_nonneg_right hsum hMφ.le
    _ = _ := by
      have hM₀ : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp

private theorem sum_cutoff_inv_le_J {Z : ℤ} (hZ : 1 ≤ Z) :
    (∑ n ∈ cutoff Z, (n : ℝ)⁻¹) ≤ J Z := by
  have hN : 0 < Z.toNat := by omega
  have hrad (n : ℕ) (hn : n ∈ cutoff Z) : rad n ∈ cutoff Z := by
    obtain ⟨hn₁, hn₂⟩ := mem_Icc.mp hn
    have hr₀ := Nat.pos_of_ne_zero (Nat.squarefree_prod_primeFactors n).ne_zero
    exact mem_Icc.mpr ⟨hr₀, (Nat.le_of_dvd hn₁ (Nat.prod_primeFactors_dvd n)).trans hn₂⟩
  rw [← Finset.sum_fiberwise_of_maps_to hrad (fun n ↦ (n : ℝ)⁻¹), J]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  by_cases hr : Squarefree r
  · have hμ : (μ r : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr
    simpa only [cutoff, hμ, one_div] using sum_rad_fiber_le hN hr
  · have hS : (cutoff Z).filter (fun n ↦ rad n = r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      exact hr ((mem_filter.mp hn).2 ▸ Nat.squarefree_prod_primeFactors n)
    rw [hS, sum_empty]
    positivity

private theorem sum_int_Icc_inv_eq {Z : ℤ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Icc (1 : ℤ) Z, (n : ℝ)⁻¹) = ∑ n ∈ cutoff Z, (n : ℝ)⁻¹ := by
  rw [← cutoff_image_int hZ, Finset.sum_image (g := fun j : ℕ ↦ (j : ℤ))
    (fun _ _ _ _ h ↦ Int.ofNat.inj h)]
  simp only [Int.cast_natCast]

/-- The finite Selberg normalizer dominates the harmonic sum over `1, …, Z`. -/
public theorem sum_inv_le_J {Z : ℤ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Icc (1 : ℤ) Z, (n : ℝ)⁻¹) ≤ J Z := by
  rw [sum_int_Icc_inv_eq hZ]
  exact sum_cutoff_inv_le_J hZ

/-- The same harmonic sum bounds the logarithm at the integer cutoff plus one. -/
public theorem log_add_one_le_sum_inv {Z : ℤ} (hZ : 1 ≤ Z) :
    Real.log ((Z : ℝ) + 1) ≤ ∑ n ∈ Icc (1 : ℤ) Z, (n : ℝ)⁻¹ := by
  rw [sum_int_Icc_inv_eq hZ]
  have hcast : (Z.toNat : ℝ) = (Z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ Z by omega)
  simpa only [cutoff, Nat.cast_add, Nat.cast_one, hcast, harmonic_eq_sum_Icc,
    Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using log_add_one_le_harmonic Z.toNat

/-- At the original real cutoff, the logarithm is bounded by the normalizer
with summation up to `⌊z⌋`. -/
public theorem log_le_J_floor {z : ℝ} (hz : 1 ≤ z) : Real.log z ≤ J ⌊z⌋ := by
  have hZ : (1 : ℤ) ≤ ⌊z⌋ := Int.le_floor.mpr (by simpa only [Int.cast_one] using hz)
  calc
    Real.log z ≤ Real.log ((⌊z⌋ : ℤ) + (1 : ℝ)) :=
      Real.log_le_log (zero_lt_one.trans_le hz) (Int.lt_floor_add_one z).le
    _ ≤ ∑ n ∈ Icc (1 : ℤ) ⌊z⌋, (n : ℝ)⁻¹ := log_add_one_le_sum_inv hZ
    _ ≤ J ⌊z⌋ := sum_inv_le_J hZ

end SelbergIntervalDiagonal
