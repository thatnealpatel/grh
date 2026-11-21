module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The residue partition of the `p`-adic integral ball

The fibers of reduction modulo `p^n` are the translates of `p^n ℤ_[p]`
by the natural residue representatives. Thus each has `p^(-n)` of the
mass of the integral ball.
-/

open scoped Padic ENNReal
open MeasureTheory Set Function

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

local notation "B[" q "]" => Set.ofPred (fun x : ℚ_[q] ↦ ‖x‖ ≤ 1)
local notation "D[" q "," n "]" => Set.ofPred (fun x : ℚ_[q] ↦ ‖((q : ℚ_[q]) ^ n)⁻¹ * x‖ ≤ 1)

private theorem padic_residue_coset (n : ℕ) (j : ZMod (p ^ n)) (x : ℚ_[p]) :
    x - (j.val : ℚ_[p]) ∈ D[p,n] ↔
      ∃ a : ℤ_[p], (a : ℚ_[p]) = x ∧ PadicInt.toZModPow n a = j := by
  let d : ℤ_[p] := (p : ℤ_[p]) ^ n
  let r : ℤ_[p] := j.val
  let ρ := PadicInt.toZModPow (p := p) n
  have hd : (d : ℚ_[p]) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  have hr : ρ r = j := by simp [ρ, r]
  have hker : ∀ a : ℤ_[p], ρ a = 0 ↔ d ∣ a := by
    intro a
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  change ‖(d : ℚ_[p])⁻¹ * (x - (r : ℚ_[p]))‖ ≤ 1 ↔ _
  constructor
  · intro hx
    let t : ℤ_[p] := ⟨_, hx⟩
    refine ⟨r + d * t, ?_, ?_⟩
    · change (r : ℚ_[p]) + (d : ℚ_[p]) * ((d : ℚ_[p])⁻¹ * (x - (r : ℚ_[p]))) = x
      rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
      abel
    · show ρ (r + d * t) = j
      rw [map_add, map_mul, hr, (hker d).mpr (dvd_refl d), zero_mul, add_zero]
  · rintro ⟨a, rfl, ha⟩
    obtain ⟨t, ht⟩ : d ∣ a - r := (hker _).mp (by rw [map_sub, ha, hr, sub_self])
    rw [← PadicInt.coe_sub, ht, PadicInt.coe_mul, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    exact t.2

/-- Each residue coset has `p^(-n)` of the mass of the integral ball. -/
public theorem padic_measure_dilatedBall [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddRightInvariant] (hμ : μ B[p] = 1) (n : ℕ) :
    μ D[p,n] = ((p : ℝ≥0∞) ^ n)⁻¹ := by
  let C (j : ZMod (p ^ n)) := (fun x : ℚ_[p] ↦ x - (j.val : ℚ_[p])) ⁻¹' D[p,n]
  have hmem (j : ZMod (p ^ n)) (x : ℚ_[p]) : x ∈ C j ↔
      ∃ a : ℤ_[p], (a : ℚ_[p]) = x ∧ PadicInt.toZModPow n a = j :=
    padic_residue_coset p n j x
  have hcover : (⋃ j, C j) = B[p] := by
    ext x
    rw [mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨a, rfl, _⟩ := (hmem j x).mp hj
      exact a.2
    · intro hx
      let a : ℤ_[p] := ⟨x, hx⟩
      exact ⟨PadicInt.toZModPow n a, (hmem _ _).mpr ⟨a, rfl, rfl⟩⟩
  have hdisj : Pairwise (Disjoint on C) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hi hj ↦ hij ?_
    obtain ⟨a, ha, rfl⟩ := (hmem i x).mp hi
    obtain ⟨b, hb, rfl⟩ := (hmem j x).mp hj
    rw [PadicInt.coe_inj.mp (ha.trans hb.symm)]
  have hmeas (j : ZMod (p ^ n)) : MeasurableSet (C j) := by
    change MeasurableSet {x : ℚ_[p] | ‖((p : ℚ_[p]) ^ n)⁻¹ * (x - (j.val : ℚ_[p]))‖ ≤ 1}
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hmass (j : ZMod (p ^ n)) : μ (C j) = μ D[p,n] := by
    simpa only [C, sub_eq_add_neg] using measure_preimage_add_right μ (-(j.val : ℚ_[p])) D[p,n]
  have hsum : (p : ℝ≥0∞) ^ n * μ D[p,n] = 1 := by
    rw [← hcover, measure_iUnion hdisj hmeas] at hμ
    simpa [hmass, tsum_fintype, ZMod.card, nsmul_eq_mul, Nat.cast_pow] using hμ
  have hp : ((p : ℝ≥0∞) ^ n) ≠ 0 := pow_ne_zero _ (by simp [NeZero.ne p])
  have hfin : ((p : ℝ≥0∞) ^ n) ≠ ∞ := by simp
  calc
    μ D[p,n] = ((p : ℝ≥0∞) ^ n)⁻¹ * ((p : ℝ≥0∞) ^ n * μ D[p,n]) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hp hfin, one_mul]
    _ = _ := by rw [hsum, mul_one]

end Masullo
