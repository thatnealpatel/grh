module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

import Lemmas.PadicBallPartition
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Normalized additive Haar on `ℚ_[p]`

Definition A.3.1.2(3) and Example A.3.1.7, pp. 556–558, normalize
additive Haar to give `ℤ_[p]` mass one. Counting residue classes
calibrates the masses of its dilates for the rational case of (A.3.1.4).
-/

open scoped Padic ENNReal
open MeasureTheory Set

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

/-- The measurable sets of `ℚ_[p]` are its Borel sets. -/
public noncomputable scoped instance padicBorelMeasurableSpace : MeasurableSpace ℚ_[p] := borel _

public scoped instance padicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

local notation "B[" q "]" => Set.ofPred (fun x : ℚ_[q] ↦ ‖x‖ ≤ 1)

private theorem padicIntegralBall_eq_closedBall : B[p] = Metric.closedBall 0 1 := by
  ext x
  simp [Metric.mem_closedBall, dist_eq_norm]

private def padicIntegralCompact : TopologicalSpace.PositiveCompacts ℚ_[p] where
  carrier := B[p]
  isCompact' := by
    rw [padicIntegralBall_eq_closedBall p]
    exact isCompact_closedBall _ _
  interior_nonempty' := by
    rw [padicIntegralBall_eq_closedBall p,
      (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).interior_eq]
    exact ⟨0, Metric.mem_closedBall_self zero_le_one⟩

/-- Additive Haar measure on `ℚ_[p]`, normalized by the integral ball. -/
public noncomputable def padicAddHaar : Measure ℚ_[p] :=
  Measure.addHaarMeasure (padicIntegralCompact p)

public instance : (padicAddHaar p).IsAddHaarMeasure := by
  unfold padicAddHaar
  infer_instance

/-- The `p`-adic integers have mass one for the normalized additive Haar measure. -/
public theorem padicAddHaar_integralBall : padicAddHaar p B[p] = 1 :=
  Measure.addHaarMeasure_self (K₀ := padicIntegralCompact p)

private theorem padic_prime_pow_ne_zero (n : ℕ) : (p : ℚ_[p]) ^ n ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))

private noncomputable def padicInvDilation (n : ℕ) : ℚ_[p] ≃ₜ+ ℚ_[p] :=
  ContinuousAddEquiv.mulLeft (Units.mk0 _ (inv_ne_zero (padic_prime_pow_ne_zero p n)))

/-- Pushing additive Haar forward by multiplication by `p^(-n)` scales the
measure by `p^(-n)`: The preimage of the unit ball has index `p^n` in it. -/
public theorem padicAddHaar_map_inv_pow (n : ℕ) :
    Measure.map (fun x : ℚ_[p] ↦ ((p : ℚ_[p]) ^ n)⁻¹ * x) (padicAddHaar p) =
      ((p : ℝ≥0∞) ^ n)⁻¹ • padicAddHaar p := by
  let e := padicInvDilation p n
  let μ := Measure.map e (padicAddHaar p)
  have : μ.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map _ e
  change μ = _
  calc
    μ = μ B[p] • padicAddHaar p := Measure.addHaarMeasure_unique μ (padicIntegralCompact p)
    _ = _ := by
      have hB : MeasurableSet B[p] := (padicIntegralCompact p).isCompact.isClosed.measurableSet
      change Measure.map e (padicAddHaar p) B[p] • padicAddHaar p = _
      have he : Measurable (e : ℚ_[p] → ℚ_[p]) := e.continuous.measurable
      rw [Measure.map_apply he hB]
      have hmass := padic_measure_dilatedBall p _ (padicAddHaar_integralBall p) n
      change padicAddHaar p (e ⁻¹' B[p]) = _ at hmass
      rw [hmass]

private theorem image_mul_integralBall (a : ℚ_[p]) (ha : a ≠ 0) :
    (fun x : ℚ_[p] ↦ a * x) '' B[p] = {x | ‖x‖ ≤ ‖a‖} := by
  ext x
  change (∃ y, ‖y‖ ≤ 1 ∧ a * y = x) ↔ ‖x‖ ≤ ‖a‖
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg a) hy
  · intro hx
    refine ⟨x / a, ?_, ?_⟩
    · rwa [norm_div, div_le_one₀ (norm_pos_iff.mpr ha)]
    · rw [mul_comm, div_mul_cancel₀ _ ha]

private theorem padicAddHaar_dilate_nat_pow (n : ℕ) :
    padicAddHaar p ((fun x : ℚ_[p] ↦ (p : ℚ_[p]) ^ n * x) '' B[p]) =
      ((p : ℝ≥0∞) ^ n)⁻¹ := by
  have h := padic_measure_dilatedBall p _ (padicAddHaar_integralBall p) n
  rw [image_mul_integralBall p _ (padic_prime_pow_ne_zero p n)]
  convert h using 2
  ext x
  change ‖x‖ ≤ ‖(p : ℚ_[p]) ^ n‖ ↔ ‖((p : ℚ_[p]) ^ n)⁻¹ * x‖ ≤ 1
  rw [mul_comm, ← div_eq_mul_inv, norm_div, div_le_one₀]
  exact norm_pos_iff.mpr (padic_prime_pow_ne_zero p n)

private theorem padicAddHaar_dilate_inv_pow (n : ℕ) :
    padicAddHaar p ((fun x : ℚ_[p] ↦ ((p : ℚ_[p]) ^ n)⁻¹ * x) '' B[p]) =
      (p : ℝ≥0∞) ^ n := by
  let e := (padicInvDilation p n).toHomeomorph.toMeasurableEquiv
  let c := (p : ℝ≥0∞) ^ n
  have hmap : Measure.map e (padicAddHaar p) = c⁻¹ • padicAddHaar p :=
    padicAddHaar_map_inv_pow p n
  have hmass : c⁻¹ * padicAddHaar p (e '' B[p]) = 1 := by
    change (c⁻¹ • padicAddHaar p) (e '' B[p]) = 1
    rw [← hmap, e.map_apply]
    change padicAddHaar p (e.toEquiv ⁻¹' (e.toEquiv '' B[p])) = 1
    rw [e.toEquiv.preimage_image, padicAddHaar_integralBall]
  have hc₀ : c ≠ 0 := pow_ne_zero _ (by simp [NeZero.ne p])
  have hc : c ≠ ∞ := by simp [c]
  change padicAddHaar p (e '' B[p]) = c
  calc
    _ = c * (c⁻¹ * padicAddHaar p (e '' B[p])) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hc₀ hc, one_mul]
    _ = c := by rw [hmass, mul_one]

/-- The dilate `a ℤ_[p]` of the integral ball has additive Haar mass `‖a‖`.
This includes balls larger than the integral ball. -/
public theorem padicAddHaar_dilate_integralBall (a : ℚ_[p]) (ha : a ≠ 0) :
    padicAddHaar p ((fun x : ℚ_[p] ↦ a * x) '' B[p]) = ENNReal.ofReal ‖a‖ := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  let b := (p : ℚ_[p]) ^ a.valuation
  have hb : b ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  have hnorm : ‖a‖ = ‖b‖ := (Padic.norm_eq_zpow_neg_valuation ha).trans (Padic.norm_p_zpow _).symm
  have hball : (fun x : ℚ_[p] ↦ a * x) '' B[p] = (fun x : ℚ_[p] ↦ b * x) '' B[p] := by
    rw [image_mul_integralBall p a ha, image_mul_integralBall p b hb, hnorm]
  rw [hball, hnorm]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg a.valuation
  · have hb' : b = (p : ℚ_[p]) ^ n := by
      dsimp [b]
      rw [hn, zpow_natCast]
    rw [hb', padicAddHaar_dilate_nat_pow, norm_pow, Padic.norm_p, inv_pow,
      ENNReal.ofReal_inv_of_pos (pow_pos hp n), ENNReal.ofReal_pow hp.le, ENNReal.ofReal_natCast]
  · have hb' : b = ((p : ℚ_[p]) ^ n)⁻¹ := by
      dsimp [b]
      rw [hn, zpow_neg, zpow_natCast]
    rw [hb', padicAddHaar_dilate_inv_pow, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv,
      ENNReal.ofReal_pow hp.le, ENNReal.ofReal_natCast]

end Masullo
