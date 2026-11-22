module

public import Theorems.FiniteCompletionDifferentScale
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Lemmas.AddSubgroupHaarIndex
import Lemmas.FiniteCompletionCompact
import Lemmas.FiniteCompletionPrimePow

/-! # Normalized additive Haar measure at a finite place -/

open IsDedekindDomain MeasureTheory NumberField TopologicalSpace
open scoped ENNReal Pointwise WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

private noncomputable def finiteCompletionIntegersCompact : PositiveCompacts F where
  carrier := (O : Set F)
  isCompact' := isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v)
  interior_nonempty' := by
    have hO : IsOpen (O : Set F) := Valued.isOpen_valuationSubring F
    rw [hO.interior_eq]
    exact ⟨0, zero_mem _⟩

/-- The integer ring has positive real mass for every additive Haar measure. -/
public theorem finiteCompletionIntegers_measureReal_pos [MeasurableSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] : 0 < μ.real (O : Set F) := by
  let hO := finiteCompletionIntegersCompact v
  change 0 < μ.real (hO : Set F)
  exact ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior μ hO.interior_nonempty).ne'
    hO.isCompact.measure_lt_top.ne

local notation "scale" =>
  (Real.sqrt (v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ))⁻¹

private theorem finiteCompletionHaarScale_pos : 0 < scale := by
  have hq : 0 < v.asIdeal.absNorm :=
    Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  have hpow : 0 < (v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ) := pow_pos hq _
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hpow))

local notation "w" => (Valued.v : Valuation F ℤᵐ⁰)

private theorem mem_smul_finiteCompletionIntegers (a x : F) (ha : a ≠ 0) :
    x ∈ a • (O : Set F) ↔ w x ≤ w a := by
  change (∃ y ∈ (O : Set F), a * y = x) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [map_mul]
    exact mul_le_of_le_one_right zero_le (show w y ≤ 1 from hy)
  · intro hx
    refine ⟨a⁻¹ * x, ?_, mul_inv_cancel_left₀ ha x⟩
    change w (a⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, inv_mul_le_iff₀ (pos_iff_ne_zero.mpr ((map_ne_zero w).2 ha)), mul_one]
    exact hx

private theorem finiteCompletion_dilate_measureReal_of_integral [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0) (hint : w a ≤ 1) :
    μ.real (a • (O : Set F)) = ‖a‖ * μ.real (O : Set F) := by
  have hwa : w a ≠ 0 := (map_ne_zero w).2 ha
  have hlog : WithZero.log (w a) ≤ 0 := by
    simpa only [WithZero.log_one] using (WithZero.log_le_log hwa one_ne_zero).2 hint
  let n := (- WithZero.log (w a)).toNat
  have hn : WithZero.log (w a) = -(n : ℤ) := by
    rw [Int.toNat_of_nonneg (neg_nonneg.mpr hlog), neg_neg]
  have hval : w a = WithZero.exp (-(n : ℤ)) := by
    rw [← hn, WithZero.exp_log hwa]
  let J := (IsLocalRing.maximalIdeal O) ^ n
  let L := (O).toSubring.toAddSubgroup
  let e := ContinuousAddEquiv.mulLeft (Units.mk0 a ha)
  let H := L.map e.toAddEquiv.toAddMonoidHom
  have hH : (H : Set F) = a • (O : Set F) := rfl
  have hHL : H ≤ L := by
    intro x hx
    exact ((mem_smul_finiteCompletionIntegers v a x ha).mp hx).trans hint
  -- Work inside the integer ring: Its subgroup cut out by the dilate is a prime power.
  have hsub : H.addSubgroupOf L = J.toAddSubgroup := by
    ext x
    change (x : F) ∈ a • (O : Set F) ↔ (show O from x) ∈ J
    rw [mem_smul_finiteCompletionIntegers v a _ ha, mem_completionIdeal_pow_iff v, hval]
  have hindex : H.relIndex L = v.asIdeal.absNorm ^ n := by
    rw [AddSubgroup.relIndex, hsub]
    change Nat.card (O ⧸ J) = _
    rw [← Nat.card_congr (finiteCompletionPrimePowQuotientEquiv v n).toEquiv,
      ← Ideal.absNorm_eq_natCard, map_pow]
  have hq : v.asIdeal.absNorm ≠ 0 := mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot
  have : H.IsFiniteRelIndex L := ⟨by rw [hindex]; exact pow_ne_zero _ hq⟩
  have hLmeas : MeasurableSet (L : Set F) := (Valued.isOpen_valuationSubring F).measurableSet
  have hHmeas : MeasurableSet (H : Set F) :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image' hLmeas
  have hmass := measure_eq_relIndex_mul H L hHL hHmeas hLmeas μ
  rw [hindex, hH] at hmass
  change μ (O : Set F) = _ at hmass
  -- Both boxes are compact, and taking real parts preserves the finite index factor.
  have hreal : μ.real (O : Set F) =
      (v.asIdeal.absNorm ^ n : ℕ) * μ.real (a • (O : Set F)) := by
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_natCast] using
      congrArg ENNReal.toReal hmass
  have hnorm : ‖a‖ = ((v.asIdeal.absNorm ^ n : ℕ) : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def,
      WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v) hwa,
      hn, zpow_neg, zpow_natCast, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast, Nat.cast_pow]
  rw [hnorm, inv_mul_eq_div, eq_div_iff (Nat.cast_ne_zero.mpr (pow_ne_zero _ hq)), mul_comm]
  exact hreal.symm

-- Prove the dilation factor for arbitrary Haar so we can apply the integral case
-- to a pushforward.
private theorem finiteCompletion_dilate_measureReal [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0) :
    μ.real (a • (O : Set F)) = ‖a‖ * μ.real (O : Set F) := by
  by_cases hint : w a ≤ 1
  · exact finiteCompletion_dilate_measureReal_of_integral v μ a ha hint
  -- For a larger box, count the index of the integral dilate by `a⁻¹`
  -- in the pushforward of `μ` under multiplication by `a⁻¹`.
  let e := ContinuousAddEquiv.mulLeft (Units.mk0 a⁻¹ (inv_ne_zero ha))
  let ν := μ.map e
  have : ν.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ e
  have hia : w a⁻¹ ≤ 1 := by
    rw [map_inv₀, inv_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero w).2 ha))]
    exact (lt_of_not_ge hint).le
  have h := finiteCompletion_dilate_measureReal_of_integral v ν a⁻¹ (inv_ne_zero ha) hia
  have hp (S : Set F) : ν.real S = μ.real (e ⁻¹' S) := by
    change (μ.map e.toHomeomorph S).toReal = (μ (e.toHomeomorph ⁻¹' S)).toReal
    rw [e.toHomeomorph.measurableEmbedding.map_apply]
  have hpre (S : Set F) : e ⁻¹' S = a • S := by
    ext x
    change a⁻¹ * x ∈ S ↔ ∃ y ∈ S, a * y = x
    exact ⟨fun hx ↦ ⟨_, hx, mul_inv_cancel_left₀ ha x⟩, by
      rintro ⟨y, hy, rfl⟩
      simpa only [inv_mul_cancel_left₀ ha] using hy⟩
  rw [hp, hp, hpre, hpre, smul_smul, mul_inv_cancel₀ ha, one_smul, norm_inv] at h
  rw [← inv_mul_eq_iff_eq_mul₀ (norm_ne_zero_iff.mpr ha)]
  exact h.symm

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

/-- Additive Haar measure on the finite completion, scaled so that the integer ring has mass
equal to the inverse square root of the norm of the local different. -/
public noncomputable def finiteCompletionNormalizedHaar : Measure F :=
  ENNReal.ofReal scale • Measure.addHaarMeasure (finiteCompletionIntegersCompact v)

public instance finiteCompletionNormalizedHaar_isAddHaarMeasure :
    (finiteCompletionNormalizedHaar v).IsAddHaarMeasure := by
  unfold finiteCompletionNormalizedHaar
  exact Measure.IsAddHaarMeasure.smul _
    (ENNReal.ofReal_pos.mpr (finiteCompletionHaarScale_pos v)).ne' ENNReal.ofReal_ne_top

/-- The real mass of the finite-completion integers is the prescribed local different scale. -/
public theorem finiteCompletionNormalizedHaar_real :
    (finiteCompletionNormalizedHaar v).real (O : Set F) = scale := by
  let C := finiteCompletionIntegersCompact v
  change (ENNReal.ofReal scale * Measure.addHaarMeasure C C).toReal = scale
  rw [Measure.addHaarMeasure_self, mul_one,
    ENNReal.toReal_ofReal (finiteCompletionHaarScale_pos v).le]

/-- At every nonzero scale the actual normalized additive Haar mass of the
integer box is the norm of the scale times its calibrated mass. -/
public theorem finiteCompletionNormalizedHaar_real_smul_integers (a : F) (ha : a ≠ 0) :
    (finiteCompletionNormalizedHaar v).real (a • (O : Set F)) =
      ‖a‖ * (finiteCompletionNormalizedHaar v).real (O : Set F) :=
  finiteCompletion_dilate_measureReal v (finiteCompletionNormalizedHaar v) a ha

end Masullo
