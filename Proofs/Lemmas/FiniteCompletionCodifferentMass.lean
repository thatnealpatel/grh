module

public import Theorems.FiniteCompletionDifferentScale
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Lemmas.AddSubgroupHaarIndex
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Additive Haar mass of the local codifferent

The codifferent is a finite union of translates of the integer ring. Its
mass relative to the integers is the norm of the local different, the
arithmetic factor in Masullo's additive normalization (A.3.1.2).
-/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "R" => ℤ_[p]
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "C" =>
  ((differentIdeal R O : FractionalIdeal O⁰ F)⁻¹ : FractionalIdeal O⁰ F)
set_option quotPrecheck false in
local notation "D" => Submodule.traceDual R ℚ_[p] (1 : Submodule O F)
set_option quotPrecheck false in
local notation "I" => (O).toSubring.toAddSubgroup

attribute [local instance] finiteCompletion_moduleFinite finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree

private theorem integralLattice_le_traceDual : I ≤ (D).toAddSubgroup := by
  intro x hx
  have h := (finiteCompletionIntegersToTraceDual v ⟨x, hx⟩).property
  rw [coe_finiteCompletionIntegersToTraceDual] at h
  exact h

private theorem integralLattice_relIndex_traceDual :
    (I).relIndex (D).toAddSubgroup = v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v := by
  have hrange : (I).addSubgroupOf (D).toAddSubgroup =
      (LinearMap.range (finiteCompletionIntegersToTraceDual v)).toAddSubgroup := by
    ext x
    change (x : F) ∈ O ↔ ∃ y : O, finiteCompletionIntegersToTraceDual v y = x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, Subtype.ext (coe_finiteCompletionIntegersToTraceDual v ⟨x, hx⟩)⟩
    · rintro ⟨y, rfl⟩
      rw [coe_finiteCompletionIntegersToTraceDual]
      exact y.property
  rw [AddSubgroup.relIndex, hrange]
  exact finiteCompletion_card_traceDual_quotient v

/-- The integer lattice is contained in the codifferent. -/
public theorem finiteCompletion_integers_subset_codifferent : (O : Set F) ⊆ (C : Set F) := by
  change (I) ≤ (C : Submodule O F).toAddSubgroup
  rw [← finiteCompletion_traceDual_eq_inv_differentIdeal v]
  exact integralLattice_le_traceDual v

/-- Additive index of the integer ring in its actual codifferent. -/
public theorem finiteCompletion_codifferent_relIndex :
    (I).relIndex (C : Submodule O F).toAddSubgroup =
      v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v := by
  rw [← finiteCompletion_traceDual_eq_inv_differentIdeal v]
  exact integralLattice_relIndex_traceDual v

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

/-- The additive Haar mass of the codifferent is the integer-ring mass
multiplied by the norm of the local different. -/
public theorem finiteCompletion_codifferent_measure :
    μ (C : Set F) = (v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ) *
      μ (O : Set F) := by
  have hO : IsOpen (O : Set F) := Valued.isOpen_valuationSubring F
  have hle := integralLattice_le_traceDual v
  have hD := AddSubgroup.isOpen_mono hle hO
  have hindex := integralLattice_relIndex_traceDual v
  have : (I).IsFiniteRelIndex (D).toAddSubgroup := ⟨by
    rw [hindex]
    exact pow_ne_zero _ (fun h ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))⟩
  rw [← show (D : Set F) = (C : Set F) from
    congrArg (fun S : Submodule O F ↦ (S : Set F)) (finiteCompletion_traceDual_eq_inv_differentIdeal v)]
  change μ (D : Set F) = ((v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ) : ℝ≥0∞) *
    μ (I : Set F)
  rw [← hindex]
  exact measure_eq_relIndex_mul _ _ hle hO.measurableSet hD.measurableSet μ

/-- The same additive Haar mass comparison for real-valued measures. -/
public theorem finiteCompletion_codifferent_measureReal :
    μ.real (C : Set F) = (v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ) *
      μ.real (O : Set F) := by
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_natCast] using
    congrArg ENNReal.toReal (finiteCompletion_codifferent_measure v μ)

end Masullo
