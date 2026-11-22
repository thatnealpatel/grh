module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-! # Compact integer units at finite places

Masullo uses compact open subgroups in the restricted-product measure prescription
(p. 556) and uses the residue-field size in (A.3.2.4), p. 560. We identify the
residue field of the actual completion and obtain the needed compactness in its
given topology. No local Haar normalization enters these facts.
-/

open Ideal IsDedekindDomain IsLocalRing NumberField Set Topology
open scoped WithZero

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]
  (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "w" => (Valued.v : Valuation F ℤᵐ⁰)

private theorem mem_completionMaximalIdeal {x : O} :
    x ∈ maximalIdeal O ↔ w (x : F) < 1 :=
  Valuation.mem_maximalIdeal_iff F w

private noncomputable def integerResidue : 𝓞 K →+* ResidueField O :=
  (residue O).comp (algebraMap (𝓞 K) O)

private theorem integerResidue_eq_zero (a : 𝓞 K) :
    integerResidue K v a = 0 ↔ a ∈ v.asIdeal := by
  change residue O (algebraMap (𝓞 K) O a) = 0 ↔ _
  rw [residue_eq_zero_iff, mem_completionMaximalIdeal K v]
  change w ((algebraMap (𝓞 K) K a : K) : F) < 1 ↔ _
  rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap,
    v.intValuation_lt_one_iff_mem]

private theorem integerResidue_surjective : Function.Surjective (integerResidue K v) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨b, hb⟩ := (v.denseRange_algebraMap K).exists_dist_lt (x : F) one_pos
  rw [dist_comm, dist_eq_norm] at hb
  have hbx := Valued.toNormedField.norm_lt_one_iff.mp hb
  have hbval : v.valuation K b ≤ 1 := by
    rw [← v.valuedAdicCompletion_eq_valuation' b]
    change w (algebraMap K F b) ≤ 1
    simpa only [sub_add_cancel] using Valuation.map_add_le w hbx.le x.property
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hbval 1
  have hab : w (algebraMap K F (algebraMap (𝓞 K) K a) - algebraMap K F b) < 1 := by
    rw [← map_sub]
    exact (v.valuedAdicCompletion_eq_valuation' _).trans_lt (by simpa using ha)
  refine ⟨a, ?_⟩
  change residue O (algebraMap (𝓞 K) O a) = residue O x
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_completionMaximalIdeal K v]
  change w (algebraMap K F (algebraMap (𝓞 K) K a) - (x : F)) < 1
  rw [← sub_add_sub_cancel (algebraMap K F (algebraMap (𝓞 K) K a)) (algebraMap K F b) (x : F)]
  exact Valuation.map_add_lt w hab hbx

/-- The completion residue field is the quotient of the global integers by the prime at `v`. -/
public noncomputable def finiteCompletionResidueEquiv :
    (𝓞 K ⧸ v.asIdeal) ≃+* ResidueField O :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift v.asIdeal (integerResidue K v) fun a ha ↦
      (integerResidue_eq_zero K v a).2 ha)
    ⟨RingHom.lift_injective_of_ker_le_ideal _ _ fun a ha ↦
        (integerResidue_eq_zero K v a).1 (RingHom.mem_ker.1 ha),
      fun y ↦ by
        obtain ⟨a, ha⟩ := integerResidue_surjective K v y
        exact ⟨Ideal.Quotient.mk _ a, ha⟩⟩

/-- The equivalence uses the canonical map of global integers into the completion integers. -/
public theorem finiteCompletionResidueEquiv_mk (a : 𝓞 K) :
    finiteCompletionResidueEquiv K v (Ideal.Quotient.mk v.asIdeal a) =
      residue O (algebraMap (𝓞 K) O a) := by
  unfold finiteCompletionResidueEquiv
  change integerResidue K v a = _
  rfl

/-- The local integer ring in its completion topology is compact. -/
public theorem compactSpace_finiteCompletionIntegers : CompactSpace O := by
  have hcomplete : CompleteSpace O := (Valued.isClosed_valuationSubring F).completeSpace_coe
  have hfinite : Finite (ResidueField O) := Finite.of_surjective _
    (finiteCompletionResidueEquiv K v).surjective
  exact (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := F) (Γ₀ := ℤᵐ⁰)).2 ⟨hcomplete, (inferInstance : IsDiscreteValuationRing O), hfinite⟩

/-- The local integer units are compact with the value-and-inverse topology. -/
public theorem compactSpace_finiteCompletionIntegralUnits : CompactSpace Oˣ := by
  let := compactSpace_finiteCompletionIntegers K v
  infer_instance

/-- The integral units embed as an open subgroup of the full local multiplicative group. -/
public theorem isOpenEmbedding_finiteCompletionIntegralUnits :
    IsOpenEmbedding (Units.map (ValuationSubring.subtype O).toMonoidHom) := by
  refine ⟨(IsEmbedding.subtypeVal (p := (· ∈ O))).units_map, ?_⟩
  have hopen := Valued.isOpen_valuationSubring F (Γ₀ := ℤᵐ⁰)
  convert (hopen.preimage Units.continuous_val).inter
    (hopen.preimage (Units.continuous_val.comp continuous_inv)) using 1
  ext x
  change (∃ u : Oˣ, Units.map (ValuationSubring.subtype O).toMonoidHom u = x) ↔ (x : F) ∈ O ∧ (↑x⁻¹ : F) ∈ O
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.property, u.inv.property⟩
  · rintro ⟨hx, hi⟩
    exact ⟨⟨⟨x.val, hx⟩, ⟨x.inv, hi⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩,
      Units.ext rfl⟩

end Masullo
