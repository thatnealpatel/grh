module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.GroupTheory.Index

/-! # Haar mass and finite relative index -/

open MeasureTheory Set
open scoped ENNReal

namespace Masullo

/-- The mass of an additive subgroup is its mass per coset times the finite relative index. -/
public theorem measure_eq_relIndex_mul {G : Type*} [AddGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (H L : AddSubgroup G) (hHL : H ≤ L)
    (hH : MeasurableSet (H : Set G)) (hL : MeasurableSet (L : Set G))
    [H.IsFiniteRelIndex L] (μ : Measure G) [μ.IsAddLeftInvariant] :
    μ L = (H.relIndex L : ℝ≥0∞) * μ H := by
  have hι : MeasurableEmbedding (L.subtype : L → G) := MeasurableEmbedding.subtype_coe hL
  have : MeasurableAdd L :=
    ⟨fun a ↦ Measurable.subtype_mk ((measurable_const_add (a : G)).comp hι.measurable),
      fun a ↦ Measurable.subtype_mk ((measurable_add_const (a : G)).comp hι.measurable)⟩
  let ν := μ.comap L.subtype
  have : ν.IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ hι
  have hsub : MeasurableSet (H.addSubgroupOf L : Set L) := hH.preimage hι.measurable
  have hm := (H.addSubgroupOf L).index_mul_measure hsub ν
  change (H.relIndex L : ℝ≥0∞) * ν ((L.subtype : L → G) ⁻¹' (H : Set G)) = ν univ at hm
  dsimp only [ν] at hm
  have hrange : range (L.subtype : L → G) = (L : Set G) := Subtype.range_val
  rw [hι.comap_preimage, hι.comap_apply, image_univ, hrange, inter_eq_left.mpr hHL] at hm
  exact hm.symm

end Masullo
