module

public import Lemmas.AdeleRestrictedProductMeasure

import Lemmas.ArchimedeanAdeleTrace
import Theorems.FiniteBoxDiagonalCoset
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Integral lattice and finite coset coordinates for additive adelic reduction -/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical InnerProductSpace Masullo.AdeleStage nonZeroDivisors

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "A" => AdeleRing (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "A∞" => InfiniteAdeleRing K
local notation "X" => mixedEmbedding.euclidean.mixedSpace K
local notation "M" => mixedEmbedding.euclidean.toMixed K
local notation "e" => archimedeanEuclideanToAdele K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K

/-- The full real basis induced by the integral basis, in the unscaled Euclidean coordinates. -/
public def archimedeanIntegerBasis :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ X :=
  (mixedEmbedding.latticeBasis K).map (M).symm.toLinearEquiv

/-- The integral span of that basis is the lattice of the unit fractional ideal. -/
public theorem span_archimedeanIntegerBasis :
    Submodule.span ℤ (range (archimedeanIntegerBasis K)) = archimedeanIdealLattice K 1 := by
  classical
  have hrange : range (archimedeanIntegerBasis K) = (M).symm '' range (mixedEmbedding.latticeBasis K) :=
    (range_comp (M).symm (mixedEmbedding.latticeBasis K))
  let m := (M).symm.toLinearEquiv.restrictScalars ℤ
  change range (archimedeanIntegerBasis K) = m '' range (mixedEmbedding.latticeBasis K) at hrange
  ext x
  rw [hrange, ← LinearEquiv.coe_coe, ← Submodule.map_span, Submodule.mem_map_equiv]
  change M x ∈ Submodule.span ℤ (range (mixedEmbedding.latticeBasis K)) ↔ _
  rw [mixedEmbedding.mem_span_latticeBasis]
  rw [mem_archimedeanIdealLattice]
  simp only [Units.val_one, SetLike.mem_coe, FractionalIdeal.mem_one_iff, exists_exists_eq_and]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (M).injective (by simpa [archimedeanEuclideanEmbedding] using hz)⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa [archimedeanEuclideanEmbedding] using congrArg M hz⟩

/-- Transport the half-open coordinate cell to the actual infinite adele ring. -/
@[expose] public def archimedeanIntegralCell : Set A∞ :=
  e '' ZSpan.fundamentalDomain (archimedeanIntegerBasis K)

public theorem measurableSet_archimedeanIntegralCell : MeasurableSet (archimedeanIntegralCell K) :=
  (e).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
    (ZSpan.fundamentalDomain_measurableSet _)

/-- Reduce the infinite adele by a unique ring integer, using signed coordinates in the
full real basis, not absolute values indexed by the infinite places. -/
public theorem existsUnique_sub_integer_mem_archimedeanIntegralCell (x : A∞) :
    ∃! z : 𝓞 K, x - algebraMap K A∞ (algebraMap (𝓞 K) K z) ∈ archimedeanIntegralCell K := by
  let b := archimedeanIntegerBasis K
  let L := Submodule.span ℤ (range b)
  have hL (y : X) : y ∈ L ↔ ∃ z : 𝓞 K,
      archimedeanEuclideanEmbedding K (algebraMap (𝓞 K) K z) = y := by
    rw [show L = archimedeanIdealLattice K 1 from span_archimedeanIntegerBasis K,
      mem_archimedeanIdealLattice]
    simp only [Units.val_one, SetLike.mem_coe, FractionalIdeal.mem_one_iff, exists_exists_eq_and]
  have hcell (z : 𝓞 K) :
      x - algebraMap K A∞ (algebraMap (𝓞 K) K z) ∈ archimedeanIntegralCell K ↔
        -archimedeanEuclideanEmbedding K (algebraMap (𝓞 K) K z) + (e).symm x ∈
          ZSpan.fundamentalDomain b := by
    change x - algebraMap K A∞ (algebraMap (𝓞 K) K z) ∈
      (e).toEquiv '' ZSpan.fundamentalDomain b ↔ _
    rw [mem_image_equiv]
    change (e).symm (x - algebraMap K A∞ (algebraMap (𝓞 K) K z)) ∈ _ ↔ _
    rw [map_sub, ← euclideanToAdele_embedding, ContinuousAddEquiv.symm_apply_apply, sub_eq_neg_add]
  obtain ⟨v, hv, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b ((e).symm x)
  obtain ⟨z, hz⟩ := (hL (- (v : X))).mp (L.neg_mem v.property)
  have hv' : (v : X) + (e).symm x ∈ ZSpan.fundamentalDomain b := hv
  refine ⟨z, (hcell z).mpr (by simpa [hz] using hv'), fun w hw ↦ ?_⟩
  let v' : L := ⟨-archimedeanEuclideanEmbedding K (algebraMap (𝓞 K) K w),
    L.neg_mem ((hL _).mpr ⟨w, rfl⟩)⟩
  have he : v' = v := huniq v' ((hcell w).mp hw)
  have he' := congrArg (fun t : L ↦ - (t : X)) he
  have he'' : archimedeanEuclideanEmbedding K (algebraMap (𝓞 K) K w) =
      archimedeanEuclideanEmbedding K (algebraMap (𝓞 K) K z) := by
    simpa [v', hz] using he'
  apply RingOfIntegers.coe_injective
  apply (algebraMap K A∞).injective
  simpa only [euclideanToAdele_embedding] using congrArg e he''

/-- First reduce the finite coordinates. The remaining possible translations differ from
this choice by exactly a global integer. -/
public theorem exists_finiteIntegral_diagonalCoset (a : A) :
    ∃ r : K, ∀ q : K,
      (∀ v : V, (a - algebraMap K A q).2 v ∈ v.adicCompletionIntegers K) ↔
        ∃ z : 𝓞 K, q - r = algebraMap (𝓞 K) K z := by
  obtain ⟨r, hr⟩ := exists_finiteBox_diagonalCoset a.2 (1 : Fˣ)
  have hone : finiteIdeleIdeal K (1 : Fˣ) = 1 :=
    (finiteIdeleIdeal_eq_one_iff _).2 (fun _ ↦ Valuation.map_one _)
  refine ⟨r, fun q ↦ ?_⟩
  have hh := hr q
  rw [hone] at hh
  change _ ↔ q - r ∈ (1 : J) at hh
  rw [FractionalIdeal.mem_one_iff] at hh
  have hval (v : V) : (a - algebraMap K A q).2 v ∈ v.adicCompletionIntegers K ↔
      Valued.v (algebraMap K (v.adicCompletion K) q - a.2 v) ≤ Valued.v ((1 : Fˣ).val v) := by
    change Valued.v (a.2 v - algebraMap K (v.adicCompletion K) q) ≤ 1 ↔ _
    rw [show (1 : Fˣ).val v = 1 from rfl, Valuation.map_one, ← neg_sub (a.2 v), Valuation.map_neg]
  simpa only [hval, eq_comm (a := q - r)] using hh

end

end Masullo
