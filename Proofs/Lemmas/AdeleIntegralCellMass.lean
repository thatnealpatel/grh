module

public import Lemmas.AdeleIntegralCell

import Lemmas.FiniteCompletionCompact
import Theorems.FiniteBoxCenteredMass
import Theorems.FiniteIdeleIdeal

/-! # Exact mass of each factor of the additive adelic cell -/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical ENNReal InnerProductSpace Masullo.AdeleStage Pointwise

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "τ" => archimedeanTraceMeasure K
local notation "e" => archimedeanEuclideanToAdele K
local notation "c" => ZLattice.covolume (archimedeanIdealLattice K 1) τ

/-- The Archimedean cell has the positive finite mass of the unit ideal lattice covolume. -/
public theorem archimedeanIntegralCell_traceMass :
    ((τ).map e (archimedeanIntegralCell K)).toReal = c ∧
      (τ).map e (archimedeanIntegralCell K) ≠ ⊤ := by
  have hm' := (e).toHomeomorph.measurableEmbedding
  change MeasurableEmbedding (e : _ → _) at hm'
  rw [archimedeanIntegralCell, hm'.map_apply, preimage_image_eq _ hm'.injective]
  let : (τ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul volume (by simp) (by finiteness)
  have hD := ZSpan.isAddFundamentalDomain (archimedeanIntegerBasis K) τ
  rw [span_archimedeanIntegerBasis] at hD
  exact ⟨(ZLattice.covolume_eq_measure_fundamentalDomain _ _ hD).symm,
    ne_top_of_le_ne_top (archimedeanIntegerBasis K).parallelepiped.isCompact.measure_ne_top
      (measure_mono (ZSpan.fundamentalDomain_subset_parallelepiped _))⟩

/-- The finite factor on a stage containing all mass exceptions is finite and has
real mass the reciprocal of the Archimedean trace covolume of the unit ideal. -/
public theorem finiteIntegerBox_stageMass (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionIntegerMass K v = 1) :
    (∏ v ∈ S, finiteCompletionIntegerMass K v).toReal = c⁻¹ ∧
      (∏ v ∈ S, finiteCompletionIntegerMass K v) ≠ ⊤ := by
  have hone : finiteIdeleIdeal K (1 : Fˣ) = 1 :=
    (finiteIdeleIdeal_eq_one_iff _).2 (fun _ ↦ Valuation.map_one _)
  have heq (v : V) : (1 : F) v = 1 := rfl
  have hf := (finiteBox_centeredMass_finprod (1 : Fˣ)).2
  simp only [Units.val_one, heq, one_smul, hone, Measure.real] at hf
  have hsupp : Function.mulSupport (fun v : V ↦ (finiteCompletionIntegerMass K v).toReal) ⊆ ↑S := by
    intro v hv
    by_contra hvS
    exact hv (by simp [hS v hvS])
  refine ⟨?_, ENNReal.prod_ne_top (fun v _ ↦ ?_)⟩
  · rw [ENNReal.toReal_prod, ← finprod_eq_prod_of_mulSupport_subset _ hsupp]
    exact hf
  · exact (isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v) :
      IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K))).measure_ne_top

end

end Masullo
