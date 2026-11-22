module

public import Lemmas.AdeleRestrictedProductMeasure

import Lemmas.FiniteCompletionCompact
import Theorems.FiniteBoxCenteredMass

/-! # The restricted product of the normalized local additive Haar measures

Masullo's prescription on PDF p. 556, immediately before Definition A.3.1.2,
uses full local fields at the Archimedean and retained finite places and
integer rings elsewhere. The prescription states that each stage has the
product restriction, but its stage quantifier does not require all exceptions
to unit integer mass to lie in the retained set. The probability tail of our
checked stage product needs exactly that requirement. The local normalizations
are supplied by Definition A.3.1.2. Here we construct the global product
measure on that cofinal family by calibrating a single Haar measure against
the same integral-finite box in every stage. This constructs the right-hand
side of the first equality of Lemma A.3.1.3. The Borel uniqueness statement
comes from the countable cofinal cover, not Haar uniqueness upstairs.

The identification with the quotient-normalized measure of Definition
A.3.1.1, p. 555, and the separate S-local equality are not proved here.
Source reading: Provisional, from the pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace

namespace Masullo

open scoped AdeleStage ENNReal Pointwise

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v
local notation "A∞" => InfiniteAdeleRing K
local notation "A" => AdeleRing (𝓞 K) K

/-- In every number field the integer-mass exceptions form a finite set. -/
public theorem exists_finiteCompletionIntegerMass_exceptions :
    ∃ E : Finset V, ∀ v : V, v ∈ E ↔ finiteCompletionIntegerMass K v ≠ 1 := by
  classical
  -- Use the finite-support statement at radius one, not the totalized finprod value.
  have hsupp : {v : V | (finiteCompletionIntegerMass K v).toReal ≠ 1}.Finite := by
    have hone (v : V) : (1 : FiniteAdeleRing (𝓞 K) K) v = 1 := rfl
    simpa only [Function.HasFiniteMulSupport, Function.mulSupport, Units.val_one, hone, one_smul,
      finiteCompletionIntegerMass, Measure.real] using
      (finiteBox_centeredMass_finprod (1 : (FiniteAdeleRing (𝓞 K) K)ˣ)).1
  have hfinite (v : V) : finiteCompletionIntegerMass K v ≠ ⊤ :=
    (isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v) :
      IsCompact (O v : Set (F v))).measure_ne_top
  refine ⟨hsupp.toFinset, fun v ↦ ?_⟩
  rw [hsupp.mem_toFinset]
  change (finiteCompletionIntegerMass K v).toReal ≠ 1 ↔ finiteCompletionIntegerMass K v ≠ 1
  simpa only [ENNReal.toReal_one] using
    not_congr (ENNReal.toReal_eq_toReal_iff' (hfinite v) ENNReal.one_ne_top)

/-- There is a regular additive Haar measure on the adeles with the prescribed
local products on every stage containing `E`. These comaps characterize it
among all Borel measures, and its integral-finite rectangles retain exactly
the finite-place mass factors in `E`. Use
`exists_finiteCompletionIntegerMass_exceptions` to obtain `E` unconditionally. -/
public theorem exists_adeleRestrictedProductHaar (E : Finset V)
    (hE : ∀ v ∉ E, finiteCompletionIntegerMass K v = 1) :
    ∃ μ : Measure A, μ.IsAddHaarMeasure ∧ μ.Regular ∧
      (∀ ν : Measure A, ν = μ ↔ ∀ S : Finset V, E ⊆ S →
        ν.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S) ∧
      (∀ B : Set A∞, MeasurableSet B →
        μ (adeleIntegerRectangle K B) =
          ((archimedeanTraceMeasure K).map (archimedeanEuclideanToAdele K)) B *
            ∏ v ∈ E, finiteCompletionIntegerMass K v) := by
  classical
  let : LocallyCompactSpace A∞ :=
    (archimedeanEuclideanToAdele K).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let B : PositiveCompacts A∞ := Classical.choice inferInstance
  let Q := adeleCalibrationBox K B
  let c := adeleFiniteStageHaar K E (adeleStageIntegerBox K B E)
  let : (adeleFiniteStageHaar K E).IsAddHaarMeasure :=
    adeleFiniteStageHaar_isAddHaarMeasure K E hE
  -- Fix the upstairs Haar scale from the stage `E`. The whole box has positive, finite mass.
  have hc₀ : c ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ (adeleStageIntegerBox K B E).interior_nonempty).ne'
  have hcfin : c ≠ ⊤ := (adeleStageIntegerBox K B E).isCompact.measure_ne_top
  let μ := c • Measure.addHaarMeasure Q
  have hμ : μ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul _ hc₀ hcfin
  have hμQ : μ Q = c := by
    rw [smul_apply, Measure.addHaarMeasure_self, smul_eq_mul, mul_one]
  -- Compare the two additive Haar measures on each open stage by this same box.
  have hstage (S : Finset V) (hES : E ⊆ S) :
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S := by
    have hS : ∀ v ∉ S, finiteCompletionIntegerMass K v = 1 :=
      fun v hv ↦ hE v (fun he ↦ hv (hES he))
    let R := adeleStageIntegerBox K B S
    let : LocallyCompactSpace (AdeleFiniteStage K S) := R.locallyCompactSpace_of_addGroup
    have hleft : (μ.comap (adeleFiniteStageEmbedding K S)).IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ
        (f := adeleFiniteStageAddEmbedding K S) (isOpenEmbedding_adeleFiniteStageEmbedding K S)
    have hright := adeleFiniteStageHaar_isAddHaarMeasure K S hS
    have h₁ : μ.comap (adeleFiniteStageEmbedding K S) R = c := by
      rw [(measurableEmbedding_adeleFiniteStageEmbedding K S).comap_apply,
        image_adeleStageIntegerBox K B S, hμQ]
    have h₂ : adeleFiniteStageHaar K S R = c := by
      dsimp only [R, c]
      rw [coe_adeleStageIntegerBox, coe_adeleStageIntegerBox,
        adeleFiniteStageHaar_integerRectangle K B S hS,
        adeleFiniteStageHaar_integerRectangle K B E hE,
        Finset.prod_subset hES (fun v _ hv ↦ hE v hv)]
    calc
      μ.comap (adeleFiniteStageEmbedding K S) = c • Measure.addHaarMeasure R :=
        (Measure.addHaarMeasure_unique _ R).trans (congrArg (· • Measure.addHaarMeasure R) h₁)
      _ = adeleFiniteStageHaar K S :=
        ((Measure.addHaarMeasure_unique _ R).trans (congrArg (· • Measure.addHaarMeasure R) h₂)).symm
  refine ⟨μ, hμ, Measure.Regular.smul (μ := Measure.addHaarMeasure Q) hcfin, ?_, ?_⟩
  · intro ν
    refine ⟨fun h ↦ h.symm ▸ hstage, fun h ↦ ?_⟩
    -- A comap determines the restriction to its Borel range. These ranges are a countable cover.
    apply Measure.ext_of_iUnion_eq_univ (iUnion_range_adeleFiniteStageEmbedding K E)
    intro S
    let j := measurableEmbedding_adeleFiniteStageEmbedding K (E ∪ S)
    have hsub : E ⊆ E ∪ S := Finset.subset_union_left
    rw [← j.map_comap ν, ← j.map_comap μ, h _ hsub, hstage _ hsub]
  · intro D _
    let j := measurableEmbedding_adeleFiniteStageEmbedding K E
    rw [← image_adeleStageIntegerRectangle K D E, ← j.comap_apply, hstage E subset_rfl,
      adeleFiniteStageHaar_integerRectangle K D E hE]

end Masullo
