module

public import Lemmas.AdeleRestrictedProductMeasure
public import Lemmas.FinitePlaceSupport
public import Theorems.IdeleFiniteStage

import Lemmas.FiniteCompletionCompact
import Theorems.IdeleFiniteStageZetaDensity

/-! # Finite-stage calibration of additive dilation

Masullo states (A.3.1.4), PDF p. 556, and refers to another source for its
proof. We check the calibration-box comparison on the actual adeles from the
stage product in (A.3.1.3): Active places use the local integer-ball dilation
law, while integral units preserve the entire compact tail. The factor is the
idelic norm in (A.1.3.2)–(A.1.3.3), PDF p. 541. The Archimedean image law
remains an explicit input. This does not yet extend the comparison to arbitrary
ideles or Borel sets. Source reading: Provisional, from Markdown and PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped ENNReal RestrictedProduct

namespace Masullo

noncomputable section

open scoped AdeleStage

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v
local notation "A∞" => InfiniteAdeleRing K
local notation "A" => AdeleRing (𝓞 K) K
local notation "νarch" => (Measure.map (archimedeanEuclideanToAdele K) (archimedeanTraceMeasure K))

private theorem finiteCompletion_measure_image_integers (v : V) (u : (F v)ˣ) :
    finiteCompletionNormalizedHaar v ((fun x : F v ↦ (u : F v) * x) '' (O v : Set (F v))) =
      ENNReal.ofReal ‖(u : F v)‖ * finiteCompletionIntegerMass K v := by
  let a : F v := u
  let ν := finiteCompletionNormalizedHaar v
  let T := (fun x ↦ a * x) '' (O v : Set (F v))
  have hO : IsCompact (O v : Set (F v)) :=
    isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v)
  have hT : IsCompact T := hO.image (continuous_const.mul continuous_id)
  have hOtop : ν (O v : Set (F v)) ≠ ∞ := hO.measure_lt_top.ne
  have hTtop : ν T ≠ ∞ := hT.measure_lt_top.ne
  have hreal : (ν T).toReal = ‖a‖ * (ν (O v : Set (F v))).toReal :=
    finiteCompletionNormalizedHaar_real_smul_integers v a u.ne_zero
  change ν T = ENNReal.ofReal ‖a‖ * ν (O v : Set (F v))
  rw [← ENNReal.ofReal_toReal hTtop, hreal, ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_toReal hOtop]

private def stageMultiplier {S : Finset V} (u : IdeleFiniteStage K S) : AdeleFiniteStage K S :=
  ((ideleFiniteStageEmbedding K S u : A).1, (fun v ↦ (u.2.1 v : F v.val)),
    (fun v ↦ (u.2.2 v : O v.val)))

private theorem embed_stageMultiplier {S : Finset V} (u : IdeleFiniteStage K S) :
    adeleFiniteStageEmbedding K S (stageMultiplier K u) =
      (ideleFiniteStageEmbedding K S u : A) := by
  refine Prod.ext (adeleFiniteStageEmbedding_infinite K S (stageMultiplier K u))
    (FiniteAdeleRing.ext K fun v ↦ ?_)
  by_cases hv : v ∈ S
  · rw [adeleFiniteStageEmbedding_finite_mem K S _ v hv,
      ideleFiniteStageEmbedding_finite_mem K S u v hv]
    rfl
  · rw [adeleFiniteStageEmbedding_finite_notMem K S _ v hv,
      ideleFiniteStageEmbedding_finite_notMem K S u v hv]
    rfl

private theorem measure_image_stageIntegerBox {S : Finset V}
    (B : PositiveCompacts A∞) (u : IdeleFiniteStage K S)
    (hS : ∀ v ∉ S, finiteCompletionIntegerMass K v = 1) :
    adeleFiniteStageHaar K S ((fun x ↦ stageMultiplier K u * x) ''
      (adeleStageIntegerBox K B S : Set (AdeleFiniteStage K S))) =
      νarch ((fun x : A∞ ↦ (ideleFiniteStageEmbedding K S u : A).1 * x) '' (B : Set A∞)) *
        ((∏ v : {v // v ∈ S}, ENNReal.ofReal ‖(u.2.1 v : F v.val)‖) *
          ∏ v ∈ S, finiteCompletionIntegerMass K v) := by
  let := adeleFiniteStageOutside_isProbabilityMeasure K S hS
  -- Integral units act bijectively on the entire inactive product.
  let dOut (x : (v : {v // v ∉ S}) → O v.val) v := (u.2.2 v : O v.val) * x v
  let e : (v : {v // v ∉ S}) → (O v.val) ≃ (O v.val) := fun v ↦ (u.2.2 v).mulLeft
  have hOut : dOut '' univ = univ := by
    rw [image_univ]
    exact (Equiv.piCongrRight e).surjective.range_eq
  rw [coe_adeleStageIntegerBox, adeleStageIntegerRectangle]
  change adeleFiniteStageHaar K S
    (Prod.map ((ideleFiniteStageEmbedding K S u : A).1 * ·)
      (Prod.map (Pi.map (fun v a ↦ (u.2.1 v : F v.val) * a)) dOut) '' _) = _
  rw [prodMap_image_prod, prodMap_image_prod, piMap_image_univ_pi, hOut,
    adeleFiniteStageHaar, Measure.prod_prod, Measure.prod_prod, Measure.pi_pi,
    measure_univ, mul_one]
  simp only [finiteCompletion_measure_image_integers, Finset.prod_mul_distrib]
  exact congrArg (_ * ·) (congrArg (_ * ·) (Finset.prod_attach S (finiteCompletionIntegerMass K)))

/-- For the actual adelic calibration box, the stage-product comparison leaves only the
Archimedean image law as a local dilation input (Masullo (A.3.1.4), p. 556). -/
public theorem adeleCalibrationBox_image_idele_stage {S : Finset V} (B : PositiveCompacts A∞)
    (u : IdeleFiniteStage K S) (μ : Measure A)
    (hμ : μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    (hS : ∀ v ∉ S, finiteCompletionIntegerMass K v = 1)
    (hArch : let g := ideleFiniteStageEmbedding K S u;
      νarch ((fun x : A∞ ↦ (g : A).1 * x) '' (B : Set A∞)) =
        ENNReal.ofReal (∏ v : InfinitePlace K, ‖(g : A).1 v‖ ^ v.mult) * νarch B) :
    let g := ideleFiniteStageEmbedding K S u
    let Q := adeleCalibrationBox K B
    μ ((fun x : A ↦ (g : A) * x) '' (Q : Set A)) = ENNReal.ofReal (ideleNorm g) * μ Q := by
  dsimp only at hArch ⊢
  let g := ideleFiniteStageEmbedding K S u
  let j := adeleFiniteStageEmbedding K S
  have hj : MeasurableEmbedding j := measurableEmbedding_adeleFiniteStageEmbedding K S
  have hmul : (fun x : A ↦ (g : A) * x) ∘ j = j ∘ (fun x ↦ stageMultiplier K u * x) := by
    funext x
    change (g : A) * j x = j (stageMultiplier K u * x)
    rw [map_mul j, embed_stageMultiplier]
  -- The inactive norm factors are one in `ideleFiniteStage_norm`.
  have hnorm : ideleNorm g = (∏ v : InfinitePlace K, ‖(g : A).1 v‖ ^ v.mult) *
      (∏ v : {v // v ∈ S}, ‖(u.2.1 v : F v.val)‖) := by
    rw [ideleNorm_apply, ideleFiniteStage_norm K S u]
    congr 1
    exact Finset.prod_congr rfl (fun v _ ↦ by rw [ideleFiniteStageEmbedding_infinite])
  have harch_nonneg : 0 ≤ ∏ v : InfinitePlace K, ‖(g : A).1 v‖ ^ v.mult :=
    Finset.prod_nonneg fun v _ ↦ pow_nonneg (norm_nonneg _) _
  -- Compare both upstairs sets by the same comap, then multiply their local factors.
  rw [← image_adeleStageIntegerBox K B S, ← image_comp, hmul, image_comp,
    ← hj.comap_apply, ← hj.comap_apply, hμ, measure_image_stageIntegerBox K B u hS,
    coe_adeleStageIntegerBox, adeleFiniteStageHaar_integerRectangle K (B : Set A∞) S hS,
    hArch, hnorm, ENNReal.ofReal_mul harch_nonneg,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ norm_nonneg _)]
  ac_rfl

end

end Masullo
