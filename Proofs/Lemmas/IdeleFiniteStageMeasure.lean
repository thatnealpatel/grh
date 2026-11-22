module

public import Lemmas.FiniteCompletionCompact
public import Theorems.IdeleFiniteStage
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.LinearAlgebra.Countable
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-! # Local product measures in finite idele stages -/

open IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped ENNReal RestrictedProduct

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers K v
set_option quotPrecheck false in
local notation "A" => (Π v : InfinitePlace K, v.Completionˣ)
local notation "I" => IdeleGroup (𝓞 K) K

private theorem countable_numberField : Countable K := Countable.of_moduleFinite (R := ℚ)

public theorem countable_ideleFinitePlaces : Countable V := by
  classical
  let : Countable K := countable_numberField K
  let : Countable (𝓞 K) := Function.Injective.countable (RingOfIntegers.coe_injective (K := K))
  have h (J : Ideal (𝓞 K)) : ∃ s : Finset (𝓞 K), Ideal.span (s : Set (𝓞 K)) = J :=
    J.fg_of_isNoetherianRing
  choose gen hg using h
  apply Function.Injective.countable (f := gen ∘ HeightOneSpectrum.asIdeal)
  intro v w hvw
  change gen v.asIdeal = gen w.asIdeal at hvw
  exact HeightOneSpectrum.ext (by rw [← hg v.asIdeal, ← hg w.asIdeal, hvw])

local instance : Countable V := countable_ideleFinitePlaces K

private instance (v : V) : SecondCountableTopology (F v) := by
  let : Countable K := countable_numberField K
  let : SeparableSpace (F v) :=
    ⟨range (algebraMap K (F v)), countable_range _, v.denseRange_algebraMap K⟩
  infer_instance

private instance (v : InfinitePlace K) : SecondCountableTopology v.Completion := by
  rcases v.isReal_or_isComplex with h | h
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal h).toHomeomorph.secondCountableTopology
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex h).toHomeomorph.secondCountableTopology

private instance (v : InfinitePlace K) : LocallyCompactSpace v.Completion := by
  rcases v.isReal_or_isComplex with h | h
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex h).toHomeomorph.isClosedEmbedding.locallyCompactSpace

/-- The inclusion of integer units into the full multiplicative group at a finite place. -/
public noncomputable abbrev finiteCompletionUnitInclusion (v : V) : (O v)ˣ →* (F v)ˣ :=
  Units.map (ValuationSubring.subtype (O v)).toMonoidHom

local instance (v : V) : CompactSpace (O v)ˣ := compactSpace_finiteCompletionIntegralUnits K v

private instance (v : V) : LocallyCompactSpace (F v)ˣ := by
  let h := isOpenEmbedding_finiteCompletionIntegralUnits K v
  exact ({ carrier := range (finiteCompletionUnitInclusion K v)
           isCompact' := isCompact_range h.continuous
           interior_nonempty' := by rw [h.isOpen_range.interior_eq]; exact ⟨_, mem_range_self 1⟩ } : PositiveCompacts (F v)ˣ).locallyCompactSpace_of_group

private instance secondCountable_units (R : Type*) [Monoid R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology Rˣ := by
  let : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private instance (v : V) : SecondCountableTopology (O v)ˣ :=
  (isOpenEmbedding_finiteCompletionIntegralUnits K v).isEmbedding.secondCountableTopology

public scoped instance secondCountable_ideleFiniteStage (S : Finset V) :
    SecondCountableTopology (IdeleFiniteStage K S) := by
  change SecondCountableTopology (A × (((v : {v // v ∈ S}) → (F v.val)ˣ) ×
    ((v : {v // v ∉ S}) → (O v.val)ˣ)))
  infer_instance

public theorem nonempty_archimedeanUnitBoxes : Nonempty (PositiveCompacts A) := by
  infer_instance

public scoped instance locallyCompact_ideleFiniteStage (S : Finset V) :
    LocallyCompactSpace (IdeleFiniteStage K S) := by
  change LocallyCompactSpace (A × (((v : {v // v ∈ S}) → (F v.val)ˣ) ×
    ((v : {v // v ∉ S}) → (O v.val)ˣ)))
  infer_instance

public scoped instance t2Space_ideleGroup : T2Space I := by
  let : T2Space (FiniteAdeleRing (𝓞 K) K) :=
    show T2Space (Πʳ v : V, [F v, O v]) from inferInstance
  let : T2Space (InfiniteAdeleRing K) :=
    show T2Space ((v : InfinitePlace K) → v.Completion) from inferInstance
  let : T2Space (AdeleRing (𝓞 K) K) :=
    show T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) from inferInstance
  infer_instance

public scoped instance secondCountable_ideleGroup : SecondCountableTopology I := by
  let (S : Finset V) : SecondCountableTopology (range (ideleFiniteStageEmbedding K S)) :=
    (isOpenEmbedding_ideleFiniteStageEmbedding K S).isEmbedding.toHomeomorph.symm.secondCountableTopology
  exact secondCountableTopology_of_countable_cover
    (fun S ↦ (isOpenEmbedding_ideleFiniteStageEmbedding K S).isOpen_range)
    (iUnion_range_ideleFiniteStageEmbedding K)

/-- Archimedean box times all finite integer units, expressed in stage coordinates. -/
public noncomputable def stageUnitBox (B : PositiveCompacts A) (S : Finset V) :
    PositiveCompacts (IdeleFiniteStage K S) where
  carrier := (B : Set A) ×ˢ
    (univ.pi (fun v : {v // v ∈ S} ↦ range (finiteCompletionUnitInclusion K v.val)) ×ˢ univ)
  isCompact' := B.isCompact.prod ((isCompact_univ_pi fun v ↦
    isCompact_range (isOpenEmbedding_finiteCompletionIntegralUnits K v.val).continuous).prod
    isCompact_univ)
  interior_nonempty' := by
    have h := isOpen_set_pi finite_univ (fun (v : {v // v ∈ S}) _ ↦
      (isOpenEmbedding_finiteCompletionIntegralUnits K v.val).isOpen_range)
    rw [interior_prod_eq, interior_prod_eq, h.interior_eq, interior_univ]
    refine B.interior_nonempty.prod (Set.Nonempty.prod ⟨1, ?_⟩ univ_nonempty)
    exact fun v _ ↦ ⟨1, map_one _⟩

private noncomputable def infiniteUnitCoordinates (a : I) (v : InfinitePlace K) : v.Completionˣ where
  val := (a : AdeleRing (𝓞 K) K).1 v
  inv := (↑(a⁻¹) : AdeleRing (𝓞 K) K).1 v
  val_inv := congrArg (fun b : AdeleRing (𝓞 K) K ↦ b.1 v) a.mul_inv
  inv_val := congrArg (fun b : AdeleRing (𝓞 K) K ↦ b.1 v) a.inv_mul

private def calibrationSet (B : PositiveCompacts A) : Set I :=
  {a | infiniteUnitCoordinates K a ∈ (B : Set A) ∧
    ∀ v : V, (a : AdeleRing (𝓞 K) K).2 v ∈ (O v) ∧ (↑(a⁻¹) : AdeleRing (𝓞 K) K).2 v ∈ (O v)}

private theorem preimage_calibrationSet (B : PositiveCompacts A) (S : Finset V) :
    ideleFiniteStageEmbedding K S ⁻¹' calibrationSet K B = stageUnitBox K B S := by
  ext x
  let j := ideleFiniteStageEmbedding K S
  have ha : infiniteUnitCoordinates K (j x) = x.1 := funext fun v ↦
    Units.ext (ideleFiniteStageEmbedding_infinite K S x v)
  have hfin (v : V) (hv : v ∈ S) :
      (j x : AdeleRing (𝓞 K) K).2 v ∈ (O v) ∧ (↑((j x)⁻¹) : AdeleRing (𝓞 K) K).2 v ∈ (O v) ↔
        x.2.1 ⟨v, hv⟩ ∈ range (finiteCompletionUnitInclusion K v) := by
    rw [← map_inv j, ideleFiniteStageEmbedding_finite_mem K S x v hv,
      ideleFiniteStageEmbedding_finite_mem K S x⁻¹ v hv]
    let y := x.2.1 ⟨v, hv⟩
    change (y : F v) ∈ (O v) ∧ (↑(y⁻¹) : F v) ∈ (O v) ↔ _
    constructor
    · rintro ⟨hy, hi⟩
      exact ⟨⟨⟨y.val, hy⟩, ⟨y.inv, hi⟩, Subtype.ext y.mul_inv, Subtype.ext y.inv_mul⟩, Units.ext rfl⟩
    · rintro ⟨u, hu⟩
      change finiteCompletionUnitInclusion K v u = y at hu
      rw [← hu]
      exact ⟨u.val.property, u.inv.property⟩
  change (infiniteUnitCoordinates K (j x) ∈ (B : Set A) ∧ _) ↔
    x ∈ (B : Set A) ×ˢ (_ ×ˢ univ)
  simp only [ha, mem_prod, mem_univ, and_true, mem_pi]
  refine and_congr_right fun _ ↦ ⟨fun h v _ ↦ (hfin v.val v.property).mp (h v.val), fun h v ↦ ?_⟩
  by_cases hv : v ∈ S
  · exact (hfin v hv).mpr (h ⟨v, hv⟩ trivial)
  · exact (range_ideleFiniteStageEmbedding K S ▸ mem_range_self x) v hv

private theorem image_stageUnitBox (B : PositiveCompacts A) (S : Finset V) :
    ideleFiniteStageEmbedding K S '' (stageUnitBox K B S : Set (IdeleFiniteStage K S)) =
      calibrationSet K B := by
  rw [← preimage_calibrationSet]
  apply image_preimage_eq_of_subset
  intro a ha
  exact (range_ideleFiniteStageEmbedding K S).symm ▸ fun v _ ↦ ha.2 v

/-- The common calibration box: `B` at infinity, with integral units at every finite place. -/
public noncomputable def ideleCalibrationBox (B : PositiveCompacts A) : PositiveCompacts I :=
  let j := isOpenEmbedding_ideleFiniteStageEmbedding K ∅
  (stageUnitBox K B ∅).map _ j.continuous j.isOpenMap

/-- The same calibration box is obtained in the coordinates of every finite stage. -/
public theorem image_ideleStageUnitBox (B : PositiveCompacts A) (S : Finset V) :
    ideleFiniteStageEmbedding K S '' (stageUnitBox K B S : Set (IdeleFiniteStage K S)) =
      ideleCalibrationBox K B :=
  (image_stageUnitBox K B S).trans (image_stageUnitBox K B ∅).symm

section Measures

omit [NumberField K] in
/-- Local Haar measures at infinity are sigma-finite: The completion units
are second countable and locally compact. -/
public theorem archimedeanHaar_sigmaFinite [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
    (μa : (v : InfinitePlace K) → Measure v.Completionˣ) [∀ v, (μa v).IsHaarMeasure]
    (v : InfinitePlace K) : SigmaFinite (μa v) :=
  inferInstance

variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [mf : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [mu : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  (μa : (v : InfinitePlace K) → Measure v.Completionˣ)
  (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)ˣ)

/-- Exact unit mass of the given finite-place Haar measure; no rescaling. -/
public noncomputable def finiteCompletionUnitMass (v : V) : ℝ≥0∞ :=
  μf v (range (finiteCompletionUnitInclusion K v))

/-- Full Archimedean product, full finite factors in `S`, and restricted local
measures outside `S`. The latter must be probabilities for the infinite product. -/
public noncomputable def ideleFiniteStageProduct (S : Finset V) : Measure (IdeleFiniteStage K S) :=
  (Measure.pi μa).prod ((Measure.pi (fun v : {v // v ∈ S} ↦ μf v.val)).prod
    (Measure.infinitePi (fun v : {v // v ∉ S} ↦
      (μf v.val).comap (finiteCompletionUnitInclusion K v.val))))

variable [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [bf : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [bu : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]

public scoped instance borelSpace_ideleFiniteStage (S : Finset V) : BorelSpace (IdeleFiniteStage K S) := by
  change BorelSpace (A × (((v : {v // v ∈ S}) → (F v.val)ˣ) ×
    ((v : {v // v ∉ S}) → (O v.val)ˣ)))
  infer_instance

private noncomputable abbrev inactiveHaar (S : Finset V) (v : {v // v ∉ S}) : Measure (O v.val)ˣ :=
  (μf v.val).comap (finiteCompletionUnitInclusion K v.val)

omit ba ma in
private theorem inactiveHaar_probability (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1) (v : {v // v ∉ S}) :
    IsProbabilityMeasure (inactiveHaar K μf S v) := by
  constructor
  rw [(isOpenEmbedding_finiteCompletionIntegralUnits K v.val).measurableEmbedding.comap_apply,
    image_univ]
  exact hS v.val v.property

variable [ha : ∀ v, (μa v).IsHaarMeasure] [hf : ∀ v, (μf v).IsHaarMeasure]

omit ba ma in
private theorem inactiveProduct_isHaar (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1) :
    (Measure.infinitePi (inactiveHaar K μf S)).IsHaarMeasure := by
  let (v : {v // v ∉ S}) := inactiveHaar_probability K μf S hS v
  let (v : {v // v ∉ S}) : (inactiveHaar K μf S v).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) (μf v.val)
      (isOpenEmbedding_finiteCompletionIntegralUnits K v.val)
  let μ := Measure.infinitePi (inactiveHaar K μf S)
  have : μ.IsMulLeftInvariant := ⟨fun u ↦ by
    change (Measure.infinitePi _).map (fun w v ↦ u v * w v) = Measure.infinitePi _
    rw [Measure.infinitePi_map_pi _ (f := fun v w ↦ u v * w)
      (fun v ↦ (continuous_const_mul (u v)).measurable)]
    congr 1
    funext v
    exact map_mul_left_eq_self (inactiveHaar K μf S v) (u v)⟩
  have h := (Measure.haarMeasure_eq_iff (⊤ : PositiveCompacts ((v : {v // v ∉ S}) → (O v.val)ˣ)) μ).mpr
    (by rw [PositiveCompacts.coe_top, measure_univ])
  change μ.IsHaarMeasure
  rw [← h]
  infer_instance

/-- A stage product is Haar once every omitted finite unit mass is one. -/
public theorem ideleFiniteStageProduct_isHaar (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1) :
    (ideleFiniteStageProduct K μa μf S).IsHaarMeasure := by
  let : (Measure.infinitePi (inactiveHaar K μf S)).IsHaarMeasure := inactiveProduct_isHaar K μf S hS
  change ((Measure.pi μa).prod ((Measure.pi (fun v : {v // v ∈ S} ↦ μf v.val)).prod
    (Measure.infinitePi (inactiveHaar K μf S)))).IsHaarMeasure
  apply Measure.prod.instIsHaarMeasure

omit ba in
/-- Fubini for a grouped Archimedean density times the active finite factors.
The inactive unit coordinates integrate out with mass one. -/
public theorem ideleFiniteStageProduct_groupedTensor {L : Type*} [RCLike L]
    (S : Finset V) (hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1)
    (a : A → L)
    (f : (v : {v // v ∈ S}) → (F v.val)ˣ → L)
    (hA : Integrable a (Measure.pi μa)) (hF : ∀ v, Integrable (f v) (μf v.val)) :
    (Integrable (fun x : IdeleFiniteStage K S ↦ a x.1 * (∏ v, f v (x.2.1 v)))
      (ideleFiniteStageProduct K μa μf S)) ∧
    (∫ x : IdeleFiniteStage K S, a x.1 * (∏ v, f v (x.2.1 v))
      ∂ideleFiniteStageProduct K μa μf S) =
      (∫ x, a x ∂Measure.pi μa) * (∏ v, ∫ x, f v x ∂μf v.val) := by
  let (v : {v // v ∉ S}) := inactiveHaar_probability K μf S hS v
  let μu := Measure.infinitePi (inactiveHaar K μf S)
  let mF := Measure.pi (fun v : {v // v ∈ S} ↦ μf v.val)
  let ff (x : (v : {v // v ∈ S}) → (F v.val)ˣ) := ∏ v, f v (x v)
  have hFf : Integrable ff mF := Integrable.fintype_prod_dep hF
  change Integrable (fun x ↦ a x.1 * ff x.2.1) ((Measure.pi μa).prod (mF.prod μu)) ∧ _
  refine ⟨hA.mul_prod (hFf.comp_fst μu), ?_⟩
  have hf_tail : (∫ x, ff x.1 ∂mF.prod μu) = ∫ x, ff x ∂mF := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      (integral_fun_fst (μ := mF) (ν := μu) ff)
  calc
    _ = (∫ x, a x ∂Measure.pi μa) * (∫ x, ff x.1 ∂mF.prod μu) :=
      integral_prod_mul (μ := Measure.pi μa) (ν := mF.prod μu) a (fun x ↦ ff x.1)
    _ = (∫ x, a x ∂Measure.pi μa) * (∫ x, ff x ∂mF) := congrArg (_ * ·) hf_tail
    _ = _ := congrArg (_ * ·)
      (integral_fintype_prod_eq_prod (μ := fun v : {v // v ∈ S} ↦ μf v.val) f)

omit ha ba in
/-- The calibration mass in stage coordinates retains all active unit masses. -/
public theorem ideleFiniteStageProduct_unitBox (B : PositiveCompacts A) (S : Finset V)
    (hS : ∀ v ∉ S, finiteCompletionUnitMass K μf v = 1) :
    ideleFiniteStageProduct K μa μf S (stageUnitBox K B S) =
      Measure.pi μa B * ∏ v ∈ S, finiteCompletionUnitMass K μf v := by
  let (v : {v // v ∉ S}) := inactiveHaar_probability K μf S hS v
  change (Measure.pi μa).prod ((Measure.pi (fun v : {v // v ∈ S} ↦ μf v.val)).prod
    (Measure.infinitePi (inactiveHaar K μf S))) ((B : Set A) ×ˢ
      (univ.pi (fun v : {v // v ∈ S} ↦ range (finiteCompletionUnitInclusion K v.val)) ×ˢ univ)) = _
  rw [Measure.prod_prod, Measure.prod_prod, Measure.pi_pi, measure_univ, mul_one]
  exact congrArg (fun m ↦ Measure.pi μa B * m) (Finset.prod_attach S (finiteCompletionUnitMass K μf))

end Measures

end Masullo
