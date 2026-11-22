module

public import Theorems.IdeleHeckeGaussian
public import Theorems.IdeleRestrictedProductHaar
public import Theorems.RationalIdeleHaarComparison
public import Theorems.RationalLocalMultiplicativeHaar
import all Lemmas.IdeleFiniteStageMeasure -- For the carrier of `stageUnitBox`.
import Theorems.RationalArchimedeanSchwartzMellin

/-! # Generic stage coordinates for rational idele Haar

The local Haar measures in (A.3.2.2) and (A.3.2.5), p. 560, calibrate
on the same positive finite-unit strip as the named upstairs measure.
The strip fixes the scalar, without restricting either sign in the stage.
-/

open IsDedekindDomain MeasureTheory NumberField InfinitePlace.Completion Set Topology TopologicalSpace
open scoped Masullo

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "Iℚ" => IdeleGroup (𝓞 ℚ) ℚ
local notation "F" v => HeightOneSpectrum.adicCompletion ℚ v
set_option quotPrecheck false in
local notation "A" => ((v : InfinitePlace ℚ) → v.Completionˣ)
local notation "ev" => (fun x : A ↦ x Rat.infinitePlace)
set_option quotPrecheck false in
local notation "c" => (fun u : Rat.infinitePlace.Completionˣ ↦
  extensionEmbeddingOfIsReal Rat.isReal_infinitePlace u.val)
local notation "J" => Icc (1 : ℝ) (Real.exp 1)
local notation "μa" => (fun v : InfinitePlace ℚ ↦ archimedeanCompletionHaar v)
local notation "μf" => (fun v : V ↦ rationalLocalMultiplicativeHaar v)

/-- The preimage of the positive real calibration interval in the grouped
Archimedean coordinates. -/
private noncomputable def archimedeanUnitStrip : PositiveCompacts A := by
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let e := Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completionˣ)
  have he : IsOpenEmbedding ev := e.isOpenEmbedding
  let r := isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  have hc : IsOpenEmbedding c := r.toHomeomorph.isOpenEmbedding.comp Units.isOpenEmbedding_val
  have h := hc.comp he
  have hJ : J ⊆ range (c ∘ ev) := by
    intro t ht
    let y := r.symm t
    have hy : y ≠ 0 := by
      intro hy
      have hrt : r y = t := r.apply_symm_apply t
      rw [hy, show r 0 = 0 from map_zero (ringEquivRealOfIsReal Rat.isReal_infinitePlace)] at hrt
      exact (ne_of_gt (zero_lt_one.trans_le ht.1)) hrt.symm
    refine ⟨e.symm (Units.mk0 y hy), ?_⟩
    change c (e (e.symm _)) = t
    rw [e.apply_symm_apply]
    exact r.apply_symm_apply t
  refine { carrier := (c ∘ ev) ⁻¹' J, isCompact' := ?_, interior_nonempty' := ?_ }
  · rw [h.isEmbedding.isCompact_iff, image_preimage_eq_of_subset hJ]
    exact isCompact_Icc
  · refine Nonempty.mono (interior_maximal (preimage_mono Ioo_subset_Icc_self)
      (isOpen_Ioo.preimage h.continuous)) ?_
    obtain ⟨t, ht⟩ := exists_between (Real.one_lt_exp_iff.mpr zero_lt_one)
    obtain ⟨x, hx⟩ := hJ (Ioo_subset_Icc_self ht)
    refine ⟨x, ?_⟩
    change (c ∘ ev) x ∈ Ioo 1 (Real.exp 1)
    rwa [hx]

private theorem calibrationBox_eq_windowUnitStrip :
    (ideleCalibrationBox ℚ archimedeanUnitStrip : Set Iℚ) = rationalIdeleWindowUnitStrip := by
  rw [← image_ideleStageUnitBox ℚ archimedeanUnitStrip ∅]
  change ideleFiniteStageEmbedding ℚ ∅ '' stageUnitRectangle ℚ (↑archimedeanUnitStrip) ∅ = _
  rw [image_ideleStageUnitRectangle]
  ext a
  change (rationalIdeleReal a ∈ J ∧ _) ↔
    a ∈ rationalIdeleUnitWindow ∧ ideleNorm a ∈ J
  constructor
  · rintro ⟨ha, hfin⟩
    have hp : 0 < rationalIdeleReal a := zero_lt_one.trans_le ha.1
    have hw : a ∈ rationalIdeleUnitWindow := ⟨hp, fun v ↦ (hfin v).1, fun v ↦ (hfin v).2⟩
    refine ⟨hw, ?_⟩
    rwa [ideleNorm_eq_abs_rationalIdeleReal a (finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow hw),
      abs_of_pos hp]
  · rintro ⟨hw, hn⟩
    have hp : 0 < rationalIdeleReal a := hw.1
    rw [ideleNorm_eq_abs_rationalIdeleReal a (finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow hw),
      abs_of_pos hp] at hn
    exact ⟨hn, fun v ↦ ⟨hw.2.1 v, hw.2.2 v⟩⟩

set_option linter.concreteInstances false

variable [ma : ∀ v : InfinitePlace ℚ, MeasurableSpace v.Completionˣ]
  [ba : ∀ v : InfinitePlace ℚ, BorelSpace v.Completionˣ]

private theorem archimedeanUnitStrip_mass : Measure.pi μa archimedeanUnitStrip = 1 := by
  change Measure.pi μa ((c ∘ ev) ⁻¹' J) = 1
  rw [preimage_comp, rationalArchimedeanEval_measurePreserving.measure_preimage
    ((realCompletionEmbedding Rat.isReal_infinitePlace).measurable measurableSet_Icc).nullMeasurableSet,
    ← Measure.map_apply (realCompletionEmbedding Rat.isReal_infinitePlace).measurable measurableSet_Icc,
    realCompletionHaar_map, ← realMultiplicativeHaar_unitStrip,
    ← Measure.map_apply Units.isOpenEmbedding_val.measurableEmbedding.measurable measurableSet_Icc,
    map_realMultiplicativeHaar_val,
    ← restrict_withDensity (measurableSet_singleton (0 : ℝ)).compl, restrict_compl_singleton]

variable [mf : ∀ v : V, MeasurableSpace (F v)ˣ]
  [mu : ∀ v : V, MeasurableSpace (v.adicCompletionIntegers ℚ)ˣ]
  [bf : ∀ v : V, BorelSpace (F v)ˣ]
  [bu : ∀ v : V, BorelSpace (v.adicCompletionIntegers ℚ)ˣ]
  [MeasurableSpace Iℚ] [BorelSpace Iℚ]

/-- The named rational idele Haar measure pulls back to the exact local product
on every generic finite stage, including the empty stage. -/
public theorem comap_rationalIdeleHaar_ideleFiniteStage (U : Finset V) :
    rationalIdeleHaar.comap (ideleFiniteStageEmbedding ℚ U) = ideleFiniteStageProduct ℚ μa μf U := by
  obtain ⟨ν, hν, _, hstages, hmass⟩ := exists_ideleRestrictedProductHaar ℚ μa μf ∅
    (fun v _ ↦ rationalLocalMultiplicativeHaar_unitMass v)
  have hstrip : ν rationalIdeleWindowUnitStrip = 1 := by
    rw [← calibrationBox_eq_windowUnitStrip, hmass, archimedeanUnitStrip_mass, Finset.prod_empty, mul_one]
  let : LocallyCompactSpace Iℚ := rationalIdeleWindowUnitStrip.locallyCompactSpace_of_group
  have hnamed : rationalIdeleHaar rationalIdeleWindowUnitStrip = 1 := rationalIdeleHaar_unitStrip
  have heq : ν = rationalIdeleHaar := by
    calc
      ν = Measure.haarMeasure rationalIdeleWindowUnitStrip := by
        rw [Measure.haarMeasure_unique ν rationalIdeleWindowUnitStrip, hstrip, one_smul]
      _ = rationalIdeleHaar := by
        symm
        rw [Measure.haarMeasure_unique rationalIdeleHaar rationalIdeleWindowUnitStrip, hnamed, one_smul]
  exact (hstages rationalIdeleHaar).mp heq.symm U (Finset.empty_subset _)

end Masullo
