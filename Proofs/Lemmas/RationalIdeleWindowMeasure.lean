module

public import Theorems.RationalIdeleFundamentalDomain
public import Theorems.RationalIdeleClassHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Measure of the rational idele window -/

open NumberField MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

local notation "Ideles" => IdeleGroup (𝓞 ℚ) ℚ

private noncomputable def representative : RationalIdeleClasses →* Ideles where
  toFun c := (rationalIdeleUnitWindowHomeomorph.symm c).val
  map_one' := by
    have h : rationalIdeleUnitWindowHomeomorph ⟨1, one_mem_rationalIdeleUnitWindow⟩ = 1 := by
      rw [rationalIdeleUnitWindowHomeomorph_apply]
      rfl
    rw [← h, Homeomorph.symm_apply_apply]
  map_mul' c d := by
    let a := rationalIdeleUnitWindowHomeomorph.symm c
    let b := rationalIdeleUnitWindowHomeomorph.symm d
    let ab : rationalIdeleUnitWindow := ⟨a.val * b.val, mul_mem_rationalIdeleUnitWindow a.2 b.2⟩
    have h : rationalIdeleUnitWindowHomeomorph ab = c * d := by
      rw [rationalIdeleUnitWindowHomeomorph_apply]
      change QuotientGroup.mk (a.val * b.val) = _
      rw [QuotientGroup.mk_mul]
      simp only [← rationalIdeleUnitWindowHomeomorph_apply]
      exact congrArg₂ (· * ·) (rationalIdeleUnitWindowHomeomorph.apply_symm_apply c)
        (rationalIdeleUnitWindowHomeomorph.apply_symm_apply d)
    rw [← h, Homeomorph.symm_apply_apply]

private theorem isOpenEmbedding_representative : IsOpenEmbedding representative :=
  isOpen_rationalIdeleUnitWindow.isOpenEmbedding_subtypeVal.comp
    rationalIdeleUnitWindowHomeomorph.symm.isOpenEmbedding

set_option linter.concreteInstances false

section Transport

variable [MeasurableSpace Ideles] [BorelSpace Ideles]
  [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

/-- The restriction to the open window pushes forward to a Haar measure on the quotient. -/
public theorem isHaarMeasure_map_restrict_rationalIdeleUnitWindow (ν : Measure Ideles)
    [ν.IsHaarMeasure] :
    ((ν.restrict rationalIdeleUnitWindow).map
      (QuotientGroup.mk : Ideles → RationalIdeleClasses)).IsHaarMeasure := by
  have h : (ν.restrict rationalIdeleUnitWindow).map (QuotientGroup.mk : Ideles → RationalIdeleClasses) =
      ν.comap representative := by
    ext s hs
    rw [Measure.map_apply QuotientGroup.continuous_mk.measurable hs,
      Measure.restrict_apply (QuotientGroup.continuous_mk.measurable hs),
      Measure.comap_apply _ isOpenEmbedding_representative.injective
        (fun _ ht ↦ isOpenEmbedding_representative.measurableEmbedding.measurableSet_image' ht) _ hs]
    congr 1
    ext a
    constructor
    · rintro ⟨has, haw⟩
      refine ⟨QuotientGroup.mk a, has, ?_⟩
      change (rationalIdeleUnitWindowHomeomorph.symm (QuotientGroup.mk a)).val = a
      rw [← rationalIdeleUnitWindowHomeomorph_apply ⟨a, haw⟩, Homeomorph.symm_apply_apply]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, (rationalIdeleUnitWindowHomeomorph.symm c).property⟩
      change QuotientGroup.mk (rationalIdeleUnitWindowHomeomorph.symm c).val ∈ s
      rwa [← rationalIdeleUnitWindowHomeomorph_apply, Homeomorph.apply_symm_apply]
  rw [h]
  exact Measure.IsHaarMeasure.comap (mH := inferInstance) ν isOpenEmbedding_representative

end Transport

local instance : CompactSpace rationalIdeleClassNormOne := compactSpace_rationalIdeleClassNormOne
local instance : T2Space RationalIdeleClasses := t2Space_rationalIdeleClassGroup
local instance : LocallyCompactSpace RationalIdeleClasses := locallyCompactSpace_rationalIdeleClassGroup
local instance : SigmaCompactSpace RationalIdeleClasses :=
  ⟨rationalIdeleClassLogSplit.surjective.range_eq ▸
    isSigmaCompact_range rationalIdeleClassLogSplit.continuous⟩

/-- A compact norm strip on the rational quotient. -/
private theorem isCompact_rationalIdeleClass_normStrip :
    IsCompact {c : RationalIdeleClasses | ideleClassNorm c ∈ Icc 1 (Real.exp 1)} := by
  let e := rationalIdeleClassLogSplit
  have hcompact : IsCompact ((Multiplicative.ofAdd '' Icc (0 : ℝ) 1) ×ˢ
      (univ : Set rationalIdeleClassNormOne)) :=
    (isCompact_Icc.image continuous_ofAdd).prod isCompact_univ
  convert hcompact.image e.continuous using 1
  ext c
  change _ ↔ c ∈ e.toEquiv '' _
  rw [e.toEquiv.image_eq_preimage_symm]
  change (1 ≤ ideleClassNorm c ∧ ideleClassNorm c ≤ Real.exp 1) ↔
    ((rationalIdeleClassLogSplit.symm c).1 ∈ Multiplicative.ofAdd '' Icc (0 : ℝ) 1 ∧ True)
  rw [and_true, rationalIdeleClassLogSplit_symm_fst]
  have hlog : rationalIdeleClassLogNorm c = Multiplicative.ofAdd (Real.log (ideleClassNorm c)) :=
    congrArg Multiplicative.ofAdd (rationalIdeleClassLogNorm_apply c)
  rw [hlog]
  rw [Multiplicative.ofAdd.injective.mem_set_image, mem_Icc,
    Real.le_log_iff_exp_le (ideleClassNorm_pos c), Real.exp_zero,
    Real.log_le_iff_le_exp (ideleClassNorm_pos c)]

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

/-- A Haar measure giving mass one to this strip is the normalized rational class measure. -/
public theorem eq_rationalIdeleClassHaar_of_normStrip (μ : Measure RationalIdeleClasses)
    [μ.IsHaarMeasure] (h : μ {c : RationalIdeleClasses | ideleClassNorm c ∈ Icc 1 (Real.exp 1)} = 1) :
    μ = rationalIdeleClassHaar := by
  let := isHaarMeasure_rationalIdeleClassHaar
  have hmass : rationalIdeleClassHaar {c : RationalIdeleClasses | ideleClassNorm c ∈
      Icc 1 (Real.exp 1)} = 1 := by
    rw [rationalIdeleClassHaar_normStrip (by rw [← Real.exp_zero]; gcongr; norm_num),
      Real.log_exp, ENNReal.ofReal_one]
  have hscale := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure
    μ rationalIdeleClassHaar isCompact_rationalIdeleClass_normStrip.closure
  rw [h, hmass] at hscale
  change 1 = (↑(μ.haarScalarFactor rationalIdeleClassHaar) : ℝ≥0∞) * 1 at hscale
  rw [mul_one] at hscale
  apply Measure.ext_of_iUnion_eq_univ (iUnion_compactCovering RationalIdeleClasses)
  intro n
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure μ rationalIdeleClassHaar
      ((isCompact_compactCovering _ n).closure_of_subset inter_subset_right)]
  change (↑(μ.haarScalarFactor rationalIdeleClassHaar) : ℝ≥0∞) * _ = _
  rw [← hscale, one_mul]

end Masullo
