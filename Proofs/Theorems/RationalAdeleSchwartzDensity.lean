module

public import Props.RationalAdeleSchwartzLF
public import Theorems.RationalAdeleAddHaar
import Lemmas.RationalAdeleAdditiveModulus
import Lemmas.RationalAdeleStageSchwartzApproximation
import Lemmas.RationalAdeleSchwartzCutoff
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Density of rational adelic Schwartz tests in normalized L²

For a compactly supported continuous test, sample first on a finite
quotient stage, then approximate the finitely many real profiles on that
same stage. Regularity of Haar gives density for arbitrary `L²` inputs.
This is a project step toward (D.1.1.10), p. 747, not the unitary extension.
-/

open NumberField MeasureTheory Set
open scoped ENNReal

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- Rational adelic Schwartz functions are dense in `L²` for the normalized
additive Haar measure. This formulation works on representatives. -/
public theorem exists_rationalAdeleSchwartzLF_L2_approx {f : A → ℂ}
    (hf : MemLp f 2 μA) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : RationalAdeleSchwartzLF, MemLp g.toUnion.val 2 μA ∧
      eLpNorm (f - g.toUnion.val) 2 μA < ε := by
  let : T2Space A := t2Space_rationalAdeles
  let : LocallyCompactSpace A := rationalAdeleClosedUnitStrip.locallyCompactSpace_of_addGroup
  let : SecondCountableTopology A := secondCountableTopology_rationalAdeles
  obtain ⟨δ, hδ, hadd⟩ := exists_Lp_half ℂ μA 2 hε.ne'
  obtain ⟨u, hus, hfu, huc, _⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hδ.ne'
  obtain ⟨M, hM, g, hg, hug⟩ := exists_rationalAdeleSchwartzStage_L2_approx huc hus hδ
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp (rationalAdeleSchwartzStage_le_union hM g.property)
  let gn : rationalAdeleSchwartzStage (rationalAdeleFactorialLevel n) := ⟨g.val, hn⟩
  let s := rationalAdeleLFAssemblyLinear n (rationalAdeleStageCoordinates (rationalAdeleFactorialLevel_pos n) gn)
  have he : s.toUnion.val = g.val := by
    rw [rationalAdeleLFAssemblyLinear_toUnion, rationalAdeleFactorialStageAssembly_val,
      LinearEquiv.symm_apply_apply]
  refine ⟨s, he ▸ hg, ?_⟩
  rw [he, show f - g.val = (f - u) + (u - g.val) by abel]
  exact hadd _ _ hfu hug.le

/-- One rational adelic Schwartz test approximates an integrable `L²` input
in both normalized Haar seminorms, with independent positive tolerances. -/
public theorem exists_rationalAdeleSchwartzLF_L1_L2_approx {f : A → ℂ}
    (hf₁ : MemLp f 1 μA) (hf₂ : MemLp f 2 μA) {ε₁ ε₂ : ℝ≥0∞}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    ∃ g : RationalAdeleSchwartzLF, eLpNorm (f - g.toUnion.val) 1 μA < ε₁ ∧
      eLpNorm (f - g.toUnion.val) 2 μA < ε₂ := by
  let : T2Space A := t2Space_rationalAdeles
  let : LocallyCompactSpace A := rationalAdeleClosedUnitStrip.locallyCompactSpace_of_addGroup
  let : SecondCountableTopology A := secondCountableTopology_rationalAdeles
  obtain ⟨δ₁, hδ₁, hadd₁⟩ := exists_Lp_half ℂ μA 1 hε₁.ne'
  obtain ⟨δ₂, hδ₂, hadd₂⟩ := exists_Lp_half ℂ μA 2 hε₂.ne'
  obtain ⟨u₁, hs₁, hu₁, _, _⟩ := hf₁.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hδ₁.ne'
  obtain ⟨u₂, hs₂, hu₂, _, _⟩ := hf₂.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hδ₂.ne'
  obtain ⟨c, hcc, hcs, hc₁, hc, hc'⟩ := exists_rationalAdeleSchwartzLF_cutoff (hs₁.union hs₂)
  let χ := c.toUnion.val
  let v := (1 - χ) * f
  have hv : AEStronglyMeasurable v μA := (continuous_const.sub hcc).aestronglyMeasurable.mul
    hf₂.aestronglyMeasurable
  have htail (u : A → ℂ) (hu : tsupport u ⊆ tsupport u₁ ∪ tsupport u₂) (p : ℝ≥0∞) :
      eLpNorm v p μA ≤ eLpNorm (f - u) p μA := by
    apply eLpNorm_mono hv
    intro x
    by_cases hx : x ∈ tsupport u₁ ∪ tsupport u₂
    · simp [v, χ, hc₁ x hx]
    · have hzero : u x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hu h))
      simp only [v, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, hzero, sub_zero, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc' x)
  let K := tsupport χ
  let C := μA K ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hcs.measure_ne_top
  obtain ⟨η, hη, hηC⟩ := ENNReal.exists_pos_mul_lt hC hδ₁.ne'
  obtain ⟨g, hg, hfg⟩ := exists_rationalAdeleSchwartzLF_L2_approx hf₂ (lt_min hη hδ₂)
  obtain ⟨s, hs⟩ := exists_rationalAdeleSchwartzLF_mul c g
  let w := χ * (f - g.toUnion.val)
  have hw : AEStronglyMeasurable w μA :=
    hcc.aestronglyMeasurable.mul (hf₂.aestronglyMeasurable.sub hg.aestronglyMeasurable)
  have hw₂ : eLpNorm w 2 μA ≤ eLpNorm (f - g.toUnion.val) 2 μA := by
    apply eLpNorm_mono hw
    intro x
    rw [show w x = χ x * (f - g.toUnion.val) x from rfl, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc x)
  have hws : Function.support w ⊆ K := by
    intro x hx
    contrapose hx
    simp [w, show χ x = 0 from image_eq_zero_of_notMem_tsupport hx]
  have hw₁ : eLpNorm w 1 μA ≤ δ₁ := by
    rw [← eLpNorm_restrict_eq_of_support_subset hw hws]
    calc
      _ ≤ eLpNorm w 2 (Measure.restrict μA K) * C := by
        simpa only [C, Measure.restrict_apply_univ] using
          (eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos (f := w) (μ := Measure.restrict μA K)
            (p := 1) (q := 2) (by simp) (by simp))
      _ ≤ η * C := mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (hw₂.trans (hfg.le.trans (min_le_left _ _)))) le_rfl
      _ ≤ δ₁ := hηC.le
  have he : f - s.toUnion.val = v + w := by
    rw [hs]
    change f - χ * g.toUnion.val = (1 - χ) * f + χ * (f - g.toUnion.val)
    ring
  refine ⟨s, ?_, ?_⟩ <;> rw [he]
  · exact hadd₁ _ _ ((htail u₁ subset_union_left 1).trans hu₁) hw₁
  · exact hadd₂ _ _ ((htail u₂ subset_union_right 2).trans hu₂)
      (hw₂.trans (hfg.le.trans (min_le_right _ _)))

end Masullo
