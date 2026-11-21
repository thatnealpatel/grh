module

public import Props.RationalAdeleSchwartzLF
public import Theorems.RationalAdeleAddHaar
import Lemmas.RationalAdeleAdditiveModulus
import Lemmas.RationalAdeleStageSchwartzApproximation
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Density of rational adelic Schwartz tests in normalized L²

For a compactly supported continuous test, sample first on a finite
quotient stage, then approximate the finitely many real profiles on that
same stage. Regularity of Haar gives density for arbitrary `L²` inputs.
This is a project step toward (D.1.1.10), p. 747, not the unitary extension.
-/

open NumberField MeasureTheory
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

end Masullo
