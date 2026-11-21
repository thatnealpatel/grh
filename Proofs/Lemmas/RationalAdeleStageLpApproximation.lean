module

public import Lemmas.RationalAdeleStageApproximation
public import Theorems.RationalAdeleAddHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Approximation in adelic L² by sampled continuous profiles

The fixed compact support bound permits conversion from uniform error
to `L²` error for the normalized additive Haar measure. The profiles in
this step are only continuous and compactly supported, not yet Schwartz.
-/

open NumberField MeasureTheory Set
open scoped ENNReal

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar

set_option linter.concreteInstances false in
/-- In normalized adelic `L²`, a continuous compactly supported function
can be approximated by its representative-line samples on one stage. -/
public theorem exists_rationalAdeleStage_L2_sample [MeasurableSpace A] [BorelSpace A]
    {f : A → ℂ} (hc : Continuous f) (hs : HasCompactSupport f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    MemLp f 2 μA ∧ ∃ M : ℕ, 0 < M ∧
      let b := fun (j : Fin (M ^ 2)) (t : ℝ) ↦
        f (rationalAdeleAt t (rationalAdeleStageRepresentative M j))
      let g := rationalAdeleAssembleProfiles M b
      (∀ j, Continuous (b j) ∧ HasCompactSupport (b j)) ∧
        MemLp g 2 μA ∧ eLpNorm (f - g) 2 μA < ε := by
  let := t2Space_rationalAdeles
  obtain ⟨K, hK, hf₀, hsample⟩ := exists_rationalAdeleStage_uniform_sample hc hs
  have hKμ : μA K ≠ ⊤ := hK.measure_ne_top
  have hscale : μA K ^ (2 : ℝ≥0∞).toReal⁻¹ ≠ ⊤ := by finiteness
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_mul_lt hscale hε.ne'
  let η := min δ 1
  have hη : 0 < η := lt_min hδ (by simp)
  have hηfin : η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  obtain ⟨M, hM, hb, hg₀, hFG⟩ := hsample η.toReal (ENNReal.toReal_pos hη.ne' hηfin)
  let b (j : Fin (M ^ 2)) (t : ℝ) := f (rationalAdeleAt t (rationalAdeleStageRepresentative M j))
  let g := rationalAdeleAssembleProfiles M b
  have hg : Continuous g := continuous_rationalAdeleAssembleProfiles fun j ↦ (hb j).1
  have hgs : HasCompactSupport g := exists_compact_iff_hasCompactSupport.mp ⟨K, hK, hg₀⟩
  refine ⟨hc.memLp_of_hasCompactSupport hs, M, hM, hb, hg.memLp_of_hasCompactSupport hgs, ?_⟩
  have hrestrict : K.indicator (f - g) = f - g := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Pi.sub_apply, hf₀ x hx, show g x = 0 from hg₀ x hx,
        sub_zero]
  have hbound := eLpNorm_indicator_sub_le_of_dist_bdd (p := 2) μA
    (by simp) hK.isClosed.measurableSet.nullMeasurableSet
    ENNReal.toReal_nonneg
    (hrestrict ▸ (hc.sub hg).aestronglyMeasurable)
    (fun x _ ↦ by rw [dist_eq_norm]; exact hFG x)
  rw [hrestrict, ENNReal.ofReal_toReal hηfin, one_div] at hbound
  refine hbound.trans_lt ((mul_le_mul_of_nonneg_right ?_ bot_le).trans_lt hδε)
  exact min_le_left δ 1

end Masullo
