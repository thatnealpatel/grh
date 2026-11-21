module

public import Props.RationalAdeleSchwartzLF
import Lemmas.RationalAdeleStageSampling

/-! # Rational adelic Schwartz functions vanish at infinity

The finitely many real profiles are small off one compact real set;
the finite coordinates already lie in a single compact support stage.
-/

open NumberField IsDedekindDomain Filter Set Topology
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ

private theorem tendsto_stage_cocompact {M : ℕ} (hM : 0 < M)
    (f : rationalAdeleSchwartzStage M) : Tendsto f.val (cocompact A) (𝓝 0) := by
  let b := rationalAdeleStageCoordinates hM f
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨K, hK, hsmall⟩ := mem_cocompact.mp (eventually_all.mpr fun j : Fin (M ^ 2) ↦
    Metric.tendsto_nhds.mp (b j).tendsto_cocompact ε hε)
  let C : Set F := ((M : F) * ·) ⁻¹' (rationalFiniteIntegralAdeles : Set F)
  let e : ℝ × F → A := fun p ↦ ((rationalAdeleAt p.1 0).1, p.2)
  have he : Continuous e :=
    (((continuous_rationalAdeleAt (0 : F)).fst).comp continuous_fst).prodMk continuous_snd
  have hC : IsCompact C := (rationalAdeleBoxStage_isCompact_isOpen hM).2.2.1
  filter_upwards [((hK.prod hC).image he).compl_mem_cocompact] with x hx
  by_cases hs : x ∈ rationalAdeleStageSupport M
  · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hs
    have ht : rationalAdeleReal x ∉ K := fun ht ↦ hx
      ⟨(rationalAdeleReal x, x.2), ⟨ht, hs⟩, Prod.ext (rationalAdeleAt_fst_real x 0) rfl⟩
    rw [← rationalAdeleStageCoordinates_eq_on_cell hM f hj]
    exact hsmall ht j
  · rw [f.property.1 x hs, dist_self]
    exact hε

/-- The representative of a rational adelic Schwartz test is continuous and
vanishes at infinity on the additive adeles. -/
public theorem rationalAdeleSchwartzLF_continuous_vanishing (f : RationalAdeleSchwartzLF) :
    Continuous f.toUnion.val ∧ Tendsto f.toUnion.val (cocompact A) (𝓝 0) := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  let u : rationalAdeleSchwartzStage (rationalAdeleFactorialLevel n) := ⟨f.toUnion.val, hn⟩
  have h := rationalAdeleFactorialLevel_pos n
  refine ⟨?_, tendsto_stage_cocompact h u⟩
  change Continuous u.val
  rw [← LinearEquiv.symm_apply_apply (rationalAdeleStageCoordinates h) u,
    rationalAdeleStageCoordinates_symm_eq_boxSum]
  exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul (continuous_rationalAdeleBox _ _ _)

end Masullo
