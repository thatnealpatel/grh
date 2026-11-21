module

public import Props.RationalAdeleSchwartzLF
import Lemmas.RationalAdeleStageApproximation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Compactly supported rational adelic Schwartz cutoffs

A real smooth plateau and a compact-open finite cylinder suffice to cut
out any compact subset of the rational adeles.
-/

open NumberField IsDedekindDomain Set Metric
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF

private theorem exists_schwartzLF_of_mem_union {f : A → ℂ}
    (hf : f ∈ rationalAdeleSchwartzStageUnion) : ∃ g : E, g.toUnion.val = f := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp hf
  let b := rationalAdeleStageCoordinates (rationalAdeleFactorialLevel_pos n) ⟨f, hn⟩
  exact ⟨rationalAdeleLFAssemblyLinear n b, by
    rw [rationalAdeleLFAssemblyLinear_toUnion, rationalAdeleFactorialStageAssembly_val,
      LinearEquiv.symm_apply_apply]⟩

private theorem schwartzStage_mul {M : ℕ} {f g : A → ℂ}
    (hf : f ∈ rationalAdeleSchwartzStage M) (hg : g ∈ rationalAdeleSchwartzStage M) :
    f * g ∈ rationalAdeleSchwartzStage M := by
  refine ⟨fun x hx ↦ ?_, fun x z hz ↦ ?_, fun z ↦ ?_⟩
  · simp [hf.1 x hx]
  · simp [hf.2.1 x z hz, hg.2.1 x z hz]
  · obtain ⟨b, hb⟩ := hf.2.2 z
    obtain ⟨c, hc⟩ := hg.2.2 z
    exact ⟨SchwartzMap.smulLeftCLM ℂ b c, fun t ↦ by
      rw [SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth]
      simp [hb t, hc t, smul_eq_mul]⟩

/-- Pointwise multiplication preserves rational adelic Schwartz tests. -/
public theorem exists_rationalAdeleSchwartzLF_mul (f g : E) :
    ∃ u : E, u.toUnion.val = f.toUnion.val * g.toUnion.val := by
  obtain ⟨m, hm⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp g.toUnion.property
  apply exists_schwartzLF_of_mem_union
  refine mem_rationalAdeleSchwartzStageUnion.mpr ⟨max m n, schwartzStage_mul ?_ ?_⟩
  · exact rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_left m n)) hm
  · exact rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_right m n)) hn

/-- A Schwartz cutoff is one on the given compact set and takes real
values in `[0,1]`. The two bounds are stated in the complex norm. -/
public theorem exists_rationalAdeleSchwartzLF_cutoff {K : Set A} (hK : IsCompact K) :
    ∃ χ : E, Continuous χ.toUnion.val ∧ HasCompactSupport χ.toUnion.val ∧
      (∀ x ∈ K, χ.toUnion.val x = 1) ∧
      (∀ x, ‖χ.toUnion.val x‖ ≤ 1) ∧ (∀ x, ‖1 - χ.toUnion.val x‖ ≤ 1) := by
  let := t2Space_rationalAdeles
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_rationalAdeleReal.continuousOn
  let r := max R 1
  let β : ContDiffBump (0 : ℝ) := ⟨r, r + 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), by linarith⟩
  let b := β.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero |>.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp β.contDiff)
  obtain ⟨M, hM, hfin⟩ := exists_rationalFinite_support_bound (hK.image continuous_snd)
  let C : Set F := ((M : F) * ·) ⁻¹' (rationalFiniteIntegralAdeles : Set F)
  let f := rationalAdeleAssembleProfiles M (fun _ ↦ (b : ℝ → ℂ))
  have hcell : ∀ j x, x ∈ rationalAdeleStageCell M j → f x = b (rationalAdeleReal x) :=
    fun _ _ hx ↦ rationalAdeleAssembleProfiles_on_cell hM _ hx
  have hzero : ∀ x, x ∉ rationalAdeleStageSupport M → f x = 0 :=
    fun _ hx ↦ rationalAdeleAssembleProfiles_off_stage hM _ hx
  obtain ⟨u, hu, _⟩ := exists_rationalAdeleStageSample_eq_of_assembled hM f (fun _ ↦ b) hcell hzero
  obtain ⟨χ, he⟩ := exists_schwartzLF_of_mem_union
    (rationalAdeleSchwartzStage_le_union hM (hu ▸ u.property))
  have hstage (x : A) (hx : x ∈ rationalAdeleStageSupport M) :
      f x = (β (rationalAdeleReal x) : ℂ) := by
    obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
    exact hcell j x hj
  refine ⟨χ, ?_⟩
  rw [he]
  refine ⟨continuous_rationalAdeleAssembleProfiles (fun _ ↦ b.continuous), ?_, ?_, ?_, ?_⟩
  · let e : ℝ × F → A := fun p ↦ ((rationalAdeleAt p.1 0).1, p.2)
    have hec : Continuous e :=
      (((continuous_rationalAdeleAt (0 : F)).fst).comp continuous_fst).prodMk continuous_snd
    have hC : IsCompact C := (rationalAdeleBoxStage_isCompact_isOpen hM).2.2.1
    apply exists_compact_iff_hasCompactSupport.mp
    refine ⟨e '' (tsupport (β : ℝ → ℝ) ×ˢ C), (β.hasCompactSupport.prod hC).image hec, ?_⟩
    intro x hx
    by_cases hs : x ∈ rationalAdeleStageSupport M
    · rw [hstage x hs]
      suffices hr : β (rationalAdeleReal x) = 0 by exact_mod_cast hr
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      exact hx ⟨(rationalAdeleReal x, x.2), ⟨ht, hs⟩,
        Prod.ext (rationalAdeleAt_fst_real x 0) rfl⟩
    · exact hzero x hs
  · intro x hx
    have hs : x ∈ rationalAdeleStageSupport M := hfin (mem_image_of_mem _ hx)
    rw [hstage x hs, β.one_of_mem_closedBall]
    · simp
    · simpa [Real.dist_eq, Real.norm_eq_abs, β, r] using (hR x hx).trans (le_max_left R 1)
  · intro x
    by_cases hx : x ∈ rationalAdeleStageSupport M
    · rw [hstage x hx, Complex.norm_real, Real.norm_of_nonneg β.nonneg]
      exact β.le_one
    · simp [hzero x hx]
  · intro x
    by_cases hx : x ∈ rationalAdeleStageSupport M
    · rw [hstage x hx, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr β.le_one)]
      exact sub_le_self _ β.nonneg
    · simp [hzero x hx]

end Masullo
