module

public import Props.RationalAdeleSchwartzLF
import Lemmas.EventualZeroSeminormSum

/-! # Bounded families of rational adelic Schwartz functions

Every bounded family in the rational LF topology has one common finite
geometry and a bounded set of real Schwartz profiles in that geometry.
This is a direct proof of the stage-boundedness input used at Theorem
2.2.3.4(4), pp. 84–85, for the rational model.
-/

open Bornology
open scoped NNReal SchwartzMap

namespace Masullo

local notation "E" => RationalAdeleSchwartzLF
local notation "L" => rationalAdeleFactorialLevel
local notation "Stage" n => rationalAdeleSchwartzStage (L n)
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)
local notation "R" n => rationalAdeleStageResidual n
local notation "A" n => rationalAdeleLFAssembly n
local notation "Read" n => rationalAdeleLFRead n

/-- A residual seminorm can be made large on one detected element, while
it still vanishes on the entire preceding stage. -/
private theorem exists_layer_seminorm (B : Set E) (n : ℕ) :
    ∃ p : RationalAdeleLFSeminorm,
      (∀ f : E, f.toUnion.val ∈ (Stage n) → p.val f = 0) ∧
      ((∃ f ∈ B, (R n) f.toUnion ≠ 0) → ∃ f ∈ B, (n : ℝ) + 1 ≤ p.val f) := by
  classical
  by_cases h : ∃ f ∈ B, (R n) f.toUnion ≠ 0
  · obtain ⟨f, hf, hr⟩ := h
    have hj : ∃ j, (R n) f.toUnion j ≠ 0 := by
      by_contra! h
      apply hr
      funext j
      exact h j
    obtain ⟨j, hj⟩ := hj
    let q := (SchwartzMap.seminorm ℂ 0 0 : Seminorm ℂ 𝓢(ℝ, ℂ)).comp
      ((LinearMap.proj j).comp ((R n).comp RationalAdeleSchwartzLF.toUnion))
    have hq : 0 < q f := by
      have ht : ∃ t, (R n) f.toUnion j t ≠ 0 := by
        by_contra! h
        exact hj (SchwartzMap.ext h)
      obtain ⟨t, ht⟩ := ht
      exact (norm_pos_iff.mpr ht).trans_le (SchwartzMap.norm_le_seminorm ℂ _ t)
    let c : ℝ≥0 := ⟨((n : ℝ) + 1) / q f, div_nonneg (by positivity) hq.le⟩
    refine ⟨⟨c • q, fun m ↦ ?_⟩, ?_, fun _ ↦ ⟨f, hf, ?_⟩⟩
    · simp only [Seminorm.coe_comp, Function.comp_def, smul_apply, NNReal.smul_def, q,
        LinearMap.comp_apply, LinearMap.proj_apply, rationalAdeleLFAssemblyLinear_toUnion]
      exact continuous_const.mul (((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0, 0)).comp
        ((continuous_apply j).comp (rationalAdeleStageResidual_continuous_on_stage m n)))
    · intro g hg
      simp [q, rationalAdeleStageResidual_eq_zero n g.toUnion hg]
    · change (n : ℝ) + 1 ≤ (((n : ℝ) + 1) / q f) * q f
      rw [div_mul_cancel₀ _ hq.ne']
  · exact ⟨⟨0, fun _ ↦ continuous_const⟩, fun _ _ ↦ rfl, fun hh ↦ (h hh).elim⟩

/-- Every LF-bounded family is contained in a common factorial stage. -/
public theorem rationalAdeleLF_bounded_subset_stage {B : Set E} (hB : IsVonNBounded ℂ B) :
    ∃ m, ∀ f ∈ B, f.toUnion.val ∈ (Stage m) := by
  classical
  choose p hp_zero hp_large using exists_layer_seminorm B
  let q (n : ℕ) := (p n).val
  have hzero (f : E) {m : ℕ} (hm : f.toUnion.val ∈ (Stage m)) (n : ℕ) (hn : m ≤ n) :
      q n f = 0 :=
    hp_zero n f (rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd hn) hm)
  have hfinite (f : E) : ∃ m, ∀ n ≥ m, q n f = 0 := by
    obtain ⟨m, hm⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
    exact ⟨m, hzero f hm⟩
  let s := eventualZeroSeminormSum q hfinite
  have hs : ∀ m, Continuous (s.comp (rationalAdeleLFAssemblyLinear m)) := by
    intro m
    have he (b : Profiles m) : s (rationalAdeleLFAssemblyLinear m b) =
        ∑ n ∈ Finset.range m, q n (rationalAdeleLFAssemblyLinear m b) := by
      apply eventualZeroSeminormSum_apply
      apply hzero
      rw [rationalAdeleLFAssemblyLinear_toUnion, rationalAdeleFactorialStageAssembly_val]
      exact Subtype.property _
    simp only [Seminorm.coe_comp, Function.comp_def, he]
    exact continuous_finsetSum _ fun n _ ↦ (p n).property m
  obtain ⟨r, _, hr⟩ := rationalAdeleLF_withSeminorms.isVonNBounded_iff_seminorm_bounded.mp hB ⟨s, hs⟩
  obtain ⟨m, hm⟩ := exists_nat_gt r
  refine ⟨m, fun f hf ↦ (mem_rationalAdeleSchwartzStage_iff_residual m f.toUnion).mpr ?_⟩
  intro n hn
  by_contra hne
  obtain ⟨g, hg, hlarge⟩ := hp_large n ⟨f, hf, hne⟩
  have hle : q n g ≤ s g := le_eventualZeroSeminormSum_apply q hfinite n g
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hn
  have hs_r : s g < r := hr g hg
  have hn_q : (n : ℝ) + 1 ≤ q n g := hlarge
  linarith only [hs_r, hn_q, hle, hmn, hm]

/-- A subset of the rational LF space is bounded exactly if it is the assembly
of a bounded tuple family from a single factorial level. -/
public theorem rationalAdeleLF_bounded_iff {B : Set E} :
    IsVonNBounded ℂ B ↔ ∃ (n : ℕ) (C : Set (Profiles n)), IsVonNBounded ℂ C ∧ B = (A n) '' C := by
  constructor
  · intro hB
    obtain ⟨n, hn⟩ := rationalAdeleLF_bounded_subset_stage hB
    refine ⟨n, (Read n) '' B, hB.image (Read n), ?_⟩
    ext f
    constructor
    · intro hf
      exact ⟨(Read n) f, ⟨f, hf, rfl⟩, rationalAdeleLFAssembly_read n f (hn f hf)⟩
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      rwa [rationalAdeleLFAssembly_read n g (hn g hg)]
  · rintro ⟨n, C, hC, rfl⟩
    exact hC.image (A n)

end Masullo
