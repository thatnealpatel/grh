module

public import Props.RationalAdeleSchwartzLF
import Lemmas.RationalAdeleStageApproximation
import Lemmas.RationalAdeleStageNorm
import Mathlib.Geometry.Manifold.SmoothApprox

/-! # Uniform approximation by rational adelic Schwartz tests

Sample on a finite stage, then smooth its finitely many real profiles
without enlarging their supports. The resulting Schwartz approximants
are supported in a common compact set, independent of the tolerance.
-/

open NumberField Set
open scoped ContDiff SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF

/-- Uniform Schwartz approximation with support in a fixed compact set. -/
public theorem exists_rationalAdeleSchwartzLF_uniform_approx {f : A → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) :
    ∃ K : Set A, IsCompact K ∧ (∀ x ∉ K, f x = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ g : E,
        (∀ x ∉ K, g.toUnion.val x = 0) ∧ ∀ x, ‖g.toUnion.val x - f x‖ ≤ ε := by
  obtain ⟨K, hK, hf, hsample⟩ := exists_rationalAdeleStage_uniform_sample hc hs
  refine ⟨K, hK, hf, fun ε hε ↦ ?_⟩
  obtain ⟨M, hM, hb, hv, happrox⟩ := hsample (ε / 2) (half_pos hε)
  let b (j : Fin (M ^ 2)) (t : ℝ) := f (rationalAdeleAt t (rationalAdeleStageRepresentative M j))
  let v := rationalAdeleAssembleProfiles M b
  choose c hcd he hcs using fun j ↦ Continuous.exists_contDiff_approx ⊤ (hb j).1
    (ε := fun _ ↦ ε / 2) continuous_const (fun _ ↦ half_pos hε)
  let d (j : Fin (M ^ 2)) : 𝓢(ℝ, ℂ) := ((hb j).2.mono (hcs j)).toSchwartzMap (hcd j)
  let w := (rationalAdeleStageCoordinates hM).symm d
  have hw : w.val = rationalAdeleAssembleProfiles M (fun j ↦ d j) :=
    rationalAdeleStageCoordinates_symm_eq_assembleProfiles hM d
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp (rationalAdeleSchwartzStage_le_union hM w.property)
  let wn : rationalAdeleSchwartzStage (rationalAdeleFactorialLevel n) := ⟨w.val, hn⟩
  let g := rationalAdeleLFAssemblyLinear n (rationalAdeleStageCoordinates (rationalAdeleFactorialLevel_pos n) wn)
  have hg : g.toUnion.val = w.val := by
    rw [rationalAdeleLFAssemblyLinear_toUnion, rationalAdeleFactorialStageAssembly_val, LinearEquiv.symm_apply_apply]
  have hwv (x : A) (hx : x ∈ rationalAdeleStageSupport M) :
      ∃ j, w.val x = c j (rationalAdeleReal x) ∧ v x = b j (rationalAdeleReal x) := by
    obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
    exact ⟨j, by rw [hw, rationalAdeleAssembleProfiles_on_cell hM _ hj]; rfl,
      rationalAdeleAssembleProfiles_on_cell hM _ hj⟩
  refine ⟨g, fun x hx ↦ ?_, fun x ↦ ?_⟩
  · rw [hg]
    by_cases hsx : x ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, hj'⟩ := hwv x hsx
      rw [hj]
      by_contra hnz
      exact (hcs j hnz) (show b j (rationalAdeleReal x) = 0 from hj' ▸ hv x hx)
    · exact w.property.1 x hsx
  have hclose : ‖w.val x - v x‖ ≤ ε / 2 := by
    by_cases hx : x ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, hj'⟩ := hwv x hx
      rw [hj, hj', ← dist_eq_norm]
      exact (he j (rationalAdeleReal x)).le
    · rw [w.property.1 x hx, show v x = 0 from rationalAdeleAssembleProfiles_off_stage hM _ hx,
        sub_zero, norm_zero]
      exact (half_pos hε).le
  rw [hg]
  calc
    ‖w.val x - f x‖ ≤ ‖w.val x - v x‖ + ‖f x - v x‖ := by
      rw [norm_sub_rev (f x) (v x)]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hclose (happrox x)
    _ = ε := add_halves _

end Masullo
