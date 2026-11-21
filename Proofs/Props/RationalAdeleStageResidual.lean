module

public import Lemmas.RationalAdeleStageUnion

/-! # Detecting escape from a rational adelic Schwartz stage

Read at two adjacent factorial levels and subtract the transition of
the coarse reading from the fine reading. The difference detects new
profiles at that layer. This is a project construction for the bounded
family step of Theorem 2.2.3.4(4), pp. 84–85, not yet a statement about
boundedness in the global LF topology.
-/

open scoped SchwartzMap

namespace Masullo

local notation "L" => rationalAdeleFactorialLevel
local notation "Stage" n => rationalAdeleSchwartzStage (L n)
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)
local notation "U" => rationalAdeleSchwartzStageUnion
local notation "pos" => rationalAdeleFactorialLevel_pos

private theorem adjacent_dvd (n : ℕ) : L n ∣ L (n + 1) :=
  rationalAdeleFactorialLevel_dvd (Nat.le_succ n)

private noncomputable def transition (n : ℕ) : (Profiles n) →L[ℂ] (Profiles (n + 1)) :=
  rationalAdeleStageTransition (pos n) (pos (n + 1)) (adjacent_dvd n)

/-- The fine reading minus the extension of the coarse reading. -/
public noncomputable def rationalAdeleStageResidual (n : ℕ) : U →ₗ[ℂ] (Profiles (n + 1)) :=
  rationalAdeleFactorialStageRead (n + 1) -
    (transition n).toLinearMap.comp (rationalAdeleFactorialStageRead n)

public theorem rationalAdeleStageResidual_apply (n : ℕ) (f : U) :
    rationalAdeleStageResidual n f = rationalAdeleFactorialStageRead (n + 1) f -
      rationalAdeleStageTransition (pos n) (pos (n + 1))
        (rationalAdeleFactorialLevel_dvd (Nat.le_succ n)) (rationalAdeleFactorialStageRead n f) := by rfl

/-- Each residual is continuous on tuples from each fixed stage. -/
public theorem rationalAdeleStageResidual_continuous_on_stage (m n : ℕ) :
    Continuous (fun b : Profiles m ↦
      rationalAdeleStageResidual n (rationalAdeleFactorialStageAssembly m b)) :=
  (rationalAdeleFactorialStageRead_continuous_on_stage m (n + 1)).sub
    ((transition n).continuous.comp (rationalAdeleFactorialStageRead_continuous_on_stage m n))

/-- There is no new profile at layer `n+1` for a function from stage `n`. -/
public theorem rationalAdeleStageResidual_eq_zero (n : ℕ) (f : U) (hf : f.val ∈ Stage n) :
    rationalAdeleStageResidual n f = 0 := by
  have hg := rationalAdeleSchwartzStage_mono (adjacent_dvd n) hf
  rw [rationalAdeleStageResidual_apply, rationalAdeleFactorialStageRead_eq_coordinates _ _ hf,
    rationalAdeleFactorialStageRead_eq_coordinates _ _ hg,
    rationalAdeleStageTransition_eq_coordinates, LinearEquiv.symm_apply_apply]
  exact sub_self _

/-- For a function in stage `n+1`, a zero residual means it was already
in stage `n`. No assertion that a single layer detects all later stages. -/
public theorem rationalAdeleStageResidual_eq_zero_iff (n : ℕ) (f : U)
    (hf : f.val ∈ Stage (n + 1)) : rationalAdeleStageResidual n f = 0 ↔ f.val ∈ Stage n := by
  refine ⟨fun h ↦ ?_, rationalAdeleStageResidual_eq_zero n f⟩
  rw [rationalAdeleStageResidual_apply, sub_eq_zero,
    rationalAdeleFactorialStageRead_eq_coordinates _ _ hf] at h
  have he : f.val = ((rationalAdeleStageCoordinates (pos n)).symm
      (rationalAdeleFactorialStageRead n f)).val := by
    rw [← rationalAdeleStageTransition_assemble (pos n) (pos (n + 1)) (adjacent_dvd n), ← h,
      LinearEquiv.symm_apply_apply]
  rw [he]
  exact Subtype.property _

/-- A function belongs to stage `m` exactly when it has no residual above
that stage. The backward implication descends from a stage containing it. -/
public theorem mem_rationalAdeleSchwartzStage_iff_residual (m : ℕ) (f : U) :
    f.val ∈ (Stage m) ↔ ∀ n ≥ m, rationalAdeleStageResidual n f = 0 := by
  constructor
  · intro hf n hmn
    exact rationalAdeleStageResidual_eq_zero n f
      (rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd hmn) hf)
  · intro h
    have descend (n : ℕ) (hmn : m ≤ n) (hn : f.val ∈ Stage n) : f.val ∈ Stage m := by
      induction hmn with
      | refl => exact hn
      | @step n hmn ih =>
        exact ih ((rationalAdeleStageResidual_eq_zero_iff n f hn).mp (h n hmn))
    obtain ⟨k, hk⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.property
    exact descend (max m k) (le_max_left m k)
      (rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_right m k)) hk)

end Masullo
