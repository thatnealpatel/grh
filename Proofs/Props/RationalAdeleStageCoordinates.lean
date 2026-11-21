module

public import Lemmas.RationalAdeleStageSampling

/-! # Schwartz coordinates of a rational adelic stage

In the proof of Proposition 2.1.3.2, pp. 69–70, the finite stage for
`H ⊆ K` uses functions on `K/H`, extended by zero outside `K`.
For the rational pair `M ℤ̂ ⊆ M⁻¹ ℤ̂`, we identify the corresponding
adelic stage with `M²` copies of the real Schwartz space by sampling.
The equivalence here is linear, not an assertion about the LF topology.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ

/-- Functions on the stage vanish off the support cylinder and are invariant
under finite translations by `M ℤ̂`. Those with Schwartz real slices are
linearly equivalent to one real Schwartz space per finite coset. -/
public noncomputable def rationalAdeleStageCoordinates {M : ℕ} (hM : 0 < M) :
    rationalAdeleSchwartzStage M ≃ₗ[ℂ] (Fin (M ^ 2) → 𝓢(ℝ, ℂ)) := by
  refine LinearEquiv.ofBijective (rationalAdeleStageSample M)
    ⟨rationalAdeleStageSample_injective hM, ?_⟩
  intro b
  obtain ⟨a, g, h⟩ := exists_rationalAdeleBoxSum_stage_coordinates hM
  obtain ⟨u, _, hu⟩ := exists_rationalAdeleStageSample_eq_of_assembled hM
    (rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g) b (h b).1 (h b).2
  exact ⟨u, hu⟩

/-- The forward map samples along the real line at the finite representative. -/
public theorem rationalAdeleStageCoordinates_apply {M : ℕ} (hM : 0 < M)
    (f : rationalAdeleSchwartzStage M) (j : Fin (M ^ 2)) (t : ℝ) :
    rationalAdeleStageCoordinates hM f j t =
      f.val (rationalAdeleAt t (rationalAdeleStageRepresentative M j)) :=
  rationalAdeleStageSample_apply f j t

/-- The inverse to sampling is the same fixed-geometry assembly used by the
uniform box estimates, with coefficient one on each cell. -/
public theorem exists_rationalAdeleStageCoordinates_symm_eq_boxSum {M : ℕ} (hM : 0 < M) :
    ∃ (a : Fin (M ^ 2) → A) (g : Fin (M ^ 2) → J), ∀ b : Fin (M ^ 2) → 𝓢(ℝ, ℂ),
      ((rationalAdeleStageCoordinates hM).symm b).val =
        rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g := by
  obtain ⟨a, g, h⟩ := exists_rationalAdeleBoxSum_stage_coordinates hM
  refine ⟨a, g, fun b ↦ ?_⟩
  obtain ⟨u, hval, hu⟩ := exists_rationalAdeleStageSample_eq_of_assembled hM
    (rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g) b (h b).1 (h b).2
  have he : rationalAdeleStageCoordinates hM u = b := hu
  rw [← hval, ← he, LinearEquiv.symm_apply_apply]

end Masullo
