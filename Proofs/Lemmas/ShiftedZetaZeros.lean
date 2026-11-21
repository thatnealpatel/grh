module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic.Linarith

/-!
# The shifted critical-strip zeta zeros

This is the rational trivial-isotype family used in the project comparison
of the full divisor at (B.4.2.2), p. 614, with the capped critical-line sum
at (13.3.1.3), p. 522. Here the index keeps distinct locations, not orders.
The geometric properties of this family use Mathlib, not either trace formula.
-/

open Set

namespace Masullo

/-- The distinct zeros of ζ in the open critical strip. -/
public noncomputable def criticalStripZetaZeros : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

public theorem mem_criticalStripZetaZeros {ρ : ℂ} :
    ρ ∈ criticalStripZetaZeros ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := Iff.rfl

/-- Translate the critical line to the imaginary axis. -/
@[expose] public noncomputable def shiftedZetaZero (ρ : criticalStripZetaZeros) : ℂ :=
  (ρ : ℂ) - 1 / 2

public theorem shiftedZetaZero_injective : Function.Injective shiftedZetaZero := by
  intro ρ σ h
  exact Subtype.ext (sub_left_inj.mp h)

public theorem abs_re_shiftedZetaZero_lt (ρ : criticalStripZetaZeros) :
    |(shiftedZetaZero ρ).re| < (1 / 2 : ℝ) := by
  obtain ⟨_, hpos, hlt⟩ := ρ.property
  have hshift : (shiftedZetaZero ρ).re = (ρ : ℂ).re - 1 / 2 := by
    simp [shiftedZetaZero]
  rw [hshift, abs_lt]
  constructor <;> linarith

/-- Only finitely many shifted zeros lie in a given compact set. -/
public theorem shiftedZetaZero_preimage_finite {K : Set ℂ} (hK : IsCompact K) :
    (shiftedZetaZero ⁻¹' K).Finite := by
  -- Translate back before applying Mathlib's theorem for the unshifted zeros.
  have hK' : IsCompact ((fun z : ℂ ↦ z + 1 / 2) '' K) :=
    hK.image (continuous_id.add continuous_const)
  refine (hK'.inter_riemannZetaZeros_finite.preimage Subtype.val_injective.injOn).subset ?_
  intro ρ hρ
  exact ⟨⟨shiftedZetaZero ρ, hρ, sub_add_cancel _ _⟩,
    mem_riemannZetaZeros.mpr ρ.property.1⟩

public instance : Countable criticalStripZetaZeros := by
  rw [← countable_univ_iff, ← preimage_univ (f := shiftedZetaZero),
    ← Metric.iUnion_closedBall_nat (0 : ℂ), preimage_iUnion]
  exact countable_iUnion fun n ↦
    (shiftedZetaZero_preimage_finite (isCompact_closedBall (0 : ℂ) n)).countable

/-- Each complex point has positive distance from all shifted zeros other than itself. -/
public theorem shiftedZetaZero_separated (z : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : criticalStripZetaZeros,
      shiftedZetaZero ρ ≠ z → δ ≤ ‖z - shiftedZetaZero ρ‖ := by
  -- Delete the center from the finite family in the unit ball and take its open complement.
  let F := (shiftedZetaZero '' (shiftedZetaZero ⁻¹' Metric.closedBall z 1)) \ {z}
  have hF : F.Finite :=
    ((shiftedZetaZero_preimage_finite (isCompact_closedBall z 1)).image _).subset sdiff_subset
  have hz : z ∈ Fᶜ := fun h ↦ h.2 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF.isClosed.isOpen_compl z hz
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro ρ hρ
  rw [← dist_eq_norm, dist_comm]
  by_contra! hdist
  have hfar : shiftedZetaZero ρ ∈ Fᶜ := hball <|
    Metric.mem_ball.mpr (hdist.trans_le (min_le_left _ _))
  exact hfar ⟨⟨ρ, Metric.mem_closedBall.mpr (hdist.le.trans (min_le_right _ _)), rfl⟩, hρ⟩

end Masullo
