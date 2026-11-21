module

public import Props.RationalAdeleStageCoordinates
import Lemmas.RationalAdeleAffineIntegral
import Lemmas.RationalAdeleStageFourier
import Mathlib.MeasureTheory.Integral.Prod

/-! # Squared norm of a rational adelic Schwartz stage

The finite cells are disjoint, and each has finite Haar mass `1/M`.
These coordinates therefore give the squared norm with weight `1/M` on
all `M²` copies of the real Schwartz space.
-/

open NumberField MeasureTheory
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "S" => 𝓢(ℝ, ℂ)
local notation "μA" => rationalAdeleAddHaar
local notation "W" => (rationalIntegralAdeles : Set A)

set_option linter.concreteInstances false

private theorem unramified_sq (b : S) :
    (fun x ↦ ‖rationalAdeleUnramified b x‖ ^ 2) =
      Set.indicator W (fun x ↦ ‖b (rationalAdeleReal x)‖ ^ 2) := by
  funext x
  by_cases hx : x ∈ W <;> simp [rationalAdeleUnramified, hx]

variable [MeasurableSpace A] [BorelSpace A]

private theorem integrable_unramified_sq (b : S) :
    Integrable (fun x ↦ ‖rationalAdeleUnramified b x‖ ^ 2) μA := by
  rw [unramified_sq, integrable_indicator_iff isOpen_rationalIntegralAdeles.measurableSet]
  let j := rationalAdeleIntegralEmbedding
  have hj : MeasurableEmbedding j := isOpenEmbedding_rationalAdeleIntegralEmbedding.measurableEmbedding
  change Integrable (fun a ↦ ‖b (rationalAdeleReal a)‖ ^ 2) (Measure.restrict μA W)
  rw [← range_rationalAdeleIntegralEmbedding, ← hj.map_comap, hj.integrable_map_iff,
    comap_rationalAdeleAddHaar_integral]
  change Integrable (fun z : ℝ × RationalFiniteIntegers ↦
    ‖b (rationalAdeleReal (rationalIntegralAdelesHomeomorph z : A))‖ ^ 2)
    (volume.prod rationalFiniteIntegersHaar)
  simpa only [rationalIntegralAdelesHomeomorph_real] using
    ((b.memLp 2 volume).integrable_norm_pow (by decide : 2 ≠ 0)).comp_fst rationalFiniteIntegersHaar

private theorem integral_unramified_sq (b : S) :
    (∫ x, ‖rationalAdeleUnramified b x‖ ^ 2 ∂μA) = ∫ t, ‖b t‖ ^ 2 := by
  let j := rationalAdeleIntegralEmbedding
  have hj : MeasurableEmbedding j := isOpenEmbedding_rationalAdeleIntegralEmbedding.measurableEmbedding
  rw [unramified_sq, integral_indicator isOpen_rationalIntegralAdeles.measurableSet,
    ← range_rationalAdeleIntegralEmbedding, ← hj.map_comap, hj.integral_map,
    comap_rationalAdeleAddHaar_integral]
  change (∫ z : ℝ × RationalFiniteIntegers,
    ‖b (rationalAdeleReal (rationalIntegralAdelesHomeomorph z : A))‖ ^ 2
    ∂(volume.prod rationalFiniteIntegersHaar)) = _
  simp only [rationalIntegralAdelesHomeomorph_real]
  rw [integral_fun_fst (fun t : ℝ ↦ ‖b t‖ ^ 2)]
  simp [Measure.real]

/-- Squared norms on a rational stage integrate as the sum of the real
squared norms with the common Haar mass of a cell. -/
public theorem rationalAdeleStage_integrable_integral_norm_sq {M : ℕ} (hM : 0 < M)
    (b : Fin (M ^ 2) → S) :
    let f := ((rationalAdeleStageCoordinates hM).symm b).val
    Integrable (fun x ↦ ‖f x‖ ^ 2) μA ∧
      (∫ x, ‖f x‖ ^ 2 ∂μA) = (M : ℝ)⁻¹ * ∑ j, ∫ t, ‖b j t‖ ^ 2 := by
  classical
  dsimp only
  let f := (rationalAdeleStageCoordinates hM).symm b
  let a := rationalAdeleStageCenter M
  let g := rationalAdeleStageScale M hM
  let q (j : Fin (M ^ 2)) (x : A) := ‖rationalAdeleBox (b j) (a j) g x‖ ^ 2
  have hq (j : Fin (M ^ 2)) : Integrable (q j) μA :=
    integrable_rationalAdele_inv_affine (integrable_unramified_sq (b j)) (a j) g
  have hcell (j : Fin (M ^ 2)) : (∫ x, q j x ∂μA) = (M : ℝ)⁻¹ * ∫ t, ‖b j t‖ ^ 2 := by
    rw [integral_rationalAdele_affine (q j) (a j) g, ideleNorm_rationalAdeleStageScale hM]
    simp_rw [q, rationalAdeleBox_at_affine, integral_unramified_sq, smul_eq_mul]
  have he : (fun x ↦ ‖f.val x‖ ^ 2) = fun x ↦ ∑ j, q j x := by
    funext x
    by_cases hx : x ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, hu⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
      rw [← rationalAdeleStageCoordinates_eq_on_cell hM f hj, show
        rationalAdeleStageCoordinates hM f = b from LinearEquiv.apply_symm_apply _ _,
        Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · simp only [q, a, g, rationalAdeleBox_stageCell, Set.indicator_of_mem hj]
      · intro k _ hkj
        have hk : x ∉ rationalAdeleStageCell M k := fun hm ↦ hkj (hu k hm)
        simp [q, a, g, rationalAdeleBox_stageCell, hk]
    · rw [f.property.1 x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hj : x ∉ rationalAdeleStageCell M j := fun h ↦
        hx (rationalAdeleStageCell_subset_support hM j h)
      simp [q, a, g, rationalAdeleBox_stageCell, hj]
  change Integrable (fun x ↦ ‖f.val x‖ ^ 2) μA ∧ _
  rw [he, integral_finsetSum _ (fun j _ ↦ hq j)]
  exact ⟨integrable_finsetSum _ (fun j _ ↦ hq j), by simp_rw [hcell, Finset.mul_sum]⟩

end Masullo
