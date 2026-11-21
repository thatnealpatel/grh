module

public import Props.RationalAdeleStageCoordinates
public import Theorems.RationalAdeleAddHaar
public import Lemmas.RationalAdeleStageApproximation
import Lemmas.RationalAdeleAffineIntegral
import Lemmas.RationalAdeleStageFourier
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Prod

/-! # Squared norm of a rational adelic stage

The real marginal on each clopen cell is Lebesgue measure scaled by `1/M`.
Disjointness then gives the squared norm on assembled real profiles.
-/

open NumberField MeasureTheory Set
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "S" => 𝓢(ℝ, ℂ)
local notation "μA" => rationalAdeleAddHaar
local notation "W" => (rationalIntegralAdeles : Set A)

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

private theorem map_real_restrict_integral :
    Measure.map rationalAdeleReal (Measure.restrict μA W) = volume := by
  let j := rationalAdeleIntegralEmbedding
  have hj : MeasurableEmbedding j := isOpenEmbedding_rationalAdeleIntegralEmbedding.measurableEmbedding
  rw [← range_rationalAdeleIntegralEmbedding, ← hj.map_comap,
    Measure.map_map continuous_rationalAdeleReal.measurable hj.measurable,
    comap_rationalAdeleAddHaar_integral]
  have he : rationalAdeleReal ∘ j = Prod.fst := funext rationalIntegralAdelesHomeomorph_real
  rw [he, (measurePreserving_fst (μ := volume) (ν := rationalFiniteIntegersHaar)).map_eq]

/-- The real projection of Haar restricted to one adelic cell is `dt / M`. -/
public theorem map_real_restrict_rationalAdeleStageCell {M : ℕ} (hM : 0 < M) (j : Fin (M ^ 2)) :
    Measure.map rationalAdeleReal (Measure.restrict μA (rationalAdeleStageCell M j)) =
      ENNReal.ofReal ((M : ℝ)⁻¹) • volume := by
  let a := rationalAdeleStageCenter M j
  let g := rationalAdeleStageScale M hM
  let e : A → A := fun x ↦ (g⁻¹ : _) * (x - a)
  have hm : Measurable e := (continuous_const.mul (continuous_id.sub continuous_const)).measurable
  have hr : rationalAdeleReal ∘ e = rationalAdeleReal := by
    funext x
    rw [Function.comp_apply, rationalAdeleReal_apply (e x)]
    change (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
      (1 * (x.1 Rat.infinitePlace - 0)) = _
    rw [sub_zero, one_mul, rationalAdeleReal_apply]
  have hc : e ⁻¹' W = rationalAdeleStageCell M j :=
    Set.ext (rationalAdeleStageCell_box_mem hM j)
  rw [← hc, ← hr, ← Measure.map_map continuous_rationalAdeleReal.measurable hm,
    ← Measure.restrict_map hm isOpen_rationalIntegralAdeles.measurableSet,
    show Measure.map e μA = _ from map_rationalAdele_inv_affine a g,
    ideleNorm_rationalAdeleStageScale hM, Measure.restrict_smul,
    Measure.map_smul _ continuous_rationalAdeleReal.measurable.aemeasurable, map_real_restrict_integral]

/-- Assemblies of real `L²` profiles are in adelic `L²`, with squared norms
summed with the common finite Haar mass of a cell. -/
public theorem rationalAdeleAssembleProfiles_norm_sq {M : ℕ} (hM : 0 < M)
    (b : Fin (M ^ 2) → ℝ → ℂ) (hb : ∀ j, MemLp (b j) 2 volume) :
    let f := rationalAdeleAssembleProfiles M b
    MemLp f 2 μA ∧
      (∫ x, ‖f x‖ ^ 2 ∂μA) = (M : ℝ)⁻¹ * ∑ j, ∫ t, ‖b j t‖ ^ 2 := by
  classical
  dsimp only
  let C := rationalAdeleStageCell M
  let w : ℝ := (M : ℝ)⁻¹
  let u (j : Fin (M ^ 2)) := (C j).indicator (b j ∘ rationalAdeleReal)
  have hm (j : Fin (M ^ 2)) : MeasurableSet (C j) :=
    (isClopen_rationalAdeleStageCell M j).2.measurableSet
  have hmap (j : Fin (M ^ 2)) : MemLp (b j) 2 (Measure.map rationalAdeleReal (Measure.restrict μA (C j))) := by
    rw [map_real_restrict_rationalAdeleStageCell hM j]
    exact (hb j).smul_measure ENNReal.ofReal_ne_top
  have hu (j : Fin (M ^ 2)) : MemLp (u j) 2 μA :=
    (memLp_indicator_iff_restrict (hm j).nullMeasurableSet).2
      ((hmap j).comp_of_map continuous_rationalAdeleReal.measurable.aemeasurable)
  refine ⟨memLp_finsetSum Finset.univ (fun j _ ↦ hu j), ?_⟩
  have hcell (j : Fin (M ^ 2)) :
      (∫ x, ‖u j x‖ ^ 2 ∂μA) = w * ∫ t, ‖b j t‖ ^ 2 := by
    have he : (fun x ↦ ‖u j x‖ ^ 2) = (C j).indicator (fun x ↦ ‖b j (rationalAdeleReal x)‖ ^ 2) := by
      funext x
      by_cases hx : x ∈ C j <;> simp [u, hx]
    rw [he, integral_indicator (hm j), ← integral_map continuous_rationalAdeleReal.measurable.aemeasurable
      ((hmap j).integrable_norm_pow (by decide : 2 ≠ 0)).aestronglyMeasurable,
      map_real_restrict_rationalAdeleStageCell hM j, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have he : (fun x ↦ ‖rationalAdeleAssembleProfiles M b x‖ ^ 2) = fun x ↦ ∑ j, ‖u j x‖ ^ 2 := by
    funext x
    by_cases hx : x ∈ rationalAdeleStageSupport M
    · obtain ⟨j, hj, hj'⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
      rw [rationalAdeleAssembleProfiles_on_cell hM b hj, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · simp [u, C, hj]
      · intro k _ hkj
        have hk : x ∉ C k := fun h ↦ hkj (hj' k h)
        simp [u, hk]
    · rw [rationalAdeleAssembleProfiles_off_stage hM b hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hj : x ∉ C j := fun h ↦ hx (rationalAdeleStageCell_subset_support hM j h)
      simp [u, hj]
  rw [he, integral_finsetSum _ (fun j _ ↦ (hu j).integrable_norm_pow (by decide : 2 ≠ 0))]
  simp_rw [hcell, Finset.mul_sum, w]

omit [MeasurableSpace A] [BorelSpace A] in
/-- Inverse Schwartz coordinates give the cell assembly of the underlying real profiles. -/
public theorem rationalAdeleStageCoordinates_symm_eq_assembleProfiles {M : ℕ} (hM : 0 < M)
    (b : Fin (M ^ 2) → S) :
    ((rationalAdeleStageCoordinates hM).symm b).val = rationalAdeleAssembleProfiles M (fun j ↦ b j) := by
  funext x
  by_cases hx : x ∈ rationalAdeleStageSupport M
  · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM x).mp hx
    rw [rationalAdeleAssembleProfiles_on_cell hM _ hj, ← rationalAdeleStageCoordinates_eq_on_cell hM _ hj,
      LinearEquiv.apply_symm_apply]
  · rw [rationalAdeleAssembleProfiles_off_stage hM _ hx]
    exact ((rationalAdeleStageCoordinates hM).symm b).property.1 x hx

/-- Squared norms in Schwartz coordinates are the weighted real squared norms. -/
public theorem rationalAdeleStage_integrable_integral_norm_sq {M : ℕ} (hM : 0 < M)
    (b : Fin (M ^ 2) → S) :
    let f := ((rationalAdeleStageCoordinates hM).symm b).val
    Integrable (fun x ↦ ‖f x‖ ^ 2) μA ∧
      (∫ x, ‖f x‖ ^ 2 ∂μA) = (M : ℝ)⁻¹ * ∑ j, ∫ t, ‖b j t‖ ^ 2 := by
  dsimp only
  rw [rationalAdeleStageCoordinates_symm_eq_assembleProfiles hM b]
  obtain ⟨hf, he⟩ := rationalAdeleAssembleProfiles_norm_sq hM (fun j ↦ b j) (fun j ↦ (b j).memLp 2 volume)
  exact ⟨hf.integrable_norm_pow (by decide), he⟩

end Masullo
