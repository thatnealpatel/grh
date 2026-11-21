module

public import Theorems.RationalAdeleAdditiveDilation
import Mathlib.MeasureTheory.Group.Integral

/-! # Affine change of variables on the rational adeles -/

open NumberField MeasureTheory

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

private theorem map_inv_dilate (g : J) :
    Measure.map (fun x : A ↦ (g⁻¹ : J) * x) μA = ENNReal.ofReal (ideleNorm g) • μA := by
  let e := (ContinuousAddEquiv.mulLeft g).toHomeomorph.toMeasurableEquiv
  change Measure.map e.symm μA = _
  rw [MeasurableEquiv.map_symm]
  exact comap_rationalAdeleAddHaar_dilate g

/-- Inverse affine pushforward scales Haar by the modulus of the direct map. -/
public theorem map_rationalAdele_inv_affine (a : A) (g : J) :
    Measure.map (fun x : A ↦ (g⁻¹ : J) * (x - a)) μA = ENNReal.ofReal (ideleNorm g) • μA := by
  let f : A → A := fun x ↦ x - a
  let d : A → A := fun x ↦ (g⁻¹ : J) * x
  have hf : Measure.map f μA = μA := by
    simpa only [f, sub_eq_add_neg, add_comm _ (-a)] using (measurePreserving_add_left μA (-a)).map_eq
  have hfm : Measurable f := (continuous_id.sub continuous_const).measurable
  have hdm : Measurable d := (continuous_const.mul continuous_id).measurable
  change Measure.map (d ∘ f) μA = _
  rw [← Measure.map_map hdm hfm, hf]
  exact map_inv_dilate g

/-- Inverse affine precomposition preserves `L¹` on the rational adeles. -/
public theorem integrable_rationalAdele_inv_affine {E : Type*} [NormedAddCommGroup E]
    {f : A → E} (hf : Integrable f μA)
    (a : A) (g : J) : Integrable (fun x : A ↦ f ((g⁻¹ : J) * (x - a))) μA := by
  have hm : Measurable (fun x : A ↦ (g⁻¹ : J) * (x - a)) :=
    (continuous_const.mul (continuous_id.sub continuous_const)).measurable
  apply Integrable.comp_aemeasurable _ hm.aemeasurable
  rw [map_rationalAdele_inv_affine]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- Change variables by `x = a + g*z`, with the direct modulus. -/
public theorem integral_rationalAdele_affine {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : A → E) (a : A) (g : J) :
    (∫ x, f x ∂μA) = ideleNorm g • ∫ z, f (a + (g : A) * z) ∂μA := by
  let e := (ContinuousAddEquiv.mulLeft g).toHomeomorph.toMeasurableEquiv
  have h := e.symm.measurableEmbedding.integral_map (μ := μA) (fun z ↦ f (a + e z))
  change (∫ z, f (a + e z) ∂(Measure.map (fun x : A ↦ (g⁻¹ : J) * x) μA)) = _ at h
  have hg : 0 ≤ ideleNorm g := (ideleClassNorm_mk g ▸ ideleClassNorm_pos (QuotientGroup.mk g)).le
  rw [map_inv_dilate, integral_smul_measure, ENNReal.toReal_ofReal hg] at h
  simp only [MeasurableEquiv.apply_symm_apply, integral_add_left_eq_self] at h
  exact h.symm

end Masullo
