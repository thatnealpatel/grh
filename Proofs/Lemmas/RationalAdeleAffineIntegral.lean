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

/-- Inverse affine precomposition preserves `L¹` on the rational adeles. -/
public theorem integrable_rationalAdele_inv_affine {f : A → ℂ} (hf : Integrable f μA)
    (a : A) (g : J) : Integrable (fun x : A ↦ f ((g⁻¹ : J) * (x - a))) μA := by
  let e := (ContinuousAddEquiv.mulLeft g).toHomeomorph.toMeasurableEquiv
  have h : Integrable f (Measure.map e.symm μA) := by
    change Integrable f (Measure.map (fun x : A ↦ (g⁻¹ : J) * x) μA)
    rw [map_inv_dilate]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have h' : Integrable (fun x : A ↦ f ((g⁻¹ : J) * x)) μA :=
    (integrable_map_equiv e.symm f).mp h
  simpa only [Function.comp_def, sub_eq_add_neg, add_comm _ (-a)] using
    (measurePreserving_add_left μA (-a)).integrable_comp_of_integrable h'

/-- Change variables by `x = a + g*z`, with the direct modulus. -/
public theorem integral_rationalAdele_affine (f : A → ℂ) (a : A) (g : J) :
    (∫ x, f x ∂μA) = ideleNorm g • ∫ z, f (a + (g : A) * z) ∂μA := by
  let e := (ContinuousAddEquiv.mulLeft g).toHomeomorph.toMeasurableEquiv
  have h := e.symm.measurableEmbedding.integral_map (μ := μA) (fun z ↦ f (a + e z))
  change (∫ z, f (a + e z) ∂(Measure.map (fun x : A ↦ (g⁻¹ : J) * x) μA)) = _ at h
  have hg : 0 ≤ ideleNorm g := (ideleClassNorm_mk g ▸ ideleClassNorm_pos (QuotientGroup.mk g)).le
  rw [map_inv_dilate, integral_smul_measure, ENNReal.toReal_ofReal hg] at h
  simp only [MeasurableEquiv.apply_symm_apply, integral_add_left_eq_self] at h
  exact h.symm

end Masullo
