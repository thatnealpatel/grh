module

public import Theorems.IdeleClassSeparation
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # The regular class-Haar convolution kernel

Masullo, §1.2.1(3), p. 15, uses the kernel `φ (x / y)` for the inverse-left
convolution on the middle isotype. We check the scalar integral on continuous
isotype test inputs, against Haar, as in p. 14 and (9.3.1.2), p. 419. This is
not an identification of the general completed Hardy–Sobolev action.
-/

open MeasureTheory NumberField
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)

section Haar

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  (μ : Measure (IdeleClassGroup (𝓞 K) K)) [μ.IsHaarMeasure]

/-- For a continuous compactly supported kernel and a continuous input, both
integrands are integrable at every output point. The change of variables
uses the same class Haar measure on both sides. -/
public theorem ideleClass_convolution_kernel {φ ψ : C → ℂ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hψ : Continuous ψ) (x : C) :
    Integrable (fun g ↦ φ g * ψ (g⁻¹ * x)) μ ∧
    Integrable (fun y ↦ φ (x / y) * ψ y) μ ∧
    (∫ g, φ g * ψ (g⁻¹ * x) ∂μ) = ∫ y, φ (x / y) * ψ y ∂μ := by
  let : T2Space C := t2Space_ideleClassGroup
  let : μ.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular μ
  let f (g : C) : ℂ := φ g * ψ (g⁻¹ * x)
  have ht : Continuous (fun g : C ↦ g⁻¹ * x) := by fun_prop
  have hf : Continuous f := hφ.mul (hψ.comp ht)
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hc.mul_right
  have hsub (y : C) : (x / y)⁻¹ * x = y := by
    calc
      (x / y)⁻¹ * x = x * (x / y)⁻¹ := mul_comm ((x / y)⁻¹ : C) x
      _ = x / (x / y) := (div_eq_mul_inv x (x / y)).symm
      _ = y := div_div_cancel x y
  have heq (y : C) : f (x / y) = φ (x / y) * ψ y := by simp only [f, hsub]
  refine ⟨hfi, ?_, ?_⟩
  · simpa only [← heq] using hfi.comp_div_left x
  · simpa only [heq] using (integral_div_left_eq_self f μ x).symm

/-- On continuous inputs in the `χ`-isotype for inverse-left translation,
the Haar kernel formula has the same pointwise `χ`-equivariance. This
applies directly to the input, with no projection or extension by zero. -/
public theorem ideleClass_convolution_kernel_isotype {φ ψ : C → ℂ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hψ : Continuous ψ) (χ : PontryaginDual C₁)
    (hχ : ∀ (h : C₁) (y : C), ψ ((h : C)⁻¹ * y) = (χ h : ℂ) * ψ y) (h : C₁) (x : C) :
    (∫ y, φ (((h : C)⁻¹ * x) / y) * ψ y ∂μ) = (χ h : ℂ) * ∫ y, φ (x / y) * ψ y ∂μ := by
  rw [← (ideleClass_convolution_kernel μ hφ hc hψ _).2.2,
    ← (ideleClass_convolution_kernel μ hφ hc hψ x).2.2, ← integral_const_mul]
  congr 1
  funext g
  rw [mul_left_comm (g⁻¹ : C) ((h : C)⁻¹) x, hχ h (g⁻¹ * x)]
  exact mul_left_comm (φ g) (χ h : ℂ) (ψ (g⁻¹ * x))

end Haar

/-- If the topological support lies strictly above `b`, the Haar kernel
vanishes throughout the closed below-threshold region. The comparison is
against the norm of the second variable, not an additive displacement. -/
public theorem ideleClass_convolution_kernel_eq_zero_of_norm_le {φ : C → ℂ} {b : ℝ}
    (hφ : tsupport φ ⊆ {g | b < ideleClassNorm g}) {x y : C}
    (hxy : ideleClassNorm x ≤ b * ideleClassNorm y) : φ (x / y) = 0 := by
  by_contra hn
  have hlt := hφ (subset_tsupport _ (show x / y ∈ Function.support φ from hn))
  change b < ideleClassNorm (x / y) at hlt
  rw [div_eq_mul_inv, map_mul, map_inv, ← div_eq_mul_inv, lt_div_iff₀ (ideleClassNorm_pos y)] at hlt
  exact (not_lt_of_ge hxy) hlt

/-- Diagonal vanishing needs support above one, without a specified gap. -/
public theorem ideleClass_convolution_kernel_diagonal {φ : C → ℂ}
    (hφ : tsupport φ ⊆ {g | 1 < ideleClassNorm g}) (x : C) : φ (x / x) = 0 :=
  ideleClass_convolution_kernel_eq_zero_of_norm_le hφ (by rw [one_mul])

end Masullo
