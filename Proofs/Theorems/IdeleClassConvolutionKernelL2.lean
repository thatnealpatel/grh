module

public import Theorems.IdeleClassConvolutionKernel
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Pointwise evaluation of the regular class-Haar kernel on `L²`

The scalar Haar integral in Masullo, §1.2.1(3), p. 15, has a representative
at every output point for an `L²` kernel and input. These statements concern
scalar evaluation, not boundedness into a Hardy–Sobolev completion.
-/

open Filter MeasureTheory NumberField
open scoped ENNReal Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K

private theorem integrable_pointwise_mul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun y ↦ f y * g y) ν := by
  rw [show (fun y ↦ f y * g y) = f * g from funext fun y ↦ (Pi.mul_apply f g y).symm]
  exact hf.integrable_mul hg

private theorem ideleClass_inv_mul_eq_div (x g : C) : g⁻¹ * x = x / g := by
  rw [div_eq_mul_inv]
  exact mul_comm (g⁻¹ : C) x

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  (μ : Measure (IdeleClassGroup (𝓞 K) K)) [μ.IsHaarMeasure]

private theorem ideleClass_div_measurePreserving (x : C) :
    MeasurePreserving (fun y : C ↦ x / y) μ μ := by
  let : T2Space C := t2Space_ideleClassGroup
  let : μ.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular μ
  exact Measure.measurePreserving_div_left μ x

private theorem ideleClass_memLp_div_left {f : C → ℂ} (hf : MemLp f 2 μ) (x : C) :
    MemLp (fun y ↦ f (x / y)) 2 μ :=
  hf.comp_measurePreserving (ideleClass_div_measurePreserving μ x)

/-- On class Haar, an `L²` kernel and an `L²` input give integrable products
in both convolution formulas, with the same integral at every `x`. -/
public theorem ideleClass_convolution_kernel_memLp {φ f : C → ℂ}
    (hφ : MemLp φ 2 μ) (hf : MemLp f 2 μ) (x : C) :
    Integrable (fun g ↦ φ g * f (g⁻¹ * x)) μ ∧
    Integrable (fun y ↦ φ (x / y) * f y) μ ∧
    (∫ g, φ g * f (g⁻¹ * x) ∂μ) = ∫ y, φ (x / y) * f y ∂μ := by
  let : T2Space C := t2Space_ideleClassGroup
  let : μ.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular μ
  have hsub (y : C) : (x / y)⁻¹ * x = y := by
    rw [ideleClass_inv_mul_eq_div]
    exact div_div_cancel x y
  exact ⟨by simpa only [ideleClass_inv_mul_eq_div] using
      integrable_pointwise_mul hφ (ideleClass_memLp_div_left μ hf x),
    integrable_pointwise_mul (ideleClass_memLp_div_left μ hφ x) hf,
    by simpa only [hsub] using
      (integral_div_left_eq_self (fun g ↦ φ g * f (g⁻¹ * x)) μ x).symm⟩

/-- Replacing either factor by an a.e.-equal representative leaves every
scalar kernel evaluation unchanged, not just almost every evaluation. -/
public theorem ideleClass_convolution_kernel_ae_congr {φ φ' f f' : C → ℂ}
    (hφ : φ =ᵐ[μ] φ') (hf : f =ᵐ[μ] f') (x : C) :
    (∫ y, φ (x / y) * f y ∂μ) = ∫ y, φ' (x / y) * f' y ∂μ := by
  apply integral_congr_ae
  exact ((ideleClass_div_measurePreserving μ x).quasiMeasurePreserving.ae_eq_comp hφ).mul hf

/-- Cauchy–Schwarz on class Haar gives a bound independent of the output
point. Both `eLpNorm` factors are finite by the `MemLp` hypotheses. -/
public theorem norm_ideleClass_convolution_kernel_le {φ f : C → ℂ}
    (hφ : MemLp φ 2 μ) (hf : MemLp f 2 μ) (x : C) :
    ‖∫ y, φ (x / y) * f y ∂μ‖ ≤ (eLpNorm φ 2 μ).toReal * (eLpNorm f 2 μ).toReal := by
  let k (y : C) := φ (x / y)
  have hk := ideleClass_memLp_div_left μ hφ x
  have hknorm : eLpNorm k 2 μ = eLpNorm φ 2 μ :=
    eLpNorm_comp_measurePreserving hφ.aestronglyMeasurable (ideleClass_div_measurePreserving μ x)
  have h₂ : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ h₂
    hk.aestronglyMeasurable.eNorm hf.aestronglyMeasurable.eNorm
  have haux {g : C → ℂ} (hg : MemLp g 2 μ) :
      eLpNorm g 2 μ = (∫⁻ y, ‖g y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by simp) hg.aestronglyMeasurable]
    norm_num
  rw [← haux hk, ← haux hf, hknorm] at hholder
  calc
    ‖∫ y, φ (x / y) * f y ∂μ‖ ≤ (∫⁻ y, ‖k y‖ₑ * ‖f y‖ₑ ∂μ).toReal := by
      simpa only [ofReal_norm, eNorm_mul, k] using
        (norm_integral_le_lintegral_norm (μ := μ) (fun y ↦ k y * f y))
    _ ≤ (eLpNorm φ 2 μ * eLpNorm f 2 μ).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hφ.eLpNorm_ne_top hf.eLpNorm_ne_top) hholder
    _ = _ := ENNReal.toReal_mul

/-- The scalar kernel evaluation of an a.e. isotypic input satisfies the
character law at every output point. The input a.e. condition is for each
fixed translation, so it does not require a common conull set for all `h`. -/
public theorem ideleClass_convolution_kernel_isotype_ae {φ f : C → ℂ}
    (hφ : MemLp φ 2 μ) (hf : MemLp f 2 μ) (χ : PontryaginDual (ideleClassNormOne (K := K)))
    (h : ideleClassNormOne (K := K))
    (hχ : (fun y : C ↦ f ((h : C)⁻¹ * y)) =ᵐ[μ] fun y ↦ (χ h : ℂ) * f y) (x : C) :
    (∫ y, φ (((h : C)⁻¹ * x) / y) * f y ∂μ) = (χ h : ℂ) * ∫ y, φ (x / y) * f y ∂μ := by
  rw [← (ideleClass_convolution_kernel_memLp μ hφ hf _).2.2,
    ← (ideleClass_convolution_kernel_memLp μ hφ hf x).2.2, ← integral_const_mul]
  apply integral_congr_ae
  have he := (ideleClass_div_measurePreserving μ x).quasiMeasurePreserving.ae_eq_comp hχ
  filter_upwards [he] with g hg
  change f ((h : C)⁻¹ * (x / g)) = (χ h : ℂ) * f (x / g) at hg
  rw [mul_left_comm (g⁻¹ : C) ((h : C)⁻¹) x, ideleClass_inv_mul_eq_div x g, hg]
  exact mul_left_comm (φ g) (χ h : ℂ) (f (x / g))

private theorem dist_kernel_le_of_measure_le {ν : Measure C} (hμν : μ ≤ ν)
    {φ : C → ℂ} (hφ : MemLp φ 2 μ) (u v : Lp ℂ 2 ν) (x : C) :
    dist (∫ y, φ (x / y) * u y ∂μ) (∫ y, φ (x / y) * v y ∂μ) ≤
      (eLpNorm φ 2 μ).toReal * dist u v := by
  have hu := (Lp.memLp u).mono_measure hμν
  have hv := (Lp.memLp v).mono_measure hμν
  have hdiff : (fun y ↦ φ (x / y) * u y - φ (x / y) * v y) =ᵐ[μ]
      fun y ↦ φ (x / y) * (u - v) y := by
    filter_upwards [hμν.absolutelyContinuous.ae_le (Lp.coeFn_sub u v)] with y hy
    rw [hy, Pi.sub_apply, mul_sub]
  rw [dist_eq_norm, ← integral_sub (ideleClass_convolution_kernel_memLp μ hφ hu x).2.1
    (ideleClass_convolution_kernel_memLp μ hφ hv x).2.1, integral_congr_ae hdiff]
  have hmono : (eLpNorm (u - v : Lp ℂ 2 ν) 2 μ).toReal ≤ dist u v := by
    rw [dist_eq_norm, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp (u - v)).eLpNorm_ne_top (eLpNorm_mono_measure _ hμν)
  exact (norm_ideleClass_convolution_kernel_le μ hφ ((Lp.memLp (u - v)).mono_measure hμν) x).trans
    (mul_le_mul_of_nonneg_left hmono ENNReal.toReal_nonneg)

/-- `L²(ν)` convergence implies uniform convergence of scalar kernel
integrals if `ν` dominates Haar. In particular one may take `ν = w μ` for a
Haar-a.e. density `w ≥ 1`. The output convergence here is not in `L²(ν)`. -/
public theorem tendstoUniformly_ideleClass_convolution_kernel_of_measure_le
    {ι : Type*} {l : Filter ι} {ν : Measure C} (hμν : μ ≤ ν) {φ : C → ℂ} (hφ : MemLp φ 2 μ)
    {u : ι → Lp ℂ 2 ν} {v : Lp ℂ 2 ν} (hu : Tendsto u l (𝓝 v)) :
    TendstoUniformly (fun i x ↦ ∫ y, φ (x / y) * u i y ∂μ)
      (fun x ↦ ∫ y, φ (x / y) * v y ∂μ) l := by
  have hd : Tendsto (fun i ↦ dist v (u i)) l (𝓝 (dist v v)) := tendsto_const_nhds.dist hu
  have hnorm : Tendsto (fun i ↦ (eLpNorm φ 2 μ).toReal * dist v (u i)) l (𝓝 0) := by
    simpa only [dist_self, mul_zero] using hd.const_mul (eLpNorm φ 2 μ).toReal
  refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ((tendsto_order.mp hnorm).2 ε hε).mono ?_
  intro i hi x
  exact (dist_kernel_le_of_measure_le μ hμν hφ v (u i) x).trans_lt hi

end Masullo
