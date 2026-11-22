module

public import Lemmas.SchwartzGaussian
public import Theorems.ArchimedeanCompletionGaussian
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

import all Theorems.RealGaussianMellin
import all Theorems.ComplexGaussianMellin

/-! # Products of real and complex Gaussian monomials on Euclidean mixed space -/

open NumberField NumberField.mixedEmbedding
open scoped Classical ComplexConjugate SchwartzMap

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

local notation "E" => euclidean.mixedSpace K
set_option quotPrecheck false in
local notation "R" => {v : InfinitePlace K // v.IsReal}
set_option quotPrecheck false in
local notation "C" => {v : InfinitePlace K // v.IsComplex}

private def realCoordinate (v : R) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj v).comp ((ContinuousLinearMap.fst ℝ (R → ℝ) (C → ℂ)).comp
    (euclidean.toMixed K).toContinuousLinearMap)

private def complexCoordinate (v : C) : E →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj v).comp ((ContinuousLinearMap.snd ℝ (R → ℝ) (C → ℂ)).comp
    (euclidean.toMixed K).toContinuousLinearMap)

private def gaussianScale : E ≃L[ℝ] E :=
  let e := WithLp.linearEquiv 2 ℝ
    (EuclideanSpace ℝ {v : InfinitePlace K // v.IsReal} ×
      EuclideanSpace ℂ {v : InfinitePlace K // v.IsComplex})
  let πr := Real.sqrt Real.pi
  let πc := Real.sqrt (2 * Real.pi)
  let er := LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ R) πr (Real.sqrt_pos.2 Real.pi_pos).ne'
  let ec := LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℂ C) πc
    (Real.sqrt_pos.2 (show 0 < 2 * Real.pi by positivity)).ne'
  (e.trans ((er.prodCongr ec).trans e.symm)).toContinuousLinearEquiv

private theorem gaussianScale_norm_sq (x : E) :
    ‖gaussianScale x‖ ^ 2 =
      (∑ v : R, Real.pi * ((euclidean.toMixed K x).1 v) ^ 2) +
        ∑ v : C, 2 * Real.pi * ‖(euclidean.toMixed K x).2 v‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖Real.sqrt Real.pi • x.fst‖ ^ 2 + ‖Real.sqrt (2 * Real.pi) • x.snd‖ ^ 2 = _
  simp only [_root_.norm_smul, mul_pow, Real.norm_eq_abs (Real.sqrt _), abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity),
    PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  rfl

private def realMonomial (b : R → ℕ) (x : E) (v : R) : ℂ :=
  (realCoordinate v x : ℂ) ^ b v

private def complexMonomial (m : C → ℤ) (x : E) (v : C) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) *
    (if 0 ≤ m v then conj (complexCoordinate v x) ^ (m v).toNat
      else complexCoordinate v x ^ (m v).natAbs)

private theorem temperate_prod {ι : Type*} [Fintype ι] (p : ι → E → ℂ)
    (hp : ∀ i, (p i).HasTemperateGrowth) : (fun x ↦ ∏ i, p i x).HasTemperateGrowth := by
  classical
  suffices ∀ s : Finset ι, (fun x ↦ ∏ i ∈ s, p i x).HasTemperateGrowth by exact this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (Function.HasTemperateGrowth.const (1 : ℂ) : (fun _ : E ↦ (1 : ℂ)).HasTemperateGrowth)
  | insert i s hi ih => simpa only [Finset.prod_insert hi] using (hp i).fun_mul ih

private theorem realMonomial_temperate (b : R → ℕ) (v : R) :
    (fun x : E ↦ realMonomial b x v).HasTemperateGrowth :=
  (Complex.hasTemperateGrowth_ofReal.comp (realCoordinate v).hasTemperateGrowth).pow (b v)

private theorem complexMonomial_temperate (m : C → ℤ) (v : C) :
    (fun x : E ↦ complexMonomial m x v).HasTemperateGrowth := by
  have h := (complexCoordinate v).hasTemperateGrowth
  have hc : (fun _ : E ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ)).HasTemperateGrowth :=
    Function.HasTemperateGrowth.const _
  by_cases hm : 0 ≤ m v
  · simpa only [complexMonomial, ite_eq_left hm, Pi.pow_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using
      hc.fun_mul ((Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth.comp h).pow (m v).toNat)
  · simpa only [complexMonomial, ite_eq_right hm, Pi.pow_apply] using hc.fun_mul (h.pow (m v).natAbs)

private theorem monomialProduct_temperate (b : R → ℕ) (m : C → ℤ) :
    (fun x : E ↦ (∏ v, realMonomial b x v) * ∏ v, complexMonomial m x v).HasTemperateGrowth :=
  (temperate_prod (fun v x ↦ realMonomial b x v) (realMonomial_temperate b)).mul
    (temperate_prod (fun v x ↦ complexMonomial m x v) (complexMonomial_temperate m))

/-- Gaussian monomials of widths `π` and `2π` in the real and complex blocks. -/
public def mixedSchwartzGaussian (b : R → ℕ) (m : C → ℤ) : 𝓢(E, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ).flip (monomialProduct_temperate b m)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ gaussianScale (schwartzGaussian E))

public theorem mixedSchwartzGaussian_apply (b : R → ℕ) (m : C → ℤ) (x : E) :
    mixedSchwartzGaussian b m x =
      (∏ v, realZetaGaussian (b v) ((euclidean.toMixed K x).1 v)) *
        ∏ v, complexZetaGaussian (m v) ((euclidean.toMixed K x).2 v) := by
  rw [mixedSchwartzGaussian, SchwartzMap.bilinLeftCLM_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change ((∏ v, realMonomial b x v) * ∏ v, complexMonomial m x v) *
    schwartzGaussian E (gaussianScale x) = _
  rw [schwartzGaussian_apply, gaussianScale_norm_sq]
  simp only [neg_add, ← Finset.sum_neg_distrib, Real.exp_add, Real.exp_sum, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_exp, Complex.ofReal_neg, realZetaGaussian, complexZetaGaussian, mul_assoc,
    Finset.prod_mul_distrib]
  have hr (v : R) : realCoordinate v x = (euclidean.toMixed K x).1 v := rfl
  have hc (v : C) : complexCoordinate v x = (euclidean.toMixed K x).2 v := rfl
  simp only [realMonomial, complexMonomial, hr, hc, Finset.prod_mul_distrib]
  ac_rfl

end

end Masullo
