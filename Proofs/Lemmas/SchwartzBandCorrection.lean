module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Two compactly supported correcting functions, real Fourier parity, and reflection -/

open MeasureTheory FourierTransform
open scoped ContDiff FourierTransform SchwartzMap

namespace Masullo

public noncomputable abbrev bandSchwartzMass := SchwartzMap.integralCLM ℂ (volume : Measure ℝ) (V := ℂ)

private theorem fourier_zero_eq_mass (f : 𝓢(ℝ, ℂ)) : (𝓕 f) 0 = bandSchwartzMass f := by
  rw [congrFun (SchwartzMap.fourier_coe f) 0, Real.fourier_real_eq_integral_exp_smul]
  simp [bandSchwartzMass, SchwartzMap.integralCLM_apply]

public theorem fourierInv_zero_eq_bandSchwartzMass (f : 𝓢(ℝ, ℂ)) : (𝓕⁻ f) 0 = bandSchwartzMass f := by
  rw [SchwartzMap.fourierInv_apply_eq]
  simpa using fourier_zero_eq_mass f

@[expose] public noncomputable def bandSchwartzBump (x : ℝ) : 𝓢(ℝ, ℂ) := by
  let b : ContDiffBump x := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  exact (b.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

public theorem bandSchwartzBump_compact (x : ℝ) : HasCompactSupport (bandSchwartzBump x : ℝ → ℂ) := by
  unfold bandSchwartzBump
  exact (ContDiffBump.hasCompactSupport (f := (⟨1 / 2, 1, by norm_num, by norm_num⟩ :
    ContDiffBump x))).comp_left Complex.ofReal_zero

public theorem bandSchwartzBump_zero : bandSchwartzBump 0 0 = 1 := by
  unfold bandSchwartzBump
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  change (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (by simp [b]), Complex.ofReal_one]

public theorem bandSchwartzBump_two_zero : bandSchwartzBump 2 0 = 0 := by
  unfold bandSchwartzBump
  have h : (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (2 : ℝ)) 0 = 0 := by
    apply ContDiffBump.zero_of_le_dist
    norm_num [Real.dist_eq]
  exact (congrArg Complex.ofReal h).trans Complex.ofReal_zero

public theorem bandSchwartzMass_bump_two_ne : bandSchwartzMass (bandSchwartzBump 2) ≠ 0 := by
  let b : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  change (∫ x : ℝ, (b x : ℂ)) ≠ 0
  have h := integral_ofReal (𝕜 := ℂ) (μ := volume) (f := ⇑b)
  exact h.trans_ne (Complex.ofReal_ne_zero.mpr (b.integral_pos (μ := volume)).ne')

public noncomputable abbrev bandSchwartzReflect :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (D := ℝ) (E := ℝ) (F := ℂ)
    (LinearIsometryEquiv.neg ℝ (E := ℝ))

public theorem fourier_preserves_realSchwartz_even {f : 𝓢(ℝ, ℂ)} (hf : Function.Even f) :
    Function.Even (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := by
  intro x
  have hc : (f : ℝ → ℂ) ∘ Neg.neg = f := funext hf
  simpa only [SchwartzMap.fourier_coe, LinearIsometryEquiv.coe_neg, hc] using
    (Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) (f : ℝ → ℂ) x).symm

public theorem fourierInv_preserves_realSchwartz_even {f : 𝓢(ℝ, ℂ)} (hf : Function.Even f) :
    Function.Even (⇑(𝓕⁻ f : 𝓢(ℝ, ℂ))) := by
  intro x
  have hc : (f : ℝ → ℂ) ∘ Neg.neg = f := funext hf
  simpa only [SchwartzMap.fourierInv_coe, LinearIsometryEquiv.coe_neg, hc] using
    (Real.fourierInv_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) (f : ℝ → ℂ) x).symm

end Masullo
