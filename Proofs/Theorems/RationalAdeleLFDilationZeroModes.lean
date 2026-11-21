module

public import Theorems.RationalAdeleLFDilationDeriv
public import Theorems.RationalAdeleBoxThetaInversion
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Zero modes of the rational real dilation generator

This is the positive real norm-section case of Lemma 2.2.4.5(1), with
the diagonal action on the two moments from (2.2.4.27), pp. 91–95.
At frequency zero the norm factor in (2.2.4.29) must still be differentiated.
-/

open NumberField MeasureTheory
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "D" => rationalAdeleLFDilationDeriv

private theorem real_zero : rationalAdeleReal (0 : A) = 0 := by
  simpa only [map_zero, Rat.cast_zero] using rationalAdeleReal_algebraMap 0

/-- The spatial zero mode of the generator vanishes on every test. -/
public theorem rationalAdeleLFDilationDeriv_at_zero (f : E) : (D f).toUnion.val 0 = 0 := by
  rw [rationalAdeleLFDilationDeriv_apply, real_zero, Complex.ofReal_zero, zero_mul]

private theorem integral_stageEuler (n : ℕ) (b : Fin ((rationalAdeleFactorialLevel n) ^ 2) → 𝓢(ℝ, ℂ))
    (j : Fin ((rationalAdeleFactorialLevel n) ^ 2)) :
    (∫ u, rationalAdeleStageEuler n b j u) = -∫ u, b j u := by
  have h_mul : Integrable (fun u : ℝ ↦ (u : ℂ) * b j u) := by
    have h := (SchwartzMap.smulLeftCLM ℂ Complex.ofReal (b j)).integrable (μ := volume)
    change Integrable (fun u ↦ SchwartzMap.smulLeftCLM ℂ Complex.ofReal (b j) u) at h
    simpa only [SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal,
      smul_eq_mul] using h
  have h_mul_deriv : Integrable (fun u : ℝ ↦ (u : ℂ) * deriv (b j) u) := by
    have h := (rationalAdeleStageEuler n b j).integrable (μ := volume)
    change Integrable (fun u ↦ rationalAdeleStageEuler n b j u) at h
    simpa only [rationalAdeleStageEuler_apply] using h
  have h_id (x : ℝ) : HasDerivAt Complex.ofReal (1 : ℂ) x :=
    Complex.ofRealCLM.hasDerivAt
  simp only [rationalAdeleStageEuler_apply]
  simpa only [one_mul] using integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := Complex.ofReal) (v := (b j : ℝ → ℂ)) (u' := fun _ ↦ 1)
    (fun x _ ↦ h_id x) (fun x _ ↦ (b j).hasDerivAt x) h_mul_deriv
    (by rw [show (fun _ : ℝ ↦ (1 : ℂ)) = 1 from rfl, one_mul]; exact (b j).integrable) h_mul

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

private theorem fourier_boxSum_zero {I : Type*} (s : Finset I) (b : I → 𝓢(ℝ, ℂ))
    (a : I → A) (g : I → J) :
    rationalAdeleFourier (rationalAdeleBoxSum s (fun _ ↦ 1) b a g) 0 =
      ∑ i ∈ s, ideleNorm (g i) • ∫ u, b i u := by
  rw [rationalAdeleFourier, integral_rationalAdeleBoxSum_mul_conj_char]
  have h (p : 𝓢(ℝ, ℂ)) : rationalAdeleUnramified (𝓕 p) (0 : A) = ∫ u, p u := by
    rw [rationalAdeleUnramified, Set.indicator_of_mem rationalIntegralAdeles.zero_mem,
      real_zero, SchwartzMap.fourier_coe, Real.fourier_eq]
    simp
  simp only [mul_zero, AddChar.map_zero_eq_one, map_one, one_mul, h]

/-- The Fourier zero mode of the generator is minus the original Fourier zero mode.
The positive real section has norm `t` at scale `t` (see `ideleNorm_logSection`
with log parameter `log t`), giving the coefficient `-1`. The proof uses
integration by parts on the real profiles, rather than moving a limit
through the adelic integral. -/
public theorem rationalAdeleFourier_LFDilationDeriv_at_zero (f : E) :
    rationalAdeleFourier (D f).toUnion.val 0 = -rationalAdeleFourier f.toUnion.val 0 := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  obtain ⟨a, g, hbox⟩ :=
    exists_rationalAdeleStageCoordinates_symm_eq_boxSum (rationalAdeleFactorialLevel_pos n)
  have h_assembly (b : Fin ((rationalAdeleFactorialLevel n) ^ 2) → 𝓢(ℝ, ℂ)) :
      (rationalAdeleLFAssembly n b).toUnion.val =
        rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g := by
    rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val, hbox]
  rw [← rationalAdeleLFAssembly_read n f hn, rationalAdeleLFDilationDeriv_assembly]
  simp_rw [h_assembly, fourier_boxSum_zero, integral_stageEuler, smul_neg, Finset.sum_neg_distrib]

/-- The real dilation generator preserves the intersection of the two polar kernels. -/
public theorem rationalAdeleLFDilationDeriv_preserves_zero_modes (f : E)
    (_h₀ : f.toUnion.val 0 = 0) (hF : rationalAdeleFourier f.toUnion.val 0 = 0) :
    (D f).toUnion.val 0 = 0 ∧ rationalAdeleFourier (D f).toUnion.val 0 = 0 := by
  exact ⟨rationalAdeleLFDilationDeriv_at_zero f, by
    rw [rationalAdeleFourier_LFDilationDeriv_at_zero, hF, neg_zero]⟩

end Masullo
