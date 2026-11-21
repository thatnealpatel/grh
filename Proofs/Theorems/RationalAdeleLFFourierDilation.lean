module

public import Lemmas.RationalAdeleFourierEuler

/-! # Pointwise Fourier covariance of the rational dilation generator

The positive real section case of (2.2.4.29), p. 92, in log scale.
The reciprocal norm factor remains in the derivative, even at frequency zero.
-/

open NumberField
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "D" => rationalAdeleLFDilationDeriv

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- Fourier transforms the real dilation generator by differentiating inverse
frequency dilation with the inverse norm weight. The assertion is pointwise
at every adelic frequency, not a limit in the LF topology. -/
public theorem hasDerivAt_rationalAdeleFourier_LFDilation (f : E) (y : A) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-s) • rationalAdeleFourier f.toUnion.val
      ((rationalIdeleLogSection (Multiplicative.ofAdd (-s)) : A) * y))
      (rationalAdeleFourier (D f).toUnion.val y) 0 := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  obtain ⟨a, g, ha, hg, hbox⟩ :=
    exists_rationalAdeleStageCoordinates_symm_eq_boxSum_real (rationalAdeleFactorialLevel_pos n)
  have h_assembly (b : Fin ((rationalAdeleFactorialLevel n) ^ 2) → 𝓢(ℝ, ℂ)) :
      (rationalAdeleLFAssembly n b).toUnion.val =
        rationalAdeleBoxSum Finset.univ (fun _ ↦ 1) b a g := by
    rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val, hbox]
  rw [← rationalAdeleLFAssembly_read n f hn, rationalAdeleLFDilationDeriv_assembly]
  simp only [h_assembly]
  let b := rationalAdeleLFRead n f
  have he : rationalAdeleStageEuler n b = fun i ↦
      SchwartzMap.smulLeftCLM ℂ Complex.ofReal (LineDeriv.lineDerivOp (1 : ℝ) (b i)) := by
    funext i
    ext x
    rw [rationalAdeleStageEuler_apply,
      SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal,
      smul_eq_mul, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rfl
  rw [he]
  exact hasDerivAt_rationalAdeleBoxSum_fourier_euler Finset.univ b a g ha hg y

end Masullo
