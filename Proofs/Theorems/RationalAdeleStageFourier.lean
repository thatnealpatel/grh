module

public import Props.RationalAdeleSchwartzLF
public import Theorems.RationalAdeleBoxThetaInversion
import Lemmas.RationalAdeleStageFourier

/-! # Fourier is continuous on each rational adelic Schwartz stage

This is the forward level map of Lemma D.1.6.19(2), pp. 773–775, for the
rational pair `M ℤ̂ ⊆ M⁻¹ ℤ̂`. The output is in the very same stage.
The finite Fourier matrix uses counting weights `1/M`, the Haar mass
of a cell. The infinite factor is the real Schwartz Fourier transform.
-/

open NumberField
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "Profiles" M => Fin (M ^ 2) → 𝓢(ℝ, ℂ)
local notation "rep" => rationalAdeleStageRepresentative

/-- Fourier in the product Schwartz coordinates of level `M`. -/
public noncomputable def rationalAdeleStageFourier (M : ℕ) : (Profiles M) →L[ℂ] (Profiles M) :=
  ContinuousLinearMap.pi fun k ↦ ∑ j : Fin (M ^ 2),
    ((M : ℂ)⁻¹ * conj (rationalFiniteAdeleAddChar (rep M j * rep M k))) •
      ((FourierTransform.fourierCLM ℂ 𝓢(ℝ, ℂ)).comp (ContinuousLinearMap.proj j))

/-- The coordinates are a finite matrix of weighted real transforms. -/
public theorem rationalAdeleStageFourier_apply (M : ℕ) (b : Profiles M) (k : Fin (M ^ 2)) :
    rationalAdeleStageFourier M b k = ∑ j : Fin (M ^ 2),
      ((M : ℂ)⁻¹ * conj (rationalFiniteAdeleAddChar (rep M j * rep M k))) • 𝓕 (b j) := by
  simp only [rationalAdeleStageFourier, ContinuousLinearMap.pi_apply,
    sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, FourierTransform.fourierCLM_apply]

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- The stage operator realizes the normalized adelic Fourier integral at every
frequency, including those outside the stage's frequency support. -/
public theorem rationalAdeleStageCoordinates_symm_fourier {M : ℕ} (hM : 0 < M)
    (b : Profiles M) (y : A) :
    ((rationalAdeleStageCoordinates hM).symm (rationalAdeleStageFourier M b)).val y =
      rationalAdeleFourier ((rationalAdeleStageCoordinates hM).symm b).val y := by
  rw [rationalAdeleStageCoordinates_symm_eq_boxSum hM b, rationalAdeleFourier,
    integral_rationalAdeleBoxSum_mul_conj_char]
  simp only [one_mul, rationalAdeleUnramified_stageScale, ideleNorm_rationalAdeleStageScale]
  by_cases hy : y ∈ rationalAdeleStageSupport M
  · obtain ⟨k, hk, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hM y).mp hy
    rw [← rationalAdeleStageCoordinates_eq_on_cell hM _ hk, LinearEquiv.apply_symm_apply,
      rationalAdeleStageFourier_apply]
    simp only [Set.indicator_of_mem hy, rationalAdeleAddChar_stageCenter_mul hM _ k hk,
      sum_apply, smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
  · rw [((rationalAdeleStageCoordinates hM).symm _).property.1 y hy]
    simp only [Set.indicator_of_notMem hy, mul_zero, smul_zero, Finset.sum_const_zero]

/-- Fourier commutes with assembly from each factorial stage of the rational LF
space, as an identity of adelic functions. -/
public theorem rationalAdeleLFAssembly_fourier (n : ℕ) (b : Profiles (rationalAdeleFactorialLevel n)) :
    (rationalAdeleLFAssembly n (rationalAdeleStageFourier (rationalAdeleFactorialLevel n) b)).toUnion.val =
      rationalAdeleFourier (rationalAdeleLFAssembly n b).toUnion.val := by
  funext y
  simp only [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val]
  exact rationalAdeleStageCoordinates_symm_fourier (rationalAdeleFactorialLevel_pos n) b y

end Masullo
