module

public import Lemmas.ArchimedeanTracePairing
public import Lemmas.MixedLatticeGaussianPoisson

/-! # Euclidean Fourier transform of the mixed theta test

Volume is ordinary Euclidean volume. Hence even the unit-scale Gaussian has
Fourier multiplier `2⁻ʳ²` at the trace frequency, not one.
-/

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped FourierTransform Classical InnerProductSpace

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]
local notation "G" => mixedGaussian (fun _ ↦ 1) (fun _ ↦ 1)
local notation "e" => euclidean.toMixed K

/-- The ordinary Fourier transform evaluated at the frequency which realizes
trace pairing in the mixed embedding. -/
private theorem fourier_mixedGaussian_traceFrequency (y : mixedSpace K) :
    𝓕 (fun x : euclidean.mixedSpace K ↦ G (e x)) (archimedeanTraceFrequency K ((e).symm y)) =
      (2⁻¹ : ℂ) ^ nrComplexPlaces K * G y := by
  rw [Real.fourier_eq']
  let h (x : mixedSpace K) := gaussianPhase (mixedTracePairing x y) * G x
  have hphase (x : euclidean.mixedSpace K) :
      ⟪x, archimedeanTraceFrequency K ((e).symm y)⟫_ℝ = mixedTracePairing (e x) y := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply, mixedTracePairing] using
      inner_archimedeanTraceFrequency K x ((e).symm y)
  simp_rw [hphase, smul_eq_mul]
  change (∫ x, h (e x)) = _
  rw [(euclidean.volumePreserving_toMixed K).integral_comp (euclidean.toMixed K).toHomeomorph.measurableEmbedding]
  simpa [h, nrComplexPlaces] using (mixedGaussian_fourier (fun _ ↦ 1) (fun _ ↦ 1)
    (fun _ ↦ zero_lt_one) (fun _ ↦ zero_lt_one) y).2

/-- Evaluation on a trace frequency, allowing the constant from the complex local tests. -/
public theorem fourier_const_mul_mixedGaussian_traceFrequency (c : ℂ) (y : mixedSpace K) :
    𝓕 (fun x : euclidean.mixedSpace K ↦ c * G (e x))
      (archimedeanTraceFrequency K ((e).symm y)) =
      (2⁻¹ : ℂ) ^ nrComplexPlaces K * (c * G y) := by
  change 𝓕 (c • (fun x : euclidean.mixedSpace K ↦ G (e x))) _ = _
  have h : 𝓕 (c • (fun x : euclidean.mixedSpace K ↦ G (e x))) =
      c • 𝓕 (fun x : euclidean.mixedSpace K ↦ G (e x)) :=
    VectorFourier.fourierIntegral_const_smul _ _ _ _ _
  rw [h, Pi.smul_apply, smul_eq_mul, fourier_mixedGaussian_traceFrequency, mul_left_comm]

/-- Simultaneous analytic hypotheses for Poisson summation in the ordinary Euclidean metric. -/
public theorem const_mul_mixedGaussian_poissonData (c : ℂ) :
    let f := fun x : euclidean.mixedSpace K ↦ c * G (e x)
    Continuous f ∧ Integrable f ∧
      ∀ p : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖x‖ ^ p * ‖f x‖ ≤ A := by
  dsimp only
  refine ⟨continuous_const.mul ((continuous_mixedGaussian _ _).comp (euclidean.toMixed K).continuous), ?_, ?_⟩
  · exact ((euclidean.volumePreserving_toMixed K).integrable_comp_emb
      (euclidean.toMixed K).toHomeomorph.measurableEmbedding |>.mpr
        (integrable_mixedGaussian _ _ (fun _ ↦ zero_lt_one) (fun _ ↦ zero_lt_one))).const_mul c
  · intro p
    obtain ⟨A, hA, h⟩ := rapidDecay_comp_continuousLinearEquiv (euclidean.toMixed K) G p
      (mixedGaussian_rapidDecay _ _ (fun _ ↦ zero_lt_one) (fun _ ↦ zero_lt_one) p)
    exact ⟨‖c‖ * A, mul_nonneg (norm_nonneg _) hA, fun x ↦ by
      rw [norm_mul, mul_left_comm]; exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)⟩

end Masullo
