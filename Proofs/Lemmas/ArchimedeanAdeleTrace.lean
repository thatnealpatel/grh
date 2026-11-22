module

public import Lemmas.AdeleFiniteStageMeasure
public import Theorems.ArchimedeanTracePoisson

/-! # The trace phase on the actual infinite completions

The real and complex factors of Masullo's Example A.3.1.5 (PDF p. 557) give
`exp (2πi Tr∞(x))`. The pairing with the trace frequency in Euclidean mixed
coordinates implements the conjugated kernel of (2.2.4.32), p. 92.
Source reading: Provisional, pinned Markdown and numbered PDF layout.
-/

open MeasureTheory NumberField
open scoped Masullo.AdeleStage Classical ComplexConjugate InnerProductSpace SchwartzMap

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "E" => mixedEmbedding.euclidean.mixedSpace K
local notation "A∞" => InfiniteAdeleRing K
local notation "ι∞" => (archimedeanEuclideanToAdele K)

/-- The Euclidean embedding of a field element transports to its infinite diagonal. -/
public theorem euclideanToAdele_embedding (y : K) :
    ι∞ (archimedeanEuclideanEmbedding K y) = algebraMap K A∞ y := by
  apply ι∞.symm.injective
  apply (mixedEmbedding.euclidean.toMixed K).injective
  rw [ContinuousAddEquiv.symm_apply_apply, archimedeanEuclideanToAdele_symm_mixed,
    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  simp [archimedeanEuclideanEmbedding]

/-- The phase in the positive Archimedean character, before multiplying by `2πi`. -/
@[expose] public def archimedeanAdeleTrace (x : A∞) : ℝ :=
  ⟪ι∞.symm x, archimedeanTraceFrequency K (ι∞.symm 1)⟫_ℝ

/-- The trace of an infinite adele product is exactly the mixed-space trace pairing. -/
public theorem archimedeanAdeleTrace_mul (x y : A∞) :
    archimedeanAdeleTrace K (x * y) =
      ⟪ι∞.symm x, archimedeanTraceFrequency K (ι∞.symm y)⟫_ℝ := by
  rw [archimedeanAdeleTrace, inner_archimedeanTraceFrequency, inner_archimedeanTraceFrequency]
  simp only [archimedeanEuclideanToAdele_symm_mixed, map_one, map_mul, Prod.fst_mul,
    Prod.snd_mul, Prod.fst_one, Prod.snd_one, Pi.mul_apply, Pi.one_apply, mul_one]

/-- The positive Archimedean trace character on the actual infinite adeles. -/
@[expose] public def numberFieldInfiniteAdeleAddChar : AddChar A∞ ℂ where
  toFun x := Complex.exp (2 * Real.pi * Complex.I * (archimedeanAdeleTrace K x : ℂ))
  map_zero_eq_one' := by simp [archimedeanAdeleTrace]
  map_add_eq_mul' x y := by
    simp only [archimedeanAdeleTrace, map_add, inner_add_left, Complex.ofReal_add, mul_add,
      Complex.exp_add]

public theorem continuous_numberFieldInfiniteAdeleAddChar :
    Continuous (numberFieldInfiniteAdeleAddChar K : A∞ → ℂ) := by
  apply Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact ι∞.symm.continuous.inner continuous_const

public theorem norm_numberFieldInfiniteAdeleAddChar (x : A∞) :
    ‖numberFieldInfiniteAdeleAddChar K x‖ = 1 := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (archimedeanAdeleTrace K x : ℂ))‖ = 1
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- At the diagonal the Archimedean phase is the ordinary rational field trace. -/
public theorem numberFieldInfiniteAdeleAddChar_diagonal (x : K) :
    numberFieldInfiniteAdeleAddChar K (algebraMap K A∞ x) =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ K x : ℂ)) := by
  have h := archimedeanAdeleTrace_mul K (algebraMap K A∞ x) (algebraMap K A∞ 1)
  rw [map_one, mul_one, ← map_one (algebraMap K A∞), ← euclideanToAdele_embedding,
    ← euclideanToAdele_embedding, ι∞.symm_apply_apply, ι∞.symm_apply_apply,
    inner_archimedeanEuclideanEmbedding_traceFrequency, mul_one, euclideanToAdele_embedding] at h
  change Complex.exp (2 * Real.pi * Complex.I * (archimedeanAdeleTrace K (algebraMap K A∞ x) : ℂ)) = _
  rw [h, Complex.ofReal_ratCast]

/-- The infinite factor of the Fourier integral at a diagonal frequency. -/
@[expose] public def archimedeanAdeleFourierIntegrand (φ : 𝓢(E, ℂ)) (y : K) (z : A∞) : ℂ :=
  φ (ι∞.symm z) * conj (numberFieldInfiniteAdeleAddChar K (z * algebraMap K A∞ y))

private theorem archimedeanAdeleFourierIntegrand_coord (φ : 𝓢(E, ℂ)) (y : K) (x : E) :
    archimedeanAdeleFourierIntegrand K φ y (ι∞ x) =
      Complex.exp ((↑(-2 * Real.pi * ⟪x, archimedeanTraceFrequency K
        (archimedeanEuclideanEmbedding K y)⟫_ℝ) : ℂ) * Complex.I) * φ x := by
  simp only [archimedeanAdeleFourierIntegrand, ι∞.symm_apply_apply, numberFieldInfiniteAdeleAddChar,
    AddChar.coe_mk, archimedeanAdeleTrace_mul, ← euclideanToAdele_embedding K y, ← Complex.exp_conj]
  rw [mul_comm (φ x)]
  congr 2
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Transporting the trace measure to the infinite adeles preserves the Fourier integral. -/
public theorem archimedeanAdeleFourierIntegrand_integral (φ : 𝓢(E, ℂ)) (y : K) :
    (∫ z, archimedeanAdeleFourierIntegrand K φ y z ∂(archimedeanTraceMeasure K).map ι∞) =
      archimedeanTraceFourier K φ (archimedeanEuclideanEmbedding K y) := by
  have he : MeasurableEmbedding (ι∞ : E → A∞) := ι∞.toHomeomorph.measurableEmbedding
  rw [he.integral_map, archimedeanTraceFourier]
  exact integral_congr_ae (Filter.Eventually.of_forall (archimedeanAdeleFourierIntegrand_coord K φ y))

/-- This Archimedean integrand is integrable, without a compact-support hypothesis. -/
public theorem integrable_archimedeanAdeleFourierIntegrand (φ : 𝓢(E, ℂ)) (y : K) :
    Integrable (archimedeanAdeleFourierIntegrand K φ y) ((archimedeanTraceMeasure K).map ι∞) := by
  have he : MeasurableEmbedding (ι∞ : E → A∞) := ι∞.toHomeomorph.measurableEmbedding
  rw [he.integrable_map_iff]
  have hφ : Integrable (φ : E → ℂ) (archimedeanTraceMeasure K) := by
    rw [archimedeanTraceMeasure]
    exact φ.integrable.smul_measure (by finiteness)
  have h : Continuous (fun x : E ↦ conj (numberFieldInfiniteAdeleAddChar K
      (ι∞ x * algebraMap K A∞ y))) :=
    Complex.continuous_conj.comp ((continuous_numberFieldInfiniteAdeleAddChar K).comp
      (ι∞.continuous.mul continuous_const))
  simpa only [Function.comp_def, archimedeanAdeleFourierIntegrand, ι∞.symm_apply_apply] using
    hφ.mul_bdd h.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ by
      rw [Complex.norm_conj, norm_numberFieldInfiniteAdeleAddChar])

end

end Masullo
