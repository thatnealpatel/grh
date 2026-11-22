module

public import Theorems.ArchimedeanIdealPoisson

/-! # Shifted ideal Poisson summation in trace normalization

Masullo specifies `dx` at real places and `2 dx dy` at complex places
(Definition A.3.1.2(1)–(2), PDF p. 556) and the trace character at infinity
(Example A.3.1.5, p. 557). The conjugated character is used in the Fourier
integral (2.2.4.32), p. 92. These readings are provisional (pinned Markdown
and numbered PDF layout).

For the lattice proof of the theta identity (Theorem 2.2.3.2, p. 82), we
need to use the trace measure in the Fourier factor without changing the
ordinary-volume lattice identity. We prove that the complex-place scalar
multiplies both the Fourier integral and the covolume, so it cancels in
shifted Poisson summation. This is only the Archimedean comparison, not
factorization of a global Fourier integral.
-/

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped Classical ENNReal FourierTransform InnerProductSpace SchwartzMap nonZeroDivisors

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "Eucl" => mixedEmbedding.euclidean.mixedSpace K
local notation "Frac" => FractionalIdeal (𝓞 K)⁰ K

/-- Fourier integral at infinity with the negative trace kernel and the
additive trace measure. The argument `y` is in mixed coordinates, not
Euclidean dual-frequency coordinates. -/
@[expose] public def archimedeanTraceFourier (φ : Eucl → ℂ) (y : Eucl) : ℂ :=
  ∫ x, Complex.exp ((↑(-2 * Real.pi * ⟪x, archimedeanTraceFrequency K y⟫_ℝ) : ℂ) *
    Complex.I) * φ x ∂archimedeanTraceMeasure K

/-- Passing from Euclidean volume to trace measure multiplies the integral
by two per complex place, and the frequency is the Euclidean trace frequency.
For arbitrary functions this is an equality of Mathlib's totalized integrals. -/
public theorem archimedeanTraceFourier_eq (φ : Eucl → ℂ) (y : Eucl) :
    archimedeanTraceFourier K φ y =
      (2 : ℂ) ^ nrComplexPlaces K * 𝓕 φ (archimedeanTraceFrequency K y) := by
  rw [archimedeanTraceFourier, archimedeanTraceMeasure, integral_smul_measure, Real.fourier_eq']
  simp only [smul_eq_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, Complex.real_smul,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- The same change of measure multiplies the covolume by two per complex place. -/
public theorem covolume_archimedeanIdealLattice_traceMeasure_eq_smul (I : Fracˣ) :
    ZLattice.covolume (archimedeanIdealLattice K I) (archimedeanTraceMeasure K) =
      (2 : ℝ) ^ nrComplexPlaces K * ZLattice.covolume (archimedeanIdealLattice K I) volume := by
  rw [covolume_archimedeanIdealLattice_traceMeasure, covolume_archimedeanIdealLattice]
  rw [← mul_assoc, mul_left_comm, ← mul_pow]
  norm_num

/-- Shifted Poisson summation using the trace measure in both the transform
and the covolume. Both absolutely convergent series include zero. -/
public theorem archimedeanIdeal_tracePoisson (I : Fracˣ) (φ : 𝓢(Eucl, ℂ)) (b : Eucl) :
    let p (u : archimedeanIdealLattice K I) := φ (b + u)
    let q (y : ↥(FractionalIdeal.dual ℤ ℚ I.val)) :=
      let v := archimedeanTraceFrequency K (archimedeanEuclideanEmbedding K y)
      Complex.exp ((↑(2 * Real.pi * ⟪b, v⟫_ℝ) : ℂ) * Complex.I) *
        archimedeanTraceFourier K φ (archimedeanEuclideanEmbedding K y)
    Summable (fun u ↦ ‖p u‖) ∧ Summable (fun y ↦ ‖q y‖) ∧
      ∑' u, p u = ((↑(ZLattice.covolume (archimedeanIdealLattice K I)
        (archimedeanTraceMeasure K)) : ℂ)⁻¹) * ∑' y, q y := by
  obtain ⟨hp, hq, hP⟩ := archimedeanIdeal_poisson K I φ b
  dsimp only at hp hq hP ⊢
  -- Replace each integral by its volume counterpart and pull out the constant.
  have hscalar (a z : ℂ) : a * ((2 : ℂ) ^ nrComplexPlaces K * z) =
      (2 : ℂ) ^ nrComplexPlaces K * (a * z) := mul_left_comm _ _ _
  simp_rw [archimedeanTraceFourier_eq, hscalar]
  refine ⟨hp, ?_, ?_⟩
  · simpa only [norm_mul] using hq.mul_left ‖(2 : ℂ) ^ nrComplexPlaces K‖
  · rw [hP, tsum_mul_left, covolume_archimedeanIdealLattice_traceMeasure_eq_smul,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, mul_inv_rev, mul_assoc,
      ← mul_assoc (((2 : ℂ) ^ nrComplexPlaces K)⁻¹),
      inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_mul]

end

end Masullo
