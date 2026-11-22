module

public import Lemmas.IdeleGaussianThetaSum
public import Lemmas.GaussianDifferentIdele
import Lemmas.IdeleGaussianThetaPoisson

/-! # Pointwise inversion of the trivial-character idele Gaussian

The nonzero principal sum uses the additive Gaussian with its origin removed.
The different translates the reflected idele. The factor `2⁻ʳ²` in its Euclidean
Fourier transform cancels the same factor in the covolume; the value of the
local test at the origin does not cancel from the two nonzero sums.
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped Classical

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "I" => IdeleGroup (𝓞 K) K
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "q" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
local notation "Φ" => ideleHeckeGaussian (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one)

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- Pointwise inversion at *every* idele for the actual principal periodization, with both
zero modes retained. There is no Poisson, convergence, or small-norm hypothesis. -/
public theorem ideleHeckeGaussian_one_theta_inversion (T : Finset (HeightOneSpectrum (𝓞 K))) (g : I) :
    (∑' a : Kˣ, Φ T (d a * g)) =
      (((Real.sqrt |(discr K : ℝ)| * ideleNorm g)⁻¹ : ℝ) : ℂ) *
        ((∑' a : Kˣ, Φ T (d a * (gaussianDifferentIdele K * g⁻¹))) + ideleThetaTest K 0) -
          ideleThetaTest K 0 := by
  apply eq_sub_iff_add_eq.mpr
  rw [ideleHeckeGaussian_one_periodization_add_zero_eq_tsum, ideleHeckeGaussian_one_periodization_add_zero_eq_tsum]
  exact ideleThetaTest_poisson g

/-- The contract used for the counting-normalized periodization in `IdeleClassGaussianRadial`
is enough to substitute it on both sides. -/
public theorem ideleHeckeGaussian_one_radial_theta_inversion (T : Finset (HeightOneSpectrum (𝓞 K)))
    (F : IdeleClassGroup (𝓞 K) K → ℂ) (hperiod : ∀ g : I, F (q g) = ∑' a : Kˣ, Φ T (d a * g)) (g : I) :
    F (q g) = (((Real.sqrt |(discr K : ℝ)| * ideleNorm g)⁻¹ : ℝ) : ℂ) *
      (F (q (gaussianDifferentIdele K * g⁻¹)) + ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ nrComplexPlaces K) -
        ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ nrComplexPlaces K := by
  simpa only [hperiod, ideleThetaTest_zero] using ideleHeckeGaussian_one_theta_inversion T g

-- Keep the same Borel instances as the general periodization when specializing the field.
set_option linter.concreteInstances false in
/-- Over `ℚ` the different translation disappears and both additive zero values are one. -/
public theorem ideleHeckeGaussian_one_theta_inversion_rat
    [∀ v : InfinitePlace ℚ, MeasurableSpace v.Completionˣ]
    [∀ v : InfinitePlace ℚ, BorelSpace v.Completionˣ]
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : IdeleGroup (𝓞 ℚ) ℚ) :
    let P := fun b : IdeleGroup (𝓞 ℚ) ℚ ↦ ∑' a : ℚˣ,
      ideleHeckeGaussian (1 : HeckeCharacter (𝓞 ℚ) ℚ) (fun _ ↦ norm_one) T
        (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a * b)
    P g = ((ideleNorm g)⁻¹ : ℝ) * (P g⁻¹ + 1) - 1 := by
  have hc : nrComplexPlaces ℚ = 0 := nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  simpa [ideleThetaTest_zero, hc, NumberField.discr_rat] using ideleHeckeGaussian_one_theta_inversion T g

end Masullo
