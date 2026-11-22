module

public import Lemmas.IdeleGaussianThetaSum
public import Lemmas.GaussianDifferentIdele
import Lemmas.IdeleGaussianEuclideanLattice
import Lemmas.EuclideanLatticePoisson
import Lemmas.IdeleThetaFourier

/-! # Poisson summation for the Gaussian supported on an inverse finite ideal -/

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical FourierTransform nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "I" => IdeleGroup (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "E" => euclidean.mixedSpace K

private noncomputable def reflectedDualEquiv (g : I) :
    ↥(ideleGaussianIdeal (gaussianDifferentIdele K * g⁻¹) : J) ≃
      ZLattice.euclideanDual (ideleGaussianEuclideanLattice g) :=
  (Equiv.subtypeEquivRight (fun x : K ↦ by rw [ideleGaussianIdeal_reflect])).trans
    (ideleGaussianEuclideanDualEquiv g)

private theorem reflectedDualEquiv_apply (g : I)
    (y : (ideleGaussianIdeal (gaussianDifferentIdele K * g⁻¹) : J)) :
    (reflectedDualEquiv g y : E) = archimedeanTraceFrequency K ((euclidean.toMixed K).symm
      (ideleMixedScale (gaussianDifferentIdele K * g⁻¹) (mixedEmbedding K (y : K)))) := by
  simp only [reflectedDualEquiv, Equiv.trans_apply, Equiv.subtypeEquivRight_apply,
    ideleGaussianEuclideanDualEquiv_apply, ideleMixedScale_apply, ideleMixedPart_reflect]

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- Poisson summation on the scaled ideal, expressed entirely in field elements. -/
public theorem ideleThetaTest_poisson (g : I) :
    (∑' x : (ideleGaussianIdeal g : J), ideleThetaTest K (ideleMixedScale g (mixedEmbedding K (x : K)))) =
      (((Real.sqrt |(discr K : ℝ)| * ideleNorm g)⁻¹ : ℝ) : ℂ) *
        ∑' y : (ideleGaussianIdeal (gaussianDifferentIdele K * g⁻¹) : J), ideleThetaTest K
          (ideleMixedScale (gaussianDifferentIdele K * g⁻¹) (mixedEmbedding K (y : K))) := by
  let r := gaussianDifferentIdele K * g⁻¹
  let f (x : E) := ideleThetaTest K (euclidean.toMixed K x)
  let L := ideleGaussianEuclideanLattice g
  let a := ideleGaussianEuclideanLatticeEquiv g
  let b := reflectedDualEquiv g
  let t (y : (ideleGaussianIdeal r : J)) := ideleThetaTest K (ideleMixedScale r (mixedEmbedding K (y : K)))
  let m := (2⁻¹ : ℂ) ^ nrComplexPlaces K
  have sample (y : (ideleGaussianIdeal r : J)) : 𝓕 f (b y : E) = m * t y := by
    dsimp only [b]
    rw [reflectedDualEquiv_apply]
    exact fourier_const_mul_mixedGaussian_traceFrequency K _ _
  have hsum : Summable (fun y : ZLattice.euclideanDual L ↦ 𝓕 f (y : E)) := by
    apply b.summable_iff.mp
    simpa only [Function.comp_def, sample] using (summable_ideleThetaTest r).mul_left m
  obtain ⟨hc, hi, hd⟩ := const_mul_mixedGaussian_poissonData K (((1 / (2 * Real.pi) : ℝ) : ℂ) ^ nrComplexPlaces K)
  have ps := ZLattice.tsum_eq_covolume_inv_smul_tsum_fourier L f hc hi hd hsum
  rw [← a.tsum_eq (fun x : L ↦ f (x : E)), ← b.tsum_eq (fun y : ZLattice.euclideanDual L ↦ 𝓕 f (y : E))] at ps
  simp only [sample, tsum_mul_left, Complex.real_smul] at ps
  rw [← mul_assoc] at ps
  have hcoe : ∀ x : (ideleGaussianIdeal g : J), f (a x : E) =
      ideleThetaTest K (ideleMixedScale g (mixedEmbedding K (x : K))) := by
    intro x
    simp only [f, a, ideleGaussianEuclideanLatticeEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [hcoe] at ps
  rw [ps]
  congr 1
  rw [show ZLattice.covolume L volume = _ from ideleGaussianEuclideanLattice_covolume g]
  simp only [m, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [mul_assoc, mul_inv, mul_right_comm,
    inv_mul_cancel₀ (pow_ne_zero _ (inv_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0))), one_mul]

end Masullo
