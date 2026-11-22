module

public import Lemmas.AdeleFiniteStageMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex

/-! # Additive modulus of the infinite adele ring

Masullo states the global image formula in Lemma A.3.1.4 (PDF p. 556) and
refers to an external proof. Here the Archimedean factor is proved directly:
in the certified mixed coordinates, multiplication has real determinant
with absolute value `‖uᵥ‖` at real places and `‖uᵥ‖²` at complex places.
Source reading: Provisional, from the pinned Markdown and numbered PDF layout.
-/

open MeasureTheory NumberField InfinitePlace InfinitePlace.Completion Set
open scoped Classical Masullo.AdeleStage

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "A∞" => InfiniteAdeleRing K
local notation "E" => mixedEmbedding.euclidean.mixedSpace K
local notation "ι∞" => (archimedeanEuclideanToAdele K)
local notation "μ∞" => Measure.map ι∞ (archimedeanTraceMeasure K)

private theorem abs_det_archimedeanMixedMul (a : A∞) :
    |(Algebra.lmul ℝ _ (InfiniteAdeleRing.ringEquiv_mixedSpace K a)).det| =
      ∏ v : InfinitePlace K, ‖a v‖ ^ v.mult := by
  let z := InfiniteAdeleRing.ringEquiv_mixedSpace K a
  let r (v : {v : InfinitePlace K // v.IsReal}) := LinearMap.mulLeft ℝ (z.1 v)
  let s (v : {v : InfinitePlace K // v.IsComplex}) := Algebra.lmul ℝ ℂ (z.2 v)
  have h : Algebra.lmul ℝ _ z = LinearMap.prodMap
      (LinearMap.pi (fun v ↦ (r v).comp (LinearMap.proj v)))
      (LinearMap.pi (fun v ↦ (s v).comp (LinearMap.proj v))) := rfl
  change |(Algebra.lmul ℝ _ z).det| = _
  rw [h, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi, abs_mul,
    Finset.abs_prod, Finset.abs_prod, prod_eq_prod_mul_prod]
  apply congrArg₂ (· * ·) <;> apply Finset.prod_congr rfl <;> intro v _
  · rw [LinearMap.det_mulLeft, mult_isReal v, pow_one, ← Real.norm_eq_abs]
    exact (isometry_extensionEmbeddingOfIsReal v.property).norm_map_of_map_zero (map_zero _) _
  · rw [← Algebra.norm_apply, Algebra.norm_complex_apply, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq, mult_isComplex v]
    congr 1
    exact (isometry_extensionEmbedding v.val).norm_map_of_map_zero (map_zero _) _

/-- Multiplication by an infinite adele unit scales images of Borel sets in the
transported trace measure by the product of the normalized local norms. -/
public theorem archimedeanAdeleTraceMeasure_image_mul (u : (InfiniteAdeleRing K)ˣ)
    (B : Set (InfiniteAdeleRing K)) (hB : MeasurableSet B) :
    μ∞ ((fun x : InfiniteAdeleRing K ↦ (u : InfiniteAdeleRing K) * x) '' B) =
      ENNReal.ofReal (∏ v : InfinitePlace K, ‖(u : InfiniteAdeleRing K) v‖ ^ v.mult) * μ∞ B := by
  let c := mixedEmbedding.euclidean.toMixed K
  let m := Algebra.lmul ℝ _ (InfiniteAdeleRing.ringEquiv_mixedSpace K (u : A∞))
  let f : E →ₗ[ℝ] E := c.symm.toLinearMap ∘ₗ m ∘ₗ c.toLinearMap
  have hdet : |f.det| = ∏ v : InfinitePlace K, ‖(u : A∞) v‖ ^ v.mult :=
    (congrArg abs (LinearMap.det_conj m c.symm.toLinearEquiv)).trans
      (abs_det_archimedeanMixedMul K (u : A∞))
  have hconj (x : E) : (u : A∞) * ι∞ x = ι∞ (f x) := by
    apply ι∞.symm.injective
    apply c.injective
    rw [ι∞.symm_apply_apply, archimedeanEuclideanToAdele_symm_mixed, map_mul,
      ← archimedeanEuclideanToAdele_symm_mixed K (ι∞ x), ι∞.symm_apply_apply]
    exact (c.apply_symm_apply _).symm
  have himage : ι∞ ⁻¹' ((fun x : A∞ ↦ (u : A∞) * x) '' B) = f '' (ι∞ ⁻¹' B) := by
    calc
      _ = ι∞ ⁻¹' ((fun x : A∞ ↦ (u : A∞) * x) '' (ι∞ '' (ι∞ ⁻¹' B))) := by
        rw [image_preimage_eq B ι∞.surjective]
      _ = _ := by
        rw [image_image, funext hconj, ← image_image, preimage_image_eq _ ι∞.injective]
  have hι : MeasurableEmbedding (ι∞ : E → A∞) := ι∞.toHomeomorph.measurableEmbedding
  let : (archimedeanTraceMeasure K).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume (by simp) (by finiteness)
  rw [hι.map_apply, Measure.map_apply hι.measurable hB, himage,
    Measure.addHaar_image_linearMap, hdet]

end

end Masullo
