module

public import Lemmas.FinitePlaceSupport
import Mathlib.RingTheory.Complex

/-! # Archimedean dilation of the mixed lattice by an idele -/

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.InfinitePlace.Completion
open scoped Classical

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "I" => IdeleGroup (𝓞 K) K

/-- The actual Archimedean coordinates, retaining complex arguments. -/
@[expose] public noncomputable def ideleMixedPart : I →* mixedSpace K where
  toFun g := (fun w ↦ extensionEmbeddingOfIsReal w.property (g.val.1 w.val),
    fun w ↦ extensionEmbedding w.val (g.val.1 w.val))
  map_one' := by ext <;> exact map_one _
  map_mul' g h := by ext <;> exact map_mul _ _ _

/-- Dilation by the infinite component of the idele, in ordinary mixed coordinates. -/
@[expose] public noncomputable def ideleMixedScale (g : I) : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  Algebra.lmul ℝ _ (ideleMixedPart g)

public theorem ideleMixedScale_apply (g : I) (x : mixedSpace K) :
    ideleMixedScale g x = ideleMixedPart g * x := rfl

public theorem abs_det_ideleMixedScale (g : I) :
    |(ideleMixedScale g).det| = ∏ v, ‖g.val.1 v‖ ^ v.mult := by
  let a := ideleMixedPart g
  let R (w : {v : InfinitePlace K // v.IsReal}) := LinearMap.mulLeft ℝ (a.1 w)
  let C (w : {v : InfinitePlace K // v.IsComplex}) := Algebra.lmul ℝ ℂ (a.2 w)
  have h : ideleMixedScale g = LinearMap.prodMap
      (LinearMap.pi (fun w ↦ (R w).comp (LinearMap.proj w)))
      (LinearMap.pi (fun w ↦ (C w).comp (LinearMap.proj w))) := rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi, abs_mul,
    Finset.abs_prod, Finset.abs_prod, prod_eq_prod_mul_prod]
  apply congrArg₂ (· * ·) <;> apply Finset.prod_congr rfl <;> intro w _
  · rw [LinearMap.det_mulLeft, mult_isReal w, pow_one, ← Real.norm_eq_abs]
    exact (isometry_extensionEmbeddingOfIsReal w.property).norm_map_of_map_zero (map_zero _) _
  · rw [← Algebra.norm_apply, Algebra.norm_complex_eq]
    change |Complex.normSq _| = _
    rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, mult_isComplex w]
    congr 1
    exact (isometry_extensionEmbedding w.val).norm_map_of_map_zero (map_zero _) _

end Masullo
