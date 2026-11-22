module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.RingTheory.Trace.Basic

/-! # The archimedean trace character in Euclidean coordinates

Masullo, PDF p. 557, Example A.3.1.5, uses the complex trace character with
phase `2 Re(z)` (provisional text reading). Its Fourier frequency in unscaled
Euclidean coordinates thus requires conjugation and a factor of two.
-/

open NumberField NumberField.InfinitePlace
open scoped Classical InnerProductSpace

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "Eucl" => NumberField.mixedEmbedding.euclidean.mixedSpace K
local notation "M" => NumberField.mixedEmbedding.euclidean.toMixed K

/-- The mixed embedding, in the unscaled real Euclidean metric. -/
@[expose] public def archimedeanEuclideanEmbedding (x : K) : Eucl :=
  (M).symm (NumberField.mixedEmbedding K x)

/-- A trace frequency is unchanged at a real place and is twice its conjugate at a complex place. -/
@[expose] public def archimedeanTraceFrequency (y : Eucl) : Eucl :=
  (M).symm ((M y).1, fun w ↦ 2 * star ((M y).2 w))

/-- The Euclidean phase at a trace frequency is the sum of local trace phases. -/
public theorem inner_archimedeanTraceFrequency (x y : Eucl) :
    ⟪x, archimedeanTraceFrequency K y⟫_ℝ =
      (∑ w, (M x).1 w * (M y).1 w) + ∑ w, 2 * ((M x).2 w * (M y).2 w).re := by
  simp only [WithLp.prod_inner_apply, PiLp.inner_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    change (M y).1 w * (M x).1 w = (M x).1 w * (M y).1 w
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro w _
    change ((2 * star ((M y).2 w)) * star ((M x).2 w)).re =
      2 * ((M x).2 w * (M y).2 w).re
    simp [Complex.mul_re, Complex.mul_im]
    ring

/-- On field elements, the local real and complex phases sum to the rational field trace. -/
public theorem inner_archimedeanEuclideanEmbedding_traceFrequency (x y : K) :
    ⟪archimedeanEuclideanEmbedding K x,
      archimedeanTraceFrequency K (archimedeanEuclideanEmbedding K y)⟫_ℝ =
        (Algebra.trace ℚ K (x * y) : ℝ) := by
  classical
  rw [inner_archimedeanTraceFrequency]
  simp only [archimedeanEuclideanEmbedding, ContinuousLinearEquiv.apply_symm_apply,
    mixedEmbedding.mixedEmbedding_apply_isReal, mixedEmbedding.mixedEmbedding_apply_isComplex,
    ← map_mul]
  have ht := congrArg Complex.re (trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := x * y))
  rw [← Fintype.sum_equiv ((mixedEmbedding.indexEquiv K).trans (RingHom.equivRatAlgHom K ℂ))
    (fun i ↦ (mixedEmbedding.indexEquiv K i) (x * y)) _ (fun _ ↦ rfl)] at ht
  simp only [eq_ratCast, Complex.ratCast_re, mixedEmbedding.index, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Complex.add_re, Complex.re_sum, Fin.sum_univ_two,
    mixedEmbedding.indexEquiv_apply_isReal, mixedEmbedding.indexEquiv_apply_isComplex_fst,
    mixedEmbedding.indexEquiv_apply_isComplex_snd] at ht
  rw [ht]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  simp [two_mul]

end

end Masullo
