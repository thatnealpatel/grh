module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.Analysis.Complex.Exponential

/-! # Positive real scalars in the Archimedean completions -/

open NumberField

namespace Masullo

variable {K : Type*} [Field K] (v : InfinitePlace K)

open InfinitePlace.Completion in
private noncomputable def completionOfReal : ℝ →+* v.Completion := by
  classical
  exact if h : v.IsReal then (ringEquivRealOfIsReal h).symm.toRingHom
    else (ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm.toRingHom.comp
      Complex.ofRealHom

open InfinitePlace.Completion in
private theorem continuous_completionOfReal : Continuous (completionOfReal v) := by
  classical
  by_cases h : v.IsReal
  · rw [completionOfReal, dite_eq_left h]
    exact (isometryEquivRealOfIsReal h).symm.isometry.continuous
  · rw [completionOfReal, dite_eq_right h]
    exact (isometryEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm.isometry.continuous.comp
        Complex.continuous_ofReal

open InfinitePlace.Completion in
private theorem extensionEmbedding_completionOfReal (r : ℝ) :
    extensionEmbedding v (completionOfReal v r) = (r : ℂ) := by
  classical
  by_cases h : v.IsReal
  · rw [← extensionEmbeddingOfIsReal_apply h]
    change (↑(ringEquivRealOfIsReal h (completionOfReal v r)) : ℂ) = _
    simp [completionOfReal, h]
  · let e := ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)
    change e (completionOfReal v r) = _
    simp [completionOfReal, h, e]

/-- Exponentiate the log radius divided by the Archimedean multiplicity. -/
public noncomputable def completionLogRadius : Multiplicative ℝ →* v.Completion where
  toFun x := completionOfReal v (Real.exp (x.toAdd / (v.mult : ℝ)))
  map_one' := by simp
  map_mul' x y := by simp [add_div, Real.exp_add]

public theorem continuous_completionLogRadius : Continuous (completionLogRadius v) :=
  (continuous_completionOfReal v).comp (Real.continuous_exp.comp (continuous_toAdd.div_const _))

public theorem extensionEmbedding_completionLogRadius (x : Multiplicative ℝ) :
    InfinitePlace.Completion.extensionEmbedding v (completionLogRadius v x) =
      (Real.exp (x.toAdd / (v.mult : ℝ)) : ℂ) :=
  extensionEmbedding_completionOfReal v _

end Masullo
