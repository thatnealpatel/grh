module

public import Lemmas.ArchimedeanAngularChart

/-! # Total mass of the Archimedean angular coordinates

The numerator of (A.3.2.1), PDF pp. 559–560, contains the factor
`2 ^ r₁ * (2π) ^ r₂`. Definition A.3.2.2(1) and the local product
(A.3.2.5), p. 560, specify the normalizations. Here we compute this
factor for the checked angular coordinates: Count the two real signs,
measure the complex angle interval, and multiply over the signature.
This is a computation of `ω univ` in `Theorems.IdeleLogHaar`, not a
comparison of quotient measures. Source reading: Provisional, from
Markdown and numbered PDF text, not rendered pages.
-/

open MeasureTheory NumberField NumberField.InfinitePlace Set
open scoped BigOperators Classical ENNReal

namespace Masullo

variable {K : Type*} [Field K]

private def angularChartMass {X : Type*} (c : AngularChart X) : ℝ≥0∞ :=
  c.measure univ

private theorem measure_archimedeanAngular_univ_real (w : InfinitePlace K) (hw : w.IsReal) :
    archimedeanAngularMeasure w univ = 2 := by
  change angularChartMass (archimedeanAngularChart w) = 2
  rw [archimedeanAngularChart, dite_eq_left hw]
  change (Measure.count : Measure Bool) univ = 2
  rw [Measure.count_univ, ENat.card_eq_coe_fintype_card]
  norm_num

private theorem measure_archimedeanAngular_univ_complex (w : InfinitePlace K) (hw : w.IsComplex) :
    archimedeanAngularMeasure w univ = ENNReal.ofReal (2 * Real.pi) := by
  change angularChartMass (archimedeanAngularChart w) = _
  rw [archimedeanAngularChart, dite_eq_right (not_isReal_iff_isComplex.mpr hw)]
  change (volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi) univ = _
  rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_neg_eq_add, ← two_mul]

/-- The angular product measure has total mass `2 ^ r₁ * (2π) ^ r₂`.
The completion-unit Borel hypotheses match the Haar coordinates; the angular
target spaces and their measures are fixed by the charts themselves. -/
public theorem measure_archimedeanAngular_univ [NumberField K]
    [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
    [∀ w : InfinitePlace K, BorelSpace w.Completionˣ] :
    (Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w) univ =
      (2 : ℝ≥0∞) ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K := by
  rw [Measure.pi_univ, InfinitePlace.prod_eq_prod_mul_prod]
  have hreal (w : {w : InfinitePlace K // w.IsReal}) :
      archimedeanAngularMeasure w.val univ = 2 :=
    measure_archimedeanAngular_univ_real w.val w.property
  have hcomplex (w : {w : InfinitePlace K // w.IsComplex}) :
      archimedeanAngularMeasure w.val univ = ENNReal.ofReal (2 * Real.pi) :=
    measure_archimedeanAngular_univ_complex w.val w.property
  simp only [hreal, hcomplex, Finset.prod_const, nrRealPlaces, nrComplexPlaces, Fintype.card]

end Masullo
