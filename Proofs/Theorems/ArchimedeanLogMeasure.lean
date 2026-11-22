module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

import Mathlib.MeasureTheory.Group.Measure

/-!
# Separating the Archimedean norm coordinate

Masullo's (A.2.3.3)–(5), PDF p. 548, give the weighted logarithms and their
sum-zero hyperplane. For the comparison of the local normalization with
(A.3.2.1), pp. 559–560, we supply the measure calculation for retaining the
sum and dropping one log. The measure on the retained coordinates is product
Lebesgue measure, not Euclidean surface measure on the hyperplane.
-/

open MeasureTheory NumberField
open NumberField.Units.dirichletUnitTheorem (w₀ logSpace)

open scoped Classical

namespace Masullo

/-- In the already weighted log coordinates, replacing the omitted log by their sum
separates Lebesgue measure in the log-norm direction with no scalar factor. -/
public theorem measurePreserving_archimedeanLogSplit (K : Type*) [Field K] [NumberField K] :
    MeasurePreserving
      (fun x : InfinitePlace K → ℝ ↦
        ((∑ v, x v), fun v : {v : InfinitePlace K // v ≠ w₀} ↦ x v.1))
      volume ((volume : Measure ℝ).prod (volume : Measure (logSpace K))) := by
  classical
  let i : InfinitePlace K := w₀
  let J := {v : InfinitePlace K // v ≠ i}
  let : Fintype {v : InfinitePlace K // v = i} := Subtype.fintype _
  let : Unique {v : InfinitePlace K // v = i} :=
    ⟨⟨⟨i, rfl⟩⟩, fun v ↦ Subtype.ext v.property⟩
  let μ : Measure ℝ := volume
  let ν : Measure (J → ℝ) := volume
  -- First separate the singleton coordinate without changing the product measure.
  have split := volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
    (· = i)
  rw [Measure.volume_eq_prod] at split
  have singleton : MeasurePreserving (MeasurableEquiv.piUnique (fun _ : {v // v = i} ↦ ℝ))
      volume μ :=
    measurePreserving_piUnique (fun _ ↦ volume)
  have separated : MeasurePreserving (fun x : InfinitePlace K → ℝ ↦
      (x i, fun j : J ↦ x j.1)) volume (μ.prod ν) := by
    have h := (singleton.prod (MeasurePreserving.id ν)).comp split
    exact h
  -- For each retained tuple, add its sum to the omitted coordinate by translation.
  have shear : MeasurePreserving (fun p : (J → ℝ) × ℝ ↦ (p.1, p.2 + ∑ j, p.1 j))
      (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product
      (measurable_snd.add (Finset.measurable_sum _ fun j _ ↦
        (measurable_pi_apply j).comp measurable_fst))
      (Filter.Eventually.of_forall fun x ↦ (measurePreserving_add_right μ (∑ j, x j)).map_eq)
  simpa only [Function.comp_def, Prod.swap_prod_mk, Fintype.sum_eq_add_sum_subtype_ne _ i]
    using (Measure.measurePreserving_swap (μ := ν) (ν := μ)).comp
      (shear.comp ((Measure.measurePreserving_swap (μ := μ) (ν := ν)).comp separated))

end Masullo
