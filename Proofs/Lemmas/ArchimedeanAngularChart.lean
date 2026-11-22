module

public import Theorems.IdeleHeckeGaussian
public import Theorems.RealMultiplicativeHaarLogSign
public import Theorems.ComplexMultiplicativeHaarLogPolar

/-! # Dependent angular coordinates for Archimedean completion units -/

open MeasureTheory NumberField Set
open InfinitePlace.Completion
open scoped Classical

namespace Masullo

/-- A local angular coordinate with its target measure. -/
public structure AngularChart (X : Type*) where
  Angle : Type
  space : MeasurableSpace Angle
  measure : @Measure Angle space
  coord : X → Angle
  sigmaFinite : @SigmaFinite Angle space measure

/-- At real places use the two signs, each of mass one. At complex places
use the principal argument and Lebesgue measure on `(-π, π)`; the missing
branch ray has measure zero, not a discarded pointwise orbit. -/
@[expose] public noncomputable def archimedeanAngularChart {K : Type*} [Field K]
    (v : InfinitePlace K) : AngularChart v.Completionˣ :=
  if hv : v.IsReal then
    ⟨Bool, inferInstance, Measure.count,
      fun u ↦ if 0 < extensionEmbeddingOfIsReal hv u.val then true else false, inferInstance⟩
  else
    ⟨ℝ, inferInstance, volume.restrict (Ioo (-Real.pi) Real.pi),
      fun u ↦ Complex.arg (extensionEmbedding v u.val), inferInstance⟩

public abbrev ArchimedeanAngle {K : Type*} [Field K] (v : InfinitePlace K) :=
  (archimedeanAngularChart v).Angle

public noncomputable instance {K : Type*} [Field K] (v : InfinitePlace K) :
    MeasurableSpace (ArchimedeanAngle v) := (archimedeanAngularChart v).space

public noncomputable abbrev archimedeanAngularMeasure {K : Type*} [Field K] (v : InfinitePlace K) :
    Measure (ArchimedeanAngle v) := (archimedeanAngularChart v).measure

public noncomputable abbrev archimedeanAngle {K : Type*} [Field K] (v : InfinitePlace K) :
    v.Completionˣ → ArchimedeanAngle v := (archimedeanAngularChart v).coord

public instance {K : Type*} [Field K] (v : InfinitePlace K) :
    SigmaFinite (archimedeanAngularMeasure v) := (archimedeanAngularChart v).sigmaFinite

/-- The checked real and complex identities in a common dependent chart. -/
public theorem measurePreserving_archimedeanLocalCoordinates {K : Type*} [Field K]
    (v : InfinitePlace K) [MeasurableSpace v.Completionˣ] [BorelSpace v.Completionˣ] :
    MeasurePreserving (fun u : v.Completionˣ ↦ ((v.mult : ℝ) * Real.log ‖u.val‖,
      archimedeanAngle v u)) (archimedeanCompletionHaar v)
      ((volume : Measure ℝ).prod (archimedeanAngularMeasure v)) := by
  -- State the goal as a function of the whole chart so that cases also
  -- specialize the dependent angular type and its measurable space.
  let P (c : AngularChart v.Completionˣ) : Prop :=
    letI : MeasurableSpace c.Angle := c.space
    MeasurePreserving (fun u : v.Completionˣ ↦ ((v.mult : ℝ) * Real.log ‖u.val‖, c.coord u))
      (archimedeanCompletionHaar v) ((volume : Measure ℝ).prod c.measure)
  change P (archimedeanAngularChart v)
  have hlog : Measurable (fun u : v.Completionˣ ↦ Real.log ‖u.val‖) :=
    Real.measurable_log.comp (continuous_norm.comp Units.continuous_val).measurable
  by_cases hv : v.IsReal
  · rw [archimedeanAngularChart, dite_eq_left hv]
    dsimp only [P, AngularChart.coord, AngularChart.measure]
    rw [archimedeanCompletionHaar, dite_eq_left hv, hv.mult_eq_one, Nat.cast_one]
    have h : MeasurePreserving (fun u : v.Completionˣ ↦ (Real.log ‖u.val‖,
        if 0 < extensionEmbeddingOfIsReal hv u.val then true else false))
        (realCompletionHaar hv) ((volume : Measure ℝ).prod (Measure.count : Measure Bool)) :=
      ⟨hlog.prodMk (Measurable.ite
        (measurableSet_Ioi.preimage (realCompletionEmbedding hv).measurable)
        measurable_const measurable_const), realCompletionHaar_map_logSign hv⟩
    simpa only [one_mul] using h
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    rw [archimedeanAngularChart, dite_eq_right hv]
    dsimp only [P, AngularChart.coord, AngularChart.measure]
    rw [archimedeanCompletionHaar, dite_eq_right hv, hc.mult_eq_two, Nat.cast_ofNat]
    exact ⟨(measurable_const.mul hlog).prodMk
      (Complex.measurable_arg.comp (complexCompletionEmbedding hc).measurable),
      complexCompletionHaar_map_logPolar hc⟩

end Masullo
