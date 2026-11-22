module

public import Lemmas.FiniteCompletionCompact
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.LinearAlgebra.Countable

/-! # Integral-unit invariance of additive Haar at finite places -/

open IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

/-- The integer ring of a finite completion is its closed unit ball. -/
public theorem finiteCompletionIntegers_eq_closedBall : (O : Set F) = Metric.closedBall 0 1 := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
  change (x ∈ O) ↔ _
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

/-- Multiplication by an integral unit preserves any additive Haar measure.
Indeed, it preserves the integer ball that normalizes Haar uniqueness. -/
public theorem finiteCompletion_measurePreserving_mul_unit [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (u : Fˣ) (hu : ‖(u : F)‖ = 1) :
    MeasurePreserving (ContinuousAddEquiv.mulLeft u : F → F) μ μ := by
  let e := ContinuousAddEquiv.mulLeft u
  let ν := Measure.map e μ
  have : ν.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map _ e
  let : Countable K := Countable.of_moduleFinite (R := ℚ)
  let : SeparableSpace F := ⟨range (algebraMap K F), countable_range _, v.denseRange_algebraMap K⟩
  let : SecondCountableTopology F := inferInstance
  have ho : IsOpen (O : Set F) := Valued.isOpen_valuationSubring F
  let B : PositiveCompacts F :=
    ⟨⟨(O : Set F), isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v)⟩,
      by
        change (interior (O : Set F)).Nonempty
        rw [ho.interior_eq]
        exact ⟨0, zero_mem O⟩⟩
  let : LocallyCompactSpace F := B.locallyCompactSpace_of_addGroup
  have hpre : e ⁻¹' (O : Set F) = (O : Set F) := by
    rw [finiteCompletionIntegers_eq_closedBall v]
    ext x
    simp [e, Metric.mem_closedBall, dist_zero_right, norm_mul, hu]
  have hmass : ν B = μ B := by
    change Measure.map e μ (O : Set F) = μ (O : Set F)
    have he : Measurable (e : F → F) := e.continuous.measurable
    rw [Measure.map_apply he ho.measurableSet, hpre]
  exact ⟨e.continuous.measurable, by
    rw [show Measure.map e μ = ν from rfl, Measure.addHaarMeasure_unique ν B, hmass,
      ← Measure.addHaarMeasure_unique μ B]⟩

end Masullo
