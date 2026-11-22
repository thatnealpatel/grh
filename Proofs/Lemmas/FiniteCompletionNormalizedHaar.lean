module

public import Theorems.FiniteCompletionDifferentScale
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Lemmas.FiniteCompletionCompact

/-! # Normalized additive Haar measure at a finite place -/

open IsDedekindDomain MeasureTheory NumberField TopologicalSpace

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

private noncomputable def finiteCompletionIntegersCompact : PositiveCompacts F where
  carrier := (O : Set F)
  isCompact' := isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v)
  interior_nonempty' := by
    have hO : IsOpen (O : Set F) := Valued.isOpen_valuationSubring F
    rw [hO.interior_eq]
    exact ⟨0, zero_mem _⟩

/-- The integer ring has positive real mass for every additive Haar measure. -/
public theorem finiteCompletionIntegers_measureReal_pos [MeasurableSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] : 0 < μ.real (O : Set F) := by
  let hO := finiteCompletionIntegersCompact v
  change 0 < μ.real (hO : Set F)
  exact ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior μ hO.interior_nonempty).ne'
    hO.isCompact.measure_lt_top.ne

local notation "scale" =>
  (Real.sqrt (v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ))⁻¹

private theorem finiteCompletionHaarScale_pos : 0 < scale := by
  have hq : 0 < v.asIdeal.absNorm :=
    Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  have hpow : 0 < (v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ) := pow_pos hq _
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hpow))

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

/-- Additive Haar measure on the finite completion, scaled so that the integer ring has mass
equal to the inverse square root of the norm of the local different. -/
public noncomputable def finiteCompletionNormalizedHaar : Measure F :=
  ENNReal.ofReal scale • Measure.addHaarMeasure (finiteCompletionIntegersCompact v)

public instance finiteCompletionNormalizedHaar_isAddHaarMeasure :
    (finiteCompletionNormalizedHaar v).IsAddHaarMeasure := by
  unfold finiteCompletionNormalizedHaar
  exact Measure.IsAddHaarMeasure.smul _
    (ENNReal.ofReal_pos.mpr (finiteCompletionHaarScale_pos v)).ne' ENNReal.ofReal_ne_top

/-- The real mass of the finite-completion integers is the prescribed local different scale. -/
public theorem finiteCompletionNormalizedHaar_real :
    (finiteCompletionNormalizedHaar v).real (O : Set F) = scale := by
  let C := finiteCompletionIntegersCompact v
  change (ENNReal.ofReal scale * Measure.addHaarMeasure C C).toReal = scale
  rw [Measure.addHaarMeasure_self, mul_one,
    ENNReal.toReal_ofReal (finiteCompletionHaarScale_pos v).le]

end Masullo
