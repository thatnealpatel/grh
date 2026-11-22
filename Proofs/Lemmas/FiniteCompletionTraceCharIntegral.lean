module

public import Lemmas.FiniteCompletionPadic
import Lemmas.FiniteCompletionCompact
public import Theorems.PadicStandardCharacter
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.RingTheory.Trace.Basic

/-! # Integrability of the finite-place Fourier kernel on the integer ring -/

open IsDedekindDomain NumberField MeasureTheory
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

/-- The conjugate trace character is integrable on the compact integer ring. -/
public theorem integrableOn_finiteCompletion_traceChar [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [IsFiniteMeasureOnCompacts μ] (x : F) :
    IntegrableOn (fun y : F ↦ star (padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y))))
      (O : Set F) μ := by
  let _ := finiteCompletion_moduleFinite v
  have hc : Continuous (fun y : F ↦ padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y))) :=
    (continuous_padicStdAddChar p).comp
    ((Algebra.trace ℚ_[p] F).continuous_of_finiteDimensional.comp (continuous_const.mul continuous_id))
  exact hc.star.continuousOn.integrableOn_compact
    (isCompact_iff_compactSpace.mpr (compactSpace_finiteCompletionIntegers K v))

end Masullo
