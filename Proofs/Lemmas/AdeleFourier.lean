module

public import Lemmas.AdeleRestrictedProductMeasure
public import Theorems.AdeleTraceCharacter

/-! # Fourier integration with the adelic trace pairing -/

open IsDedekindDomain MeasureTheory NumberField
open scoped ComplexConjugate Masullo.AdeleStage

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K

/-- Fourier integration with the conjugated global trace character. -/
@[expose] public noncomputable def adeleFourier (μ : Measure A) (f : A → ℂ) (z : A) : ℂ :=
  ∫ w, f w * conj (numberFieldAdeleAddChar (w * z)) ∂μ

end Masullo
