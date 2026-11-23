module

public import Theorems.IdeleClassDiagonalAverage

/-! # Integrated class-Haar diagonal cancellation

Transfer the spectral box limit to the difference kernel on the actual class
quotient before integrating; no limit is interchanged with an integral.
-/

open Filter MeasureTheory NumberField Set
open scoped Masullo Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)]
  [BorelSpace (IdeleClassGroup (𝓞 K) K)]

/-- For the same class Haar measure in the product boxes and on their
centers, an integrable representative of the spectral limit gives an
integrable representative of the geometric limit and the first integral
equality on Masullo p. 15. The representative is the pointwise negative
of `dSpec`, and its recovery by geometric averages is only almost
everywhere. This implication works for any Borel `μ` on the class group;
it neither supplies the spectral limit nor identifies its integral as a trace. -/
public theorem ideleClassDiagonalAverage_sub_integrable_integral_eq_neg
    (μ : Measure C) {φ : C → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hφ : tsupport φ ⊆ {g | 1 + ε < ideleClassNorm g})
    (U : ℕ → Set C) (hU : ∀ n, MeasurableSet (U n))
    (hshrink : ∀ V ∈ 𝓝 (1 : C), ∀ᶠ n in atTop, U n ⊆ V)
    (k : C × C → ℂ) (dSpec : C → ℂ) (hSpec : Integrable dSpec μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ ideleClassDiagonalAverage μ (U n) k x)
      atTop (𝓝 (dSpec x))) :
    let dGeom : C → ℂ := fun x ↦ -dSpec x
    Integrable dGeom μ ∧
      (∀ᵐ x ∂μ, Tendsto
        (fun n ↦ ideleClassDiagonalAverage μ (U n) (fun p ↦ φ (p.1 / p.2) - k p) x)
        atTop (𝓝 (dGeom x))) ∧
      (∫ x, dGeom x ∂μ) = -(∫ x, dSpec x ∂μ) := by
  refine ⟨hSpec.neg, ?_, integral_neg dSpec⟩
  filter_upwards [hlim] with x hx
  exact (ideleClassDiagonalAverage_sub_tendsto_iff μ hε hφ U hU hshrink k x (dSpec x)).mpr hx

end Masullo
