module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Set

namespace Masullo

/-- `dt / |t|` on the ambient real line, supported off zero. -/
@[expose]
public noncomputable def realMultiplicativeDensity : Measure ℝ :=
  ((volume : Measure ℝ).restrict ({0}ᶜ)).withDensity (fun t ↦ ENNReal.ofReal |t|⁻¹)

public theorem realMultiplicativeDensity_apply {s : Set ℝ} (hs : MeasurableSet s)
    (h₀ : s ⊆ ({0} : Set ℝ)ᶜ) :
    realMultiplicativeDensity s = ∫⁻ t in s, ENNReal.ofReal |t|⁻¹ := by
  rw [realMultiplicativeDensity, withDensity_apply _ hs, Measure.restrict_restrict hs,
    inter_eq_left.mpr h₀]

/-- The Jacobian `|a|` cancels the scaling of the density, for either sign of `a`. -/
public theorem realMultiplicativeDensity_image_mul {a : ℝ} (ha : a ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) (h₀ : s ⊆ ({0} : Set ℝ)ᶜ) :
    realMultiplicativeDensity ((a * ·) '' s) = realMultiplicativeDensity s := by
  have hm : MeasurableSet ((a * ·) '' s) :=
    (Homeomorph.mulLeft₀ a ha).measurableEmbedding.measurableSet_image' hs
  have hm₀ : (a * ·) '' s ⊆ ({0} : Set ℝ)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    exact mul_ne_zero ha (h₀ ht)
  rw [realMultiplicativeDensity_apply hm hm₀, realMultiplicativeDensity_apply hs h₀,
    lintegral_image_eq_lintegral_abs_deriv_mul (f' := fun _ ↦ a) hs
      (fun t _ ↦ by
        have hd : HasDerivAt (a * ·) a t := by
          simpa only [id, mul_one] using (hasDerivAt_id t).const_mul a
        exact hd.hasDerivWithinAt)
      (fun _ _ _ _ h ↦ mul_left_cancel₀ ha h)]
  apply lintegral_congr
  intro t
  rw [abs_mul, ← ENNReal.ofReal_mul (abs_nonneg a), mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.mpr ha), one_mul]

end Masullo
