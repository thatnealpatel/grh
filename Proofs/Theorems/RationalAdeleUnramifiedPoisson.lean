module

public import Theorems.RationalAdelePoisson
public import Theorems.RationalAdeleUnramifiedFourier
import Lemmas.SchwartzLatticeTranslates

/-!
# Pointwise adelic Poisson summation for the rational unramified tensor

Theorem D.1.2.7(3), p. 749, applies here with no additional convergence
hypotheses. Only the diagonal integer frequencies survive on the Fourier side.
-/

open NumberField MeasureTheory Set
open scoped Classical ComplexConjugate FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "ι" => algebraMap ℚ A
local notation "χ" => rationalAdeleAddChar

private theorem unramified_algebraMap_int (b : 𝓢(ℝ, ℂ)) (n : ℤ) :
    rationalAdeleUnramified b (ι (n : ℚ)) = b (n : ℝ) := by
  rw [rationalAdeleUnramified, indicator_of_mem ((algebraMap_mem_rationalIntegralAdeles_iff _).mpr
    ⟨n, rfl⟩), rationalAdeleReal_algebraMap, Rat.cast_intCast]

private theorem unramified_algebraMap_eq_zero (b : 𝓢(ℝ, ℂ)) {r : ℚ}
    (hr : r ∉ range (Int.cast : ℤ → ℚ)) : rationalAdeleUnramified b (ι r) = 0 := by
  apply indicator_of_notMem
  intro h
  obtain ⟨n, hn⟩ := (algebraMap_mem_rationalIntegralAdeles_iff r).mp h
  exact hr ⟨n, hn.symm⟩

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Cq] [BorelSpace Cq]

/-- The rational diagonal periodization of the unramified Schwartz tensor equals
its character series over integer frequencies at every rational adele. Both
sides are absolutely summable, and both include the zero index. -/
public theorem hasSum_rationalAdeleUnramified_poisson (b : 𝓢(ℝ, ℂ)) (a : A) :
    HasSum (fun d : rationalDiagonal ↦ rationalAdeleUnramified b (a + (d : A)))
      (∑' n : ℤ, (𝓕 b) (n : ℝ) * χ (a * (n : A))) := by
  have hinj : Function.Injective (Int.cast : ℤ → ℚ) := Int.cast_injective
  have habs : Summable (fun n : ℤ ↦ ‖(𝓕 b) (n : ℝ)‖) := by
    simpa only [zero_add] using summable_norm_schwartz_add_int (𝓕 b) 0
  have hfour : Summable (fun r : ℚ ↦ ‖rationalAdeleUnramified (𝓕 b) (ι r)‖) := by
    apply (hinj.summable_iff (f := fun r : ℚ ↦ ‖rationalAdeleUnramified (𝓕 b) (ι r)‖)
      (fun r hr ↦ by rw [unramified_algebraMap_eq_zero _ hr, norm_zero])).mp
    simpa only [Function.comp_def, unramified_algebraMap_int] using habs
  have h := hasSum_rationalAdele_poisson (continuous_rationalAdeleUnramified b).measurable
    (integrable_rationalAdeleUnramified b) (summable_norm_rationalAdeleUnramified_add b)
    (continuous_rationalAdeleComplexPeriodization_unramified b)
    (by simpa only [integral_rationalAdeleUnramified_mul_conj_char] using hfour) a
  simp only [integral_rationalAdeleUnramified_mul_conj_char] at h
  have hreindex : (∑' r : ℚ, rationalAdeleUnramified (𝓕 b) (ι r) * χ (a * ι r)) =
      ∑' n : ℤ, (𝓕 b) (n : ℝ) * χ (a * (n : A)) := by
    rw [← hinj.tsum_eq (fun r hr ↦ by
      by_contra hnot
      apply hr
      change rationalAdeleUnramified (𝓕 b) (ι r) * χ (a * ι r) = 0
      rw [unramified_algebraMap_eq_zero _ hnot, zero_mul])]
    exact tsum_congr fun n ↦ by rw [unramified_algebraMap_int, map_intCast ι n]
  exact hreindex ▸ h

end Masullo
