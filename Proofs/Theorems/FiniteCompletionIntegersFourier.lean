module

public import Lemmas.AddSubgroupCharIntegral
public import Lemmas.FiniteCompletionTraceAnnihilator
public import Lemmas.FiniteCompletionTraceCharIntegral
public import Lemmas.FiniteCompletionDifferentQuotient
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Fourier transform of the integer ring at a finite place

With the negative sign of Example A.3.1.5, the transform is supported on
the inverse local different. Its amplitude retains the given additive Haar
mass of the integer ring; no self-dual normalization is imposed.
-/

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
attribute [local instance] finiteCompletion_moduleFinite finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree

local notation "C" => ((differentIdeal ℤ_[p] O : FractionalIdeal O⁰ F)⁻¹ : FractionalIdeal O⁰ F)

/-- The negative-sign Fourier transform of `1_O` is the Haar mass of `O`
times the indicator of its codifferent over the canonical base `ℤ_[p]`. -/
public theorem finiteCompletionIntegers_fourier [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (x : F) :
    (∫ y in (O : Set F), star (padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y))) ∂μ) =
      (μ.real (O : Set F) : ℂ) * (C : Set F).indicator (fun _ ↦ (1 : ℂ)) x := by
  classical
  let χ (y : F) := padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y))
  have hadd (a b : F) : χ (a + b) = χ a * χ b := by
    simp only [χ, mul_add, map_add, AddChar.map_add_eq_mul]
  have hO : MeasurableSet (O : Set F) := (Valued.isOpen_valuationSubring F).measurableSet
  have hann : (∀ y ∈ (O).toSubring.toAddSubgroup, χ y = 1) ↔ x ∈ C := by
    calc
      _ ↔ ∀ y : O, χ y = 1 := ⟨fun h y ↦ h y y.property, fun h y hy ↦ h ⟨y, hy⟩⟩
      _ ↔ _ := by
        have ht := finiteCompletion_traceChar_trivial_iff v x
        rw [finiteCompletion_traceDual_eq_inv_differentIdeal v] at ht
        exact ht
  calc
    _ = (if ∀ y ∈ (O).toSubring.toAddSubgroup, χ y = 1 then (μ.real (O : Set F) : ℂ) else 0) :=
      addSubgroup_integral_star_char (O).toSubring.toAddSubgroup hO μ χ hadd
    _ = _ := by
      by_cases hx : x ∈ C
      · rw [ite_eq_left (hann.mpr hx), indicator_of_mem hx, mul_one]
      · rw [ite_eq_right (mt hann.mp hx), indicator_of_notMem hx, mul_zero]

end Masullo
