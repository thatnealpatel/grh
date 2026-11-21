module

public import Theorems.RationalAdeleUnramifiedPeriodization
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Lemmas.RationalAdeleIntegralPairing
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier transform of the rational unramified Schwartz tensor

With the unit-strip Haar normalization of Example A.3.1.8, p. 558, and
negative real Fourier sign of Example A.3.1.5, p. 557, the transform is
again unramified, with archimedean factor `𝓕 b`. This extends the tensor
calculation described there for the Gaussian, with the repaired diagonal
character. It uses only the measure on the integral-finite stage.
-/

open NumberField MeasureTheory Set
open scoped Classical ComplexConjugate FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "K" => RationalFiniteIntegers
local notation "W" => (rationalIntegralAdeles : Set A)
local notation "χ" => rationalAdeleAddChar
local notation "j" => rationalAdeleIntegralEmbedding
local notation "eᵣ" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

private theorem real_add (x y : A) : rationalAdeleReal (x + y) =
    rationalAdeleReal x + rationalAdeleReal y := by
  simp only [rationalAdeleReal_apply]
  exact map_add eᵣ _ _

private theorem real_embedding (z : ℝ × K) : rationalAdeleReal (j z) = z.1 :=
  rationalIntegralAdelesHomeomorph_real z

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

local notation "μA" => rationalAdeleAddHaar

private theorem integral_eq_zero_of_not_mem (b : 𝓢(ℝ, ℂ)) {y : A} (hy : y ∉ W) :
    (∫ x, rationalAdeleUnramified b x * conj (χ (x * y)) ∂μA) = 0 := by
  obtain ⟨u, hu, hreal, hχ⟩ := exists_rationalIntegralAdele_phase_ne_one hy
  let f : A → ℂ := fun x ↦ rationalAdeleUnramified b x * conj (χ (x * y))
  have hinv (x : A) : rationalAdeleUnramified b (u + x) = rationalAdeleUnramified b x := by
    have hmem : u + x ∈ W ↔ x ∈ W := by
      constructor
      · intro hx
        change x ∈ rationalIntegralAdeles
        simpa only [neg_add_cancel_left] using
          rationalIntegralAdeles.add_mem (rationalIntegralAdeles.neg_mem hu) hx
      · exact rationalIntegralAdeles.add_mem hu
    by_cases hx : x ∈ W
    · simp only [rationalAdeleUnramified, indicator_of_mem hx, indicator_of_mem (hmem.mpr hx),
        real_add, hreal, zero_add]
    · rw [rationalAdeleUnramified, indicator_of_notMem hx, indicator_of_notMem (mt hmem.mp hx)]
  have htranslate (x : A) : f (u + x) = conj (χ (u * y)) * f x := by
    simp only [f, hinv, add_mul, AddChar.map_add_eq_mul, map_mul]
    ring
  have hI : conj (χ (u * y)) * (∫ x, f x ∂μA) = (∫ x, f x ∂μA) := by
    rw [← integral_const_mul]
    simpa only [htranslate] using integral_add_left_eq_self (μ := μA) f u
  by_contra hne
  have hphase := (mul_eq_right₀ hne).mp hI
  exact hχ (star_injective (hphase.trans (map_one (starRingEnd ℂ)).symm))

/-- The normalized adelic Fourier integral of `b ⊗ 𝟙_{∏ₚ ℤₚ}` is
`(𝓕 b) ⊗ 𝟙_{∏ₚ ℤₚ}`, at every adelic frequency. -/
public theorem integral_rationalAdeleUnramified_mul_conj_char (b : 𝓢(ℝ, ℂ)) (y : A) :
    (∫ x, rationalAdeleUnramified b x * conj (χ (x * y)) ∂μA) =
      rationalAdeleUnramified (𝓕 b) y := by
  by_cases hy : y ∈ W
  · let f : A → ℂ := fun x ↦ b (rationalAdeleReal x) * conj (χ (x * y))
    have hfun (x : A) : rationalAdeleUnramified b x * conj (χ (x * y)) = indicator W f x := by
      by_cases hx : x ∈ W <;> simp [rationalAdeleUnramified, f, hx]
    simp_rw [hfun]
    have hj : MeasurableEmbedding j := isOpenEmbedding_rationalAdeleIntegralEmbedding.measurableEmbedding
    rw [integral_indicator isOpen_rationalIntegralAdeles.measurableSet,
      ← range_rationalAdeleIntegralEmbedding, ← hj.map_comap, hj.integral_map,
      comap_rationalAdeleAddHaar_integral, rationalAdeleUnramified, indicator_of_mem hy]
    have hprod (z : ℝ × K) : f (j z) =
        Complex.exp (↑(-2 * Real.pi * z.1 * rationalAdeleReal y) * Complex.I) • b z.1 := by
      dsimp only [f]
      rw [rationalAdeleAddChar_mul_of_integral (x := j z)
        (rationalIntegralAdelesHomeomorph z).property hy,
        real_embedding, ← Complex.exp_conj, smul_eq_mul, mul_comm]
      congr 2
      push_cast
      simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
      show (fun z ↦ f (j z)) = _ from funext hprod,
      integral_fun_fst (fun t : ℝ ↦
        Complex.exp (↑(-2 * Real.pi * t * rationalAdeleReal y) * Complex.I) • b t)]
    simp [Measure.real]
  · rw [integral_eq_zero_of_not_mem b hy, rationalAdeleUnramified, indicator_of_notMem hy]

end Masullo
