module

public import Lemmas.FiniteCompletionCodifferentFourier
public import Lemmas.FiniteCompletionCodifferentMass
public import Lemmas.FiniteCompletionNormalizedHaar

/-! # Fourier inversion on the integer-ring test at a finite place -/

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
set_option quotPrecheck false in
local notation "B" => (O : Set F).indicator (fun _ ↦ (1 : ℂ))
variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

/-- Fourier transform with the negative sign and the canonical trace character. -/
@[expose] public noncomputable def finiteCompletionFourier (μ : Measure F) (f : F → ℂ) (x : F) : ℂ :=
  ∫ y, f y * star (padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y))) ∂μ

omit [BorelSpace (v.adicCompletion K)] in
private theorem fourier_indicator (μ : Measure F) (S : Set F) (hS : MeasurableSet S) (x : F) :
    finiteCompletionFourier v μ (S.indicator (fun _ ↦ (1 : ℂ))) x =
      ∫ y in S, star (padicStdAddChar p (Algebra.trace ℚ_[p] F (x * y))) ∂μ := by
  rw [finiteCompletionFourier, ← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ S <;> simp [hy]

/-- The first transform has amplitude `μ.real O` and support the inverse different. -/
public theorem finiteCompletionFourier_integers (μ : Measure F) [μ.IsAddHaarMeasure] (x : F) :
    finiteCompletionFourier v μ B x =
      (μ.real (O : Set F) : ℂ) * (C : Set F).indicator (fun _ ↦ (1 : ℂ)) x := by
  exact (fourier_indicator v μ (O : Set F) (Valued.isOpen_valuationSubring F).measurableSet x).trans
    (finiteCompletionIntegers_fourier v μ x)

/-- The first transform for the constructed measure, with no prescribed-mass hypothesis. -/
public theorem finiteCompletionNormalizedHaar_fourier_integers (x : F) :
    finiteCompletionFourier v (finiteCompletionNormalizedHaar v) B x =
      (((Real.sqrt (v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ))⁻¹ : ℝ) : ℂ) *
        (C : Set F).indicator (fun _ ↦ (1 : ℂ)) x := by
  rw [finiteCompletionFourier_integers, finiteCompletionNormalizedHaar_real]

private theorem fourier_square_masses (μ : Measure F) [μ.IsAddHaarMeasure] (x : F) :
    finiteCompletionFourier v μ (finiteCompletionFourier v μ B) x =
      (μ.real (O : Set F) : ℂ) * ((μ.real (C : Set F) : ℂ) * B x) := by
  rw [finiteCompletionFourier]
  simp_rw [finiteCompletionFourier_integers, mul_assoc]
  rw [integral_const_mul]
  congr 1
  exact (fourier_indicator v μ _ (measurableSet_finiteCompletion_codifferent v) x).trans
    (finiteCompletion_codifferent_fourier v μ x)

private theorem square_scalar_iff (n : ℕ) (hn : 0 < n) (m : ℝ) (hm : 0 < m) :
    (n : ℂ) * (m : ℂ) ^ 2 = 1 ↔ m = (Real.sqrt n)⁻¹ := by
  have hpos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  constructor
  · intro h
    have e : (n : ℝ) * m ^ 2 = 1 := by exact_mod_cast h
    rw [← one_div, eq_div_iff hpos.ne']
    have hs : (m * Real.sqrt n)^2 = 1 := by rw [mul_pow, hsq, mul_comm]; exact e
    nlinarith [mul_pos hm hpos]
  · rintro rfl
    have e : (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 = 1 := by
      rw [inv_pow, hsq, mul_inv_cancel₀ (by positivity : (n : ℝ) ≠ 0)]
    exact_mod_cast e

local notation "N" => (v.asIdeal.absNorm ^ finiteCompletionDifferentExponent v : ℕ)

/-- Both transforms use the same additive Haar. Its squared mass is multiplied
by the actual index of the integer lattice inside the inverse different. -/
public theorem finiteCompletionFourier_square_integers (μ : Measure F) [μ.IsAddHaarMeasure] (x : F) :
    finiteCompletionFourier v μ (finiteCompletionFourier v μ B) x =
      (N : ℂ) * (μ.real (O : Set F) : ℂ) ^ 2 * B x := by
  rw [fourier_square_masses, finiteCompletion_codifferent_measureReal, Complex.ofReal_mul]
  push_cast
  ring

/-- The positive square-root branch is forced already by inversion on `1_O`. -/
public theorem finiteCompletionFourier_square_integers_eq_iff (μ : Measure F) [μ.IsAddHaarMeasure] :
    finiteCompletionFourier v μ (finiteCompletionFourier v μ B) = B ↔
      μ.real (O : Set F) = (Real.sqrt N)⁻¹ := by
  have hn : 0 < N := pow_pos (Nat.pos_of_ne_zero fun h ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)) _
  have he := square_scalar_iff N hn _ (finiteCompletionIntegers_measureReal_pos v μ)
  constructor
  · intro h
    have h₀ := congrFun h 0
    rw [finiteCompletionFourier_square_integers] at h₀
    exact he.1 (by simpa using h₀)
  · intro h
    funext x
    rw [finiteCompletionFourier_square_integers, he.2 h, one_mul]

/-- Actual inversion on the test, for the constructed Haar. -/
public theorem finiteCompletionNormalizedHaar_fourier_inversion :
    finiteCompletionFourier v (finiteCompletionNormalizedHaar v)
      (finiteCompletionFourier v (finiteCompletionNormalizedHaar v) B) = B :=
  (finiteCompletionFourier_square_integers_eq_iff v _).2 (finiteCompletionNormalizedHaar_real v)

end Masullo
