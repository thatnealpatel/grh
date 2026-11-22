module

public import Theorems.FiniteHeckeCharacterEulerProduct
public import Props.CompactLogMellin
import Lemmas.CompactLogMellinInversion

/-!
# Finite-place Mellin inversion for Hecke characters

In (B.4.2.10)–(11), p. 615, Masullo invokes Mellin inversion separately
for the direct and reflected terms. The normalization is the one in
(B.4.2.4): Both lines are upward and `ds / (2πi) = dt / (2π)`.
The reflected weight changes the sample to `exp(-y) * g(-y)`, not its
sign. Fourier inversion with ordinary angular frequency supplies the
normalization and corrects the relative sign in the extracted formulas.
The negative signs in the two series below are those of (B.4.2.7).
These are finite-product statements, independent of contour reflection
and of the identification of the reflected character.
-/

open Complex IsDedekindDomain MeasureTheory NumberField
open scoped ContDiff

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)

-- Both legs use the same exchange of the integral with the joint series.
-- The weight and its inversion are supplied separately to preserve the coefficients.
private theorem finiteHecke_right_line_evaluation {a : ℝ} (ha : 1 < a)
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    {W : ℝ → ℂ} (hW : Integrable W) (sample : ℝ → ℂ)
    (hInv : ∀ y : ℝ,
      (∫ t : ℝ, W t * exp (-((a : ℂ) + (t : ℂ) * I) * y)) / (2 * (Real.pi : ℂ)) =
        sample y) :
    let s := fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I
    let A := fun p : Places × ℕ ↦ (Real.log (finitePlaceNorm p.1) : ℂ) *
      finiteHeckeCoefficient χ p.1 ^ (p.2 + 1) * sample ((p.2 + 1 : ℕ) * Real.log (finitePlaceNorm p.1))
    Integrable (fun t ↦ W t * logDeriv (finiteHeckeCharacterEulerProduct χ) (s t)) ∧
    Summable (fun p ↦ ‖A p‖) ∧
    (∫ t, W t * logDeriv (finiteHeckeCharacterEulerProduct χ) (s t)) / (2 * (Real.pi : ℂ)) =
      -(∑' p, A p) := by
  let s (t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * I
  let z := finiteHeckeCoefficient χ
  let F (p : Places × ℕ) (t : ℝ) := W t * finiteHeckeTerm z (s t) p
  let y (p : Places × ℕ) : ℝ := (p.2 + 1 : ℕ) * Real.log (finitePlaceNorm p.1)
  let b (p : Places × ℕ) : ℂ := (Real.log (finitePlaceNorm p.1) : ℂ) * z p.1 ^ (p.2 + 1)
  let J (t : ℝ) := W t * logDeriv (finiteHeckeCharacterEulerProduct χ) (s t)
  let c : ℂ := 2 * (Real.pi : ℂ)
  change Integrable J ∧ Summable (fun p ↦ ‖b p * sample (y p)‖) ∧
    (∫ t, J t) / c = -(∑' p, b p * sample (y p))
  -- The positive series represents the negative logarithmic derivative.
  have hsum (t : ℝ) : (∑' p, F p t) = -J t := by
    have hs : 1 < (s t).re := by simpa [s] using ha
    simp only [F, tsum_mul_left, J, z,
      (finiteHeckeCharacterEulerProduct_logDeriv χ hχ hs).2.2.tsum_eq, mul_neg]
  obtain ⟨_, hL1, hi, hExchange⟩ :=
    finiteHecke_right_line_integrals ha (norm_finiteHeckeCoefficient_le_one χ hχ) hW
  change Integrable (fun t ↦ ∑' p, F p t) at hi
  change Summable (fun p ↦ ∫ t, ‖F p t‖) at hL1
  change (∫ t, ∑' p, F p t) = ∑' p, ∫ t, F p t at hExchange
  -- After the joint L¹ exchange, invert the scalar weight at each log prime power.
  have hterm (p : Places × ℕ) : (∫ t, F p t) / c = b p * sample (y p) := by
    have hphase (t : ℝ) : F p t = b p * (W t * exp (-(s t) * (y p : ℂ))) := by
      unfold F b y finiteHeckeTerm
      simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
      rw [show -((p.2 + 1 : ℕ) : ℂ) * s t * (Real.log (finitePlaceNorm p.1) : ℂ) =
        -(s t) * (((p.2 + 1 : ℕ) : ℂ) * (Real.log (finitePlaceNorm p.1) : ℂ)) by ring]
      ring
    simp_rw [hphase, integral_const_mul, mul_div_assoc]
    exact congrArg (b p * ·) (hInv (y p))
  have hsum' : (fun t ↦ ∑' p, F p t) = -J := funext hsum
  rw [hsum'] at hi
  refine ⟨by simpa only [neg_neg] using hi.neg, ?_, ?_⟩
  · refine (hL1.mul_right ‖c‖⁻¹).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_)
    rw [← hterm, norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (by positivity)
  · calc
      (∫ t, J t) / c = -((∫ t, ∑' p, F p t) / c) := by
        simp_rw [hsum, integral_neg, neg_div, neg_neg]
      _ = -(∑' p, b p * sample (y p)) := by
        rw [hExchange, ← tsum_div_const, tsum_congr hterm]

/-- The direct finite-place integral (B.4.2.10), with ordinary Lebesgue
measure and the `1 / (2π)` required by the contour normalization. -/
public theorem finiteHecke_direct_right_line {a : ℝ} (ha : 1 < a)
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let s := fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I
    let A := fun p : Places × ℕ ↦
      let l := Real.log (finitePlaceNorm p.1)
      let y : ℝ := (p.2 + 1 : ℕ) * l
      (l : ℂ) * finiteHeckeCoefficient χ p.1 ^ (p.2 + 1) * g y
    Integrable (fun t ↦ compactLogMellin g (s t) * logDeriv (finiteHeckeCharacterEulerProduct χ) (s t)) ∧
    Summable (fun p ↦ ‖A p‖) ∧
    (∫ t, compactLogMellin g (s t) * logDeriv (finiteHeckeCharacterEulerProduct χ) (s t)) /
      (2 * (Real.pi : ℂ)) = -(∑' p, A p) :=
  finiteHecke_right_line_evaluation ha χ hχ (integrable_compactLogMellin_vertical hg hc a) g
    (compactLogMellin_right_line_evaluation hg hc a)

/-- The reflected finite-place integral (B.4.2.11) has its own character
`ψ`, which can be the conjugate of `χ` in the contour. The sample at `-y`
carries the reciprocal norm power `exp(-y)`, with no extra orientation sign. -/
public theorem finiteHecke_reflected_right_line {a : ℝ} (ha : 1 < a)
    (ψ : HeckeCharacter (𝓞 K) K) (hψ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖ψ x‖ = 1)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let s := fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I
    let A := fun p : Places × ℕ ↦
      let l := Real.log (finitePlaceNorm p.1)
      let y : ℝ := (p.2 + 1 : ℕ) * l
      (l : ℂ) * finiteHeckeCoefficient ψ p.1 ^ (p.2 + 1) * (exp (-y) * g (-y))
    Integrable (fun t ↦ compactLogMellin g (1 - s t) * logDeriv (finiteHeckeCharacterEulerProduct ψ) (s t)) ∧
    Summable (fun p ↦ ‖A p‖) ∧
    (∫ t, compactLogMellin g (1 - s t) * logDeriv (finiteHeckeCharacterEulerProduct ψ) (s t)) /
      (2 * (Real.pi : ℂ)) = -(∑' p, A p) :=
  finiteHecke_right_line_evaluation ha ψ hψ (integrable_compactLogMellin_reflected_vertical hg hc a)
    (fun y ↦ exp (-y) * g (-y)) (compactLogMellin_reflected_right_line_evaluation hg hc a)

end Masullo
