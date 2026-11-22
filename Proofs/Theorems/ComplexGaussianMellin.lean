module

public import Props.ArchimedeanGammaLogDerivative
import Lemmas.ComplexGaussianPolar
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The complex local Gaussian zeta integral

The bilinear integral (3.3.1.7), p. 130, pairs the test with the character,
not with its inverse. In the text-based reading of (3.4.3.5)–(6), p. 152,
the printed test has the same angular weight as the character. For weight
one, rotation by `i` then negates the integrand, incompatible with the
nonzero factor required by (3.4.3.12)–(13), p. 153. We instead give the test
the opposite weight. The theorem below supplies absolute convergence and
recovers (3.2.1.5), p. 123, with the stated Tamagawa normalization. The
radial exponent applies to the squared Euclidean norm (§A.1, p. 539),
not to the Euclidean radius.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace Masullo

/-- The corrected Gaussian monomial has angular weight `-n`. -/
public noncomputable def complexZetaGaussian (n : ℤ) (z : ℂ) : ℂ :=
  (1 / (2 * Real.pi : ℝ) : ℝ) *
    (if 0 ≤ n then conj z ^ n.toNat else z ^ n.natAbs) *
    exp (-(2 * Real.pi * ‖z‖ ^ 2 : ℝ))

/-- The bilinear zeta integrand against additive Lebesgue measure on `ℂ`.
Definitions A.3.1.2(2), p. 556, and A.3.2.2(1), p. 560, give the
multiplicative density `2 / ‖z‖²` off zero. The integrand is zero at the origin. -/
public noncomputable def complexGaussianZetaDensity (n : ℤ) (τ : ℝ) (s z : ℂ) : ℂ :=
  complexZetaGaussian n z * (z / (‖z‖ : ℂ)) ^ n *
    ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (s + (τ : ℂ) * I) * (2 / ‖z‖ ^ 2 : ℝ)

private theorem opposite_angular_cancellation (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    (if 0 ≤ n then conj z ^ n.toNat else z ^ n.natAbs) *
      (z / (‖z‖ : ℂ)) ^ n = (‖z‖ : ℂ) ^ n.natAbs := by
  have hr := norm_pos_iff.mpr hz
  have hr₀ := ofReal_ne_zero.mpr hr.ne'
  split_ifs with hn
  · have hn' : n.toNat = n.natAbs := by omega
    have hcast := congrArg (fun k : ℤ ↦ (z / (‖z‖ : ℂ)) ^ k) (Int.toNat_of_nonneg hn).symm
    rw [hcast, zpow_natCast, hn', ← mul_pow]
    congr 1
    rw [← mul_div_assoc, mul_comm (conj z) z, Complex.mul_conj, normSq_eq_norm_sq, ofReal_pow, pow_two,
      mul_div_cancel_right₀ _ hr₀]
  · have hn' : n = -(n.natAbs : ℤ) := by omega
    have hcast := congrArg (fun k : ℤ ↦ (z / (‖z‖ : ℂ)) ^ k) hn'
    rw [hcast, zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
    congr 1
    rw [inv_div, ← mul_div_assoc, mul_comm z, mul_div_cancel_right₀ _ hz]

/-- With the opposite angular weight in the test, the complex local zeta
integral is absolutely convergent and equals the shifted scalar Gamma factor. -/
public theorem complexGaussianZetaDensity_integral (n : ℤ) (τ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (complexGaussianZetaDensity n τ s) ∧
      (∫ z : ℂ, complexGaussianZetaDensity n τ s z) =
        archimedeanGammaFactor (2 * Real.pi) 1 ((n.natAbs : ℝ) / 2) τ s := by
  let B : ℝ := 2 * Real.pi
  let w := s + (τ : ℂ) * I
  let a := s + (((n.natAbs : ℝ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I
  let G (t : ℝ) := (t : ℂ) ^ (a - 1) * exp (-(B * t : ℝ))
  have hB : 0 < B := by dsimp [B]; positivity
  have ha : 0 < a.re := by
    simp [a, mul_re]
    positivity
  -- Polar reduction cancels the angular factors and leaves the square-map Jacobian.
  have hpol (p : ℝ × ℝ) (hp : 0 < p.1) :
      p.1 • complexGaussianZetaDensity n τ s (Complex.polarCoord.symm p) =
        ((B : ℂ)⁻¹) * ((2 * p.1) • G (p.1 ^ 2)) := by
    let z := Complex.polarCoord.symm p
    have hr : ‖z‖ = p.1 := (norm_polarCoord_symm p).trans (abs_of_pos hp)
    have hz : z ≠ 0 := norm_pos_iff.mp (hr ▸ hp)
    have ht : 0 < p.1 ^ 2 := by positivity
    have ht₀ := ofReal_ne_zero.mpr ht.ne'
    have hpow : ((p.1 ^ 2 : ℝ) : ℂ) ^ (a - 1) * ((p.1 ^ 2 : ℝ) : ℂ) =
        (p.1 : ℂ) ^ n.natAbs * ((p.1 ^ 2 : ℝ) : ℂ) ^ w := by
      have hsq : ((p.1 ^ 2 : ℝ) : ℂ) ^ (((n.natAbs : ℝ) / 2 : ℝ) : ℂ) =
          (p.1 : ℂ) ^ n.natAbs := by
        rw [← Real.rpow_two, ← cpow_mul_ofReal_nonneg hp.le,
          show ((2 : ℝ) : ℂ) * (((n.natAbs : ℝ) / 2 : ℝ) : ℂ) = (n.natAbs : ℂ) by
            push_cast; ring, cpow_natCast]
      calc
        _ = ((p.1 ^ 2 : ℝ) : ℂ) ^ (a - 1) * ((p.1 ^ 2 : ℝ) : ℂ) ^ (1 : ℂ) := by
          rw [cpow_one]
        _ = ((p.1 ^ 2 : ℝ) : ℂ) ^ a := by
          rw [← cpow_add _ _ ht₀, sub_add_cancel]
        _ = _ := by
          rw [show a = ((n.natAbs : ℝ) / 2 : ℝ) + w by dsimp [a, w]; ring,
            cpow_add _ _ ht₀, hsq]
    change p.1 • complexGaussianZetaDensity n τ s z = _
    unfold complexGaussianZetaDensity complexZetaGaussian
    rw [show (1 / (2 * Real.pi) : ℝ) = B⁻¹ by simp [B], ofReal_inv]
    have hcancel := opposite_angular_cancellation n hz
    rw [show _ * exp (-(2 * Real.pi * ‖z‖ ^ 2 : ℝ)) * (z / (‖z‖ : ℂ)) ^ n =
      (B : ℂ)⁻¹ * ((if 0 ≤ n then conj z ^ n.toNat else z ^ n.natAbs) *
        (z / (‖z‖ : ℂ)) ^ n) * exp (-(2 * Real.pi * ‖z‖ ^ 2 : ℝ)) by ring,
      hcancel, hr]
    change p.1 • ((↑B)⁻¹ * (p.1 : ℂ) ^ n.natAbs * exp (-(2 * Real.pi * p.1 ^ 2 : ℝ)) *
      ((p.1 ^ 2 : ℝ) : ℂ) ^ w * (2 / p.1 ^ 2 : ℝ)) = _
    rw [show (↑B)⁻¹ * (p.1 : ℂ) ^ n.natAbs * exp (-(2 * Real.pi * p.1 ^ 2 : ℝ)) *
      ((p.1 ^ 2 : ℝ) : ℂ) ^ w =
      (↑B)⁻¹ * ((p.1 : ℂ) ^ n.natAbs * ((p.1 ^ 2 : ℝ) : ℂ) ^ w) *
        exp (-(2 * Real.pi * p.1 ^ 2 : ℝ)) by ring, ← hpow]
    simp only [G, Complex.real_smul, ofReal_div, ofReal_mul, ofReal_ofNat, B]
    field_simp
  have hm : Measurable (complexGaussianZetaDensity n τ s) := by
    unfold complexGaussianZetaDensity
    have hE : Measurable (complexZetaGaussian n) := by
      unfold complexZetaGaussian
      split_ifs <;> fun_prop
    have hrad := measurable_cpow_ofReal_nonneg (r := fun z : ℂ ↦ ‖z‖ ^ 2)
      (by fun_prop) (fun _ ↦ sq_nonneg _) w
    fun_prop
  -- Substituting `t = r²` and integrating the full angle cancels the test's `1/(2π)`.
  obtain ⟨hG, hsubst⟩ := square_radial_substitution (integrableOn_scaledGammaDensity hB ha)
  obtain ⟨hi, hpolar⟩ := complex_polar_radial hm (hG.const_mul ((B : ℂ)⁻¹)) hpol
  refine ⟨hi, ?_⟩
  rw [hpolar, integral_const_mul, hsubst, Complex.real_smul, ← mul_assoc,
    mul_inv_cancel₀ (ofReal_ne_zero.mpr hB.ne'), one_mul]
  -- Euler's Gamma integral at positive scale gives the scalar factor.
  rw [show (∫ t in Ioi (0 : ℝ), G t) = (1 / (B : ℂ)) ^ a * Gamma a by
    simpa only [G, ofReal_neg, ofReal_mul] using integral_cpow_mul_exp_neg_mul_Ioi ha hB]
  rw [archimedeanGammaFactor_complex]
  change (1 / (B : ℂ)) ^ a * Gamma a = Gammaℂ a / 2
  rw [Gammaℂ_def]
  have harg : (B : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hB.le]
    exact Real.pi_pos.ne
  rw [one_div, inv_cpow _ _ harg, ← cpow_neg]
  push_cast [B]
  ring

end Masullo
