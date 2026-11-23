module

public import Props.ArchimedeanGammaLogDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exponential lower bounds for the normalized archimedean factors on `Re s = 2`. -/

open Complex
open scoped ComplexConjugate

namespace Masullo

private theorem sinh_le_mul_exp (x : ℝ) : Real.sinh x ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-2 * x)) (Real.exp_pos x).le
  rw [← Real.exp_add, show -2 * x + x = -x by ring] at h
  rw [Real.sinh_eq]
  linarith only [h]

/-- Reflection at `iu`, recurrence, and conjugation give the squared modulus
identity in a form with no division by `sinh`. -/
private theorem norm_Gamma_one_add_mul_I_sq_mul_abs_sinh {u : ℝ} (hu : u ≠ 0) :
    ‖Gamma (1 + (u : ℂ) * I)‖ ^ 2 * |Real.sinh (Real.pi * u)| = Real.pi * |u| := by
  let z : ℂ := (u : ℂ) * I
  have hz : z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hu) I_ne_zero
  have hsin : ‖sin ((Real.pi : ℂ) * z)‖ = |Real.sinh (Real.pi * u)| := by
    rw [show (Real.pi : ℂ) * z = ((Real.pi * u : ℝ) : ℂ) * I by simp [z, mul_assoc],
      sin_mul_I, ← ofReal_sinh, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  have hs : sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [← norm_ne_zero_iff, hsin, abs_ne_zero, Real.sinh_ne_zero]
    exact mul_ne_zero Real.pi_ne_zero hu
  have hconj : 1 - z = conj (1 + z) := by simp [z, sub_eq_add_neg]
  have href : Gamma (1 + z) * Gamma (1 - z) * sin ((Real.pi : ℂ) * z) = z * Real.pi := by
    rw [add_comm 1 z, Gamma_add_one z hz, mul_assoc z, mul_assoc z,
      Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hs]
  have h := congrArg (fun w : ℂ ↦ ‖w‖) href
  change ‖Gamma (1 + z) * Gamma (1 - z) * sin ((Real.pi : ℂ) * z)‖ =
    ‖z * (Real.pi : ℂ)‖ at h
  rw [hconj, Gamma_conj, norm_mul, norm_mul, norm_conj, hsin, norm_mul] at h
  simpa [z, norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos, pow_two, mul_comm |u| Real.pi]
    using h

private theorem exp_le_norm_Gamma_one_add_mul_I (u : ℝ) :
    Real.exp (-(Real.pi * |u| / 2)) ≤ ‖Gamma (1 + (u : ℂ) * I)‖ := by
  by_cases hu : u = 0
  · simp [hu, Gamma_one]
  have hπu := mul_pos Real.pi_pos (abs_pos.mpr hu)
  have hs : |Real.sinh (Real.pi * u)| ≤ (Real.pi * |u|) * Real.exp (Real.pi * |u|) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
    exact sinh_le_mul_exp _
  have hsq : 1 ≤ ‖Gamma (1 + (u : ℂ) * I)‖ ^ 2 * Real.exp (Real.pi * |u|) := by
    apply le_of_mul_le_mul_left _ hπu
    calc
      _ = ‖Gamma (1 + (u : ℂ) * I)‖ ^ 2 * |Real.sinh (Real.pi * u)| := by
        rw [norm_Gamma_one_add_mul_I_sq_mul_abs_sinh hu, mul_one]
      _ ≤ ‖Gamma (1 + (u : ℂ) * I)‖ ^ 2 * ((Real.pi * |u|) * Real.exp (Real.pi * |u|)) :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)
      _ = _ := by ring
  apply (sq_le_sq₀ (Real.exp_pos _).le (norm_nonneg _)).mp
  rw [pow_two, ← Real.exp_add, show -(Real.pi * |u| / 2) + -(Real.pi * |u| / 2) =
    -(Real.pi * |u|) by ring, Real.exp_neg, ← one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr hsq

private theorem norm_Gamma_half_add_mul_I_sq_mul_cosh (u : ℝ) :
    ‖Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2 * Real.cosh (Real.pi * u) = Real.pi := by
  let z : ℂ := 1 / 2 + (u : ℂ) * I
  have hsin : sin ((Real.pi : ℂ) * z) = (Real.cosh (Real.pi * u) : ℂ) := by
    rw [show (Real.pi : ℂ) * z = Real.pi / 2 + ((Real.pi * u : ℝ) : ℂ) * I by
      dsimp [z]
      push_cast
      ring, sin_add, sin_pi_div_two, cos_pi_div_two, one_mul, zero_mul, add_zero,
      cos_mul_I, ofReal_cosh]
  have hs : sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [hsin]
    exact ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have hconj : 1 - z = conj z := by
    dsimp [z]
    rw [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
    ring
  have href : Gamma z * Gamma (1 - z) * sin ((Real.pi : ℂ) * z) = Real.pi := by
    rw [Gamma_mul_Gamma_one_sub, div_mul_cancel₀ _ hs]
  have h := congrArg (fun w : ℂ ↦ ‖w‖) href
  change ‖Gamma z * Gamma (1 - z) * sin ((Real.pi : ℂ) * z)‖ = ‖(Real.pi : ℂ)‖ at h
  rw [hconj, Gamma_conj, norm_mul, norm_mul, norm_conj, hsin, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _), norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h
  simpa only [z, pow_two] using h

private theorem exp_le_norm_Gamma_half_add_mul_I (u : ℝ) :
    Real.exp (-(Real.pi * |u| / 2)) ≤ ‖Gamma (1 / 2 + (u : ℂ) * I)‖ := by
  have hcos : Real.cosh (Real.pi * u) ≤ Real.exp (Real.pi * |u|) := by
    rw [← Real.cosh_abs (Real.pi * u), abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    have h := Real.exp_le_exp.mpr (show -(Real.pi * |u|) ≤ Real.pi * |u| by
      linarith only [mul_nonneg Real.pi_pos.le (abs_nonneg u)])
    linarith only [h]
  have hsq : 1 ≤ ‖Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2 * Real.exp (Real.pi * |u|) :=
    calc
      1 ≤ Real.pi := by linarith only [Real.one_le_pi_div_two]
      _ = ‖Gamma (1 / 2 + (u : ℂ) * I)‖ ^ 2 * Real.cosh (Real.pi * u) :=
        (norm_Gamma_half_add_mul_I_sq_mul_cosh u).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hcos (sq_nonneg _)
  apply (sq_le_sq₀ (Real.exp_pos _).le (norm_nonneg _)).mp
  rw [pow_two, ← Real.exp_add, show -(Real.pi * |u| / 2) + -(Real.pi * |u| / 2) =
    -(Real.pi * |u|) by ring, Real.exp_neg, ← one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr hsq

private theorem Gamma_rightLine_recurrence {z : ℂ} {L : ℝ} (hz : 0 < z.re)
    (hL : 0 ≤ L) (h : L ≤ ‖Gamma z‖) : z.re * L ≤ ‖Gamma (z + 1)‖ := by
  have hz0 : z ≠ 0 := by
    intro he
    rw [he, zero_re] at hz
    exact (lt_irrefl 0) hz
  rw [Gamma_add_one _ hz0, norm_mul]
  exact mul_le_mul (re_le_norm z) h hL (norm_nonneg _)

/-- Both the integer and half-integer progressions at real part at least one
have the same exponential bound, with a factor `1 / 2` for the first
recurrence step starting at `1 / 2`. -/
private theorem exp_le_norm_Gamma_one_add_nat_div_two (u : ℝ) (m : ℕ) :
    Real.exp (-Real.log 2 - Real.pi * |u| / 2) ≤
      ‖Gamma (((1 + (m : ℝ) / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
  induction m using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.cast_zero, zero_div, add_zero, ofReal_one]
    refine (Real.exp_le_exp.mpr ?_).trans (exp_le_norm_Gamma_one_add_mul_I u)
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith only [hlog]
  | one =>
    let z : ℂ := 1 / 2 + (u : ℂ) * I
    have hre : z.re = 1 / 2 := by
      rw [show z = ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I by dsimp [z]; push_cast; rfl]
      simp
    have hz : (((1 + (1 : ℕ) / 2 : ℝ) : ℂ) + (u : ℂ) * I) = z + 1 := by
      simp only [z, Nat.cast_one]
      push_cast
      ring
    rw [hz, sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ← one_div, ← hre]
    exact Gamma_rightLine_recurrence (by rw [hre]; norm_num) (Real.exp_pos _).le
      (exp_le_norm_Gamma_half_add_mul_I u)
  | more m ih _ =>
    let z : ℂ := ((1 + (m : ℝ) / 2 : ℝ) : ℂ) + (u : ℂ) * I
    have hre : z.re = 1 + (m : ℝ) / 2 := by simp [z]
    have h1 : 1 ≤ z.re := by
      rw [hre]
      exact le_add_of_nonneg_right (by positivity)
    have hz : (((1 + ((m + 2 : ℕ) : ℝ) / 2 : ℝ) : ℂ) + (u : ℂ) * I) = z + 1 := by
      dsimp [z]
      push_cast
      ring
    rw [hz]
    exact (le_mul_of_one_le_left (Real.exp_pos _).le h1).trans
      (Gamma_rightLine_recurrence (zero_lt_one.trans_le h1) (Real.exp_pos _).le ih)

private theorem exp_le_norm_Gamma_two_add_mul_I (t : ℝ) :
    Real.exp (-(Real.pi * |t| / 2)) ≤ ‖Gamma (2 + (t : ℂ) * I)‖ := by
  have hre : (1 + (t : ℂ) * I).re = 1 := by simp
  have hnorm : 1 ≤ ‖1 + (t : ℂ) * I‖ := hre ▸ re_le_norm _
  have hz : 1 + (t : ℂ) * I ≠ 0 := by
    intro h
    rw [h, zero_re] at hre
    exact zero_ne_one hre
  rw [show (2 : ℂ) + (t : ℂ) * I = (1 + (t : ℂ) * I) + 1 by ring,
    Gamma_add_one _ hz, norm_mul]
  exact (exp_le_norm_Gamma_one_add_mul_I t).trans
    (le_mul_of_one_le_left (norm_nonneg _) hnorm)

private theorem norm_ofReal_cpow_neg {B : ℝ} (hB : 0 < B) (z : ℂ) :
    ‖(B : ℂ) ^ (-z)‖ = Real.exp (-Real.log B * z.re) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hB.ne'), ← ofReal_log hB.le, Complex.norm_exp]
  simp [mul_re]

/-- The real factor on `Re s = 2` retains its prefactor `1 / π` and has
an exponential lower bound of rate `π / 4` in `|t|`. -/
public theorem norm_archimedeanGammaFactor_real_rightLine_lower_bound (t : ℝ) :
    Real.exp (-(Real.log Real.pi) - Real.pi * |t| / 4) ≤
      ‖archimedeanGammaFactor Real.pi 2 0 0 (2 + (t : ℂ) * I)‖ := by
  rw [archimedeanGammaFactor_real]
  simp only [ofReal_zero, zero_mul, add_zero]
  rw [Gammaℝ_def, neg_div, norm_mul, norm_ofReal_cpow_neg Real.pi_pos,
    show ((2 : ℂ) + (t : ℂ) * I) / 2 = 1 + ((t / 2 : ℝ) : ℂ) * I by push_cast; ring]
  have hre : (1 + ((t / 2 : ℝ) : ℂ) * I).re = 1 := by simp
  rw [hre, mul_one]
  calc
    _ = Real.exp (-Real.log Real.pi) * Real.exp (-(Real.pi * |t / 2| / 2)) := by
      rw [← Real.exp_add, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_norm_Gamma_one_add_mul_I (t / 2))
      (Real.exp_pos _).le

/-- The complex factor on `Re s = 2` retains its prefactor `1 / (2π)^2`
(without Deligne's extra factor of `2`) and has an exponential lower bound
of rate `π / 2` in `|t|`. -/
public theorem norm_archimedeanGammaFactor_complex_rightLine_lower_bound (t : ℝ) :
    Real.exp (-(2 * Real.log (2 * Real.pi)) - Real.pi * |t| / 2) ≤
      ‖archimedeanGammaFactor (2 * Real.pi) 1 0 0 (2 + (t : ℂ) * I)‖ := by
  have hB : 0 < 2 * Real.pi := by positivity
  rw [archimedeanGammaFactor_complex]
  simp only [ofReal_zero, zero_mul, add_zero]
  rw [Gammaℂ_def, mul_assoc, mul_div_cancel_left₀ _ (by norm_num), norm_mul,
    show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    norm_ofReal_cpow_neg hB]
  have hre : (2 + (t : ℂ) * I).re = 2 := by simp
  rw [hre]
  calc
    _ = Real.exp (-Real.log (2 * Real.pi) * 2) * Real.exp (-(Real.pi * |t| / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_norm_Gamma_two_add_mul_I t) (Real.exp_pos _).le

/-- A single positive rate bounds the normalized real factor everywhere on `Re s = 2`. -/
public theorem exp_le_norm_archimedeanGammaFactor_real_rightLine (t : ℝ) :
    Real.exp (-(Real.log Real.pi + Real.pi / 4) * (1 + |t|)) ≤
      ‖archimedeanGammaFactor Real.pi 2 0 0 (2 + (t : ℂ) * I)‖ := by
  refine le_trans (Real.exp_le_exp.mpr ?_) (norm_archimedeanGammaFactor_real_rightLine_lower_bound t)
  have hlog : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.one_le_pi_div_two])
  nlinarith only [Real.pi_pos, mul_nonneg hlog (abs_nonneg t)]

/-- A single positive rate bounds the normalized complex factor everywhere on `Re s = 2`. -/
public theorem exp_le_norm_archimedeanGammaFactor_complex_rightLine (t : ℝ) :
    Real.exp (-(2 * Real.log (2 * Real.pi) + Real.pi / 2) * (1 + |t|)) ≤
      ‖archimedeanGammaFactor (2 * Real.pi) 1 0 0 (2 + (t : ℂ) * I)‖ := by
  refine le_trans (Real.exp_le_exp.mpr ?_)
    (norm_archimedeanGammaFactor_complex_rightLine_lower_bound t)
  have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.one_le_pi_div_two])
  nlinarith only [Real.pi_pos, mul_nonneg hlog (abs_nonneg t)]

private theorem exists_cpow_mul_Gamma_rightLine_lower_bound {B d : ℝ} (hB : 0 < B)
    (τ : ℝ) (hd : 0 < d) (m : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      let z : ℂ := ((1 + (m : ℝ) / 2 : ℝ) : ℂ) + (((t + τ) / d : ℝ) : ℂ) * I
      Real.exp (-A * (1 + |t|)) ≤ ‖(B : ℂ) ^ (-z) * Gamma z‖ := by
  let x : ℝ := 1 + (m : ℝ) / 2
  let c : ℝ := Real.log B * x + Real.log 2
  let a : ℝ := Real.pi / (2 * d)
  have ha : 0 < a := div_pos Real.pi_pos (mul_pos two_pos hd)
  refine ⟨|c| + a * (1 + |τ|), by positivity, fun t ↦ ?_⟩
  let u : ℝ := (t + τ) / d
  let z : ℂ := (x : ℂ) + (u : ℂ) * I
  change _ ≤ ‖(B : ℂ) ^ (-z) * Gamma z‖
  rw [norm_mul, norm_ofReal_cpow_neg hB, show z.re = x by simp [z]]
  have hu : Real.pi * |u| / 2 = a * |t + τ| := by
    dsimp [u, a]
    rw [abs_div, abs_of_pos hd]
    ring
  have hloss : c + a * |t + τ| ≤ (|c| + a * (1 + |τ|)) * (1 + |t|) :=
    calc
      _ ≤ c + a * (|t| + |τ|) :=
        add_le_add_right (mul_le_mul_of_nonneg_left (abs_add_le t τ) ha.le) _
      _ ≤ _ := by
        nlinarith only [le_abs_self c, ha, mul_nonneg (abs_nonneg c) (abs_nonneg t),
          mul_nonneg (mul_nonneg ha.le (abs_nonneg τ)) (abs_nonneg t)]
  calc
    _ ≤ Real.exp (-(c + a * |t + τ|)) := Real.exp_le_exp.mpr (by linarith only [hloss])
    _ = Real.exp (-Real.log B * x) * Real.exp (-Real.log 2 - Real.pi * |u| / 2) := by
      rw [← Real.exp_add, hu]
      congr 1
      dsimp [c]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_norm_Gamma_one_add_nat_div_two u m)
      (Real.exp_pos _).le

/-- The normalized real factor, including the power of `π`, is bounded
below exponentially for both parities and any fixed frequency. -/
public theorem exists_archimedeanGammaFactor_real_rightLine_lower_bound (b : ℕ) (τ : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Real.exp (-A * (1 + |t|)) ≤
      ‖archimedeanGammaFactor Real.pi 2 (b : ℝ) τ (2 + (t : ℂ) * I)‖ := by
  obtain ⟨A, hA, h⟩ := exists_cpow_mul_Gamma_rightLine_lower_bound Real.pi_pos τ two_pos b
  refine ⟨A, hA, fun t ↦ ?_⟩
  rw [archimedeanGammaFactor_real]
  dsimp only
  rw [Gammaℝ_def, neg_div,
    show (2 + (t : ℂ) * I + ((b : ℝ) : ℂ) + (τ : ℂ) * I) / 2 =
      ((1 + (b : ℝ) / 2 : ℝ) : ℂ) + (((t + τ) / 2 : ℝ) : ℂ) * I by push_cast; ring]
  exact h t

/-- The normalized complex factor includes the power of `2π` and no extra
factor of `2`. Its exponential lower bound allows every angular weight. -/
public theorem exists_archimedeanGammaFactor_complex_rightLine_lower_bound (n : ℤ) (τ : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, Real.exp (-A * (1 + |t|)) ≤
      ‖archimedeanGammaFactor (2 * Real.pi) 1 ((n.natAbs : ℝ) / 2) τ (2 + (t : ℂ) * I)‖ := by
  have hB : 0 < 2 * Real.pi := by positivity
  obtain ⟨A, hA, h⟩ := exists_cpow_mul_Gamma_rightLine_lower_bound hB τ one_pos (n.natAbs + 2)
  refine ⟨A, hA, fun t ↦ ?_⟩
  rw [archimedeanGammaFactor_complex]
  dsimp only
  rw [Gammaℂ_def, mul_assoc, mul_div_cancel_left₀ _ (by norm_num),
    show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    show 2 + (t : ℂ) * I + (((n.natAbs : ℝ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I =
      ((1 + ((n.natAbs + 2 : ℕ) : ℝ) / 2 : ℝ) : ℂ) + (((t + τ) / 1 : ℝ) : ℂ) * I by
      push_cast
      ring]
  exact h t

end Masullo
