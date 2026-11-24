module

public import Props.ArchimedeanGammaLogDerivative
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Lemmas.ArchimedeanGammaDomination

/-!
# The real Gamma factor on the right half-plane

The rational trivial character uses `Gammaℝ(s) = π^(-s/2) Γ(s/2)`,
the even real factor in (3.2.1.4), p. 123. Its scalar log derivative
in (B.4.2.12)–(16), pp. 615–616, is the unshifted case of the
subtracted Archimedean Gauss integral.
-/

open Complex MeasureTheory Set

namespace Masullo

/-- The real factor in the rational contour, before integration against a
Mellin test. The `π^(-s/2)` prefactor contributes `-log π / 2`. -/
public theorem logDeriv_GammaReal_eq_integral {s : ℂ} (hs : 0 < s.re) :
    let K := fun x : ℝ ↦ (exp (-2 * (x : ℂ)) - exp (-s * (x : ℂ))) /
      (1 - exp (-2 * (x : ℂ)))
    IntegrableOn K (Ioi 0) ∧
    logDeriv Gammaℝ s = -((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 +
      ∫ x in Ioi (0 : ℝ), K x := by
  have hfactor : archimedeanGammaFactor Real.pi 2 0 0 = Gammaℝ := by
    simpa only [ofReal_zero, zero_mul, add_zero] using archimedeanGammaFactor_real 0 0
  have h := (logDeriv_archimedeanGammaFactor_eq_integral (B := Real.pi) (d := 2) (b := 0) (τ := 0)
    two_pos le_rfl hs).2
  simpa only [hfactor, ofReal_zero, add_zero, zero_mul, ofReal_ofNat] using h

private theorem norm_gammaRealKernel_le_inv {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re)
    {x : ℝ} (hx : 0 < x) :
    ‖archimedeanGammaKernel 2 s x‖ ≤ (2 / x) * ((1 / 2 + x) * Real.exp (-(1 / 2) * x)) := by
  let A := Real.exp (-(1 / 2) * x)
  let B := Real.exp (-(2 : ℝ) * x)
  have hB : 0 < 1 - B := by
    change 0 < 1 - Real.exp (-(2 : ℝ) * x)
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hd : x ≤ (1 / 2 + x) * (1 - B) := by
    have h := Real.add_one_le_exp (2 * x)
    have he : (2 * x + 1) * B ≤ 1 := by
      dsimp [B]
      rw [show -(2 : ℝ) * x = -(2 * x) by ring, Real.exp_neg,
        mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
      exact h
    nlinarith
  have hB' : B ≤ A := by
    change Real.exp (-(2 : ℝ) * x) ≤ Real.exp (-(1 / 2) * x)
    exact Real.exp_le_exp.mpr (by linarith)
  have hnum : ‖exp (-s * (x : ℂ))‖ ≤ A := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right (neg_le_neg hs) hx.le
  have hexp : exp (-(2 : ℂ) * (x : ℂ)) = (B : ℂ) := by
    simp [B, ofReal_exp]
  rw [archimedeanGammaKernel, ofReal_ofNat, hexp, norm_div, ← ofReal_one,
    ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos hB]
  apply (div_le_iff₀ hB).mpr
  calc
    _ ≤ 2 * A := (norm_sub_le _ _).trans (by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      linarith)
    _ ≤ ((2 / x) * ((1 / 2 + x) * A)) * (1 - B) := by
      have hEq : ((2 / x) * ((1 / 2 + x) * A)) * (1 - B) =
          (2 * A * ((1 / 2 + x) * (1 - B))) / x := by ring
      rw [hEq]
      exact (le_div_iff₀ hx).mpr (mul_le_mul_of_nonneg_left hd (by dsimp [A]; positivity))

/-- A sublinear bound uniform over the closed right half-plane `Re s ≥ 1/2`.
Interpolate the first-moment estimate and the undifferenced numerator bound
before integrating the subtracted Gauss kernel. -/
public theorem exists_norm_logDeriv_GammaReal_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re →
      ‖logDeriv Gammaℝ s‖ ≤ C * Real.sqrt (2 + |s.re| + |s.im|) := by
  let J (x : ℝ) := (1 / 2 * x ^ (-1 / 2 : ℝ) + x ^ (1 / 2 : ℝ)) * Real.exp (-(1 / 2) * x)
  have hJi : IntegrableOn J (Ioi 0) := by
    have h (p : ℝ) (hp : -1 < p) : IntegrableOn (fun x : ℝ ↦ x ^ p * Real.exp (-(1 / 2) * x)) (Ioi 0) := by
      simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := p) hp one_pos
        (by norm_num : (0 : ℝ) < 1 / 2))
    exact (((h _ (by norm_num : (-1 : ℝ) < -1 / 2)).const_mul (1 / 2)).add
      (h _ (by norm_num : (-1 : ℝ) < 1 / 2))).congr
      (Filter.Eventually.of_forall fun x ↦ by dsimp [J]; ring)
  let j := ∫ x in Ioi (0 : ℝ), J x
  have hj : 0 ≤ j := setIntegral_nonneg measurableSet_Ioi fun x hx ↦ by
    have hx' : 0 < x := hx
    dsimp [J]; positivity
  let c : ℂ := -((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2
  refine ⟨‖c‖ + Real.sqrt 2 * j + 1, by positivity, fun s hs ↦ ?_⟩
  let X := 2 + |s.re| + |s.im|
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg s.re, abs_nonneg s.im]
  let K := archimedeanGammaKernel 2 s
  have hval : logDeriv Gammaℝ s = c + ∫ x in Ioi (0 : ℝ), K x := by
    simpa [c, K, archimedeanGammaKernel] using
      (logDeriv_GammaReal_eq_integral ((by norm_num : (0 : ℝ) < 1 / 2).trans_le hs)).2
  have hdom (x : ℝ) (hx : 0 < x) : ‖K x‖ ≤ (Real.sqrt 2 * Real.sqrt X) * J x := by
    let E := (1 / 2 + x) * Real.exp (-(1 / 2) * x)
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have h₁ : ‖K x‖ ≤ X * E := by
      have h := norm_archimedeanGammaKernel_le (u := s.re) (v := s.im) two_pos hx
      rw [Complex.re_add_im] at h
      refine h.trans ?_
      have hX' : |2 - s.re| + |s.im| ≤ X := by
        have h := abs_sub (2 : ℝ) s.re
        norm_num at h
        dsimp [X]
        linarith
      have hm : 1 / 2 ≤ min 2 s.re := le_min (by norm_num) hs
      dsimp [E]
      gcongr
    have h₂ := norm_gammaRealKernel_le_inv hs hx
    change ‖K x‖ ≤ (2 / x) * E at h₂
    have hEE : Real.sqrt (E * E) = E := Real.sqrt_mul_self hE
    calc
      ‖K x‖ = Real.sqrt (‖K x‖ * ‖K x‖) := (Real.sqrt_mul_self (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((2 / x * X) * (E * E)) := by
        apply Real.sqrt_le_sqrt
        rw [show 2 / x * X * (E * E) = (X * E) * (2 / x * E) by ring]
        exact mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
      _ = (Real.sqrt 2 * Real.sqrt X) * J x := by
        rw [Real.sqrt_mul (show 0 ≤ 2 / x * X by positivity), hEE,
          Real.sqrt_mul (show 0 ≤ 2 / x by positivity), Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
        have hxpow : 1 / Real.sqrt x = x ^ (-1 / 2 : ℝ) := by
          rw [one_div, Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx.le]
        have hxmul : x * x ^ (-1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
          calc
            _ = x ^ (1 : ℝ) * x ^ (-1 / 2 : ℝ) := by rw [Real.rpow_one]
            _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hx]; norm_num
        rw [div_eq_mul_inv, ← one_div (Real.sqrt x), hxpow]
        dsimp [E, J]
        linear_combination (Real.sqrt 2 * Real.sqrt X * Real.exp (-(1 / 2) * x)) * hxmul
  have hI : ‖∫ x in Ioi (0 : ℝ), K x‖ ≤ (Real.sqrt 2 * Real.sqrt X) * j := by
    simpa only [integral_const_mul] using
      (norm_integral_le_of_norm_le (f := K) (hJi.const_mul (Real.sqrt 2 * Real.sqrt X)) (by
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
        exact hdom x hx))
  rw [hval]
  calc
    _ ≤ ‖c‖ + (Real.sqrt 2 * Real.sqrt X) * j := (norm_add_le _ _).trans (by gcongr)
    _ ≤ (‖c‖ + Real.sqrt 2 * j + 1) * Real.sqrt X := by
      have hsqrt := Real.sqrt_le_sqrt hX
      rw [Real.sqrt_one] at hsqrt
      nlinarith [mul_nonneg (norm_nonneg c) (sub_nonneg.mpr hsqrt)]

end Masullo
