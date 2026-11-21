module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Lemmas.DigammaIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.Ring

/-!
# The real Gamma factor on the right half-plane

The rational trivial character uses `Gammaℝ(s) = π^(-s/2) Γ(s/2)`.
In (B.4.2.12)–(B.4.2.16), pp. 615–616, Masullo reduces the real
term to a digamma calculation and invokes Barner. The integral below
keeps the subtraction at zero, and differentiates the actual prefactor
rather than assigning a sign to the extracted constant in (B.4.2.12).
-/

open Complex MeasureTheory Set

namespace Masullo

private theorem logDeriv_GammaReal_eq_digamma {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s = (digamma (s / 2) - (Real.log Real.pi : ℂ)) / 2 := by
  let a : ℂ := Real.pi
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have haLog : log a = (Real.log Real.pi : ℂ) := (Complex.ofReal_log Real.pi_pos.le).symm
  have hs2 : 0 < (s / 2).re := by simpa [Complex.div_ofNat_re] using half_pos hs
  have harg : HasDerivAt (fun w : ℂ ↦ w / 2) (1 / 2) s := (hasDerivAt_id s).div_const 2
  have hexp : HasDerivAt (fun w : ℂ ↦ exp (log a * (-w / 2)))
      (exp (log a * (-s / 2)) * (log a * (-1 / 2))) s :=
    (((hasDerivAt_id s).neg.div_const 2).const_mul (log a)).cexp
  have hGamma := (hasDerivAt_Gamma_of_re_pos hs2).differentiableAt
  rw [show Gammaℝ = fun w ↦ exp (log a * (-w / 2)) * Gamma (w / 2) by
    funext w; rw [Gammaℝ_def, cpow_def_of_ne_zero ha]]
  rw [logDeriv_fun_mul (f := fun w ↦ exp (log a * (-w / 2)))
    (g := fun w ↦ Gamma (w / 2)) s (exp_ne_zero _) (Gamma_ne_zero_of_re_pos hs2)
    hexp.differentiableAt (hGamma.comp s harg.differentiableAt),
    logDeriv_fun_comp (f := Gamma) (g := fun w ↦ w / 2) hGamma harg.differentiableAt,
    harg.deriv, ← digamma_def, logDeriv_apply, hexp.deriv,
    mul_div_cancel_left₀ _ (exp_ne_zero _), haLog]
  ring

/-- The real factor in the rational contour, before integration against a
Mellin test. Barner supplies the Gauss-integral route to (B.4.2.15).
`digamma_one_sub_eq_integral` supplies the absolutely integrable difference
used here. The `π^(-s/2)` prefactor contributes `-log π / 2`. -/
public theorem logDeriv_GammaReal_eq_integral {s : ℂ} (hs : 0 < s.re) :
    let K := fun x : ℝ ↦ (exp (-2 * (x : ℂ)) - exp (-s * (x : ℂ))) /
      (1 - exp (-2 * (x : ℂ)))
    IntegrableOn K (Ioi 0) ∧
    logDeriv Gammaℝ s = -((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 +
      ∫ x in Ioi (0 : ℝ), K x := by
  let K (x : ℝ) := (exp (-2 * (x : ℂ)) - exp (-s * (x : ℂ))) / (1 - exp (-2 * (x : ℂ)))
  let Q (t : ℝ) := ((t : ℂ) ^ (s / 2 - 1) - 1) / (1 - (t : ℂ))
  have hs2 : 0 < (s / 2).re := by simpa [Complex.div_ofNat_re] using half_pos hs
  obtain ⟨hQ, hval⟩ := digamma_one_sub_eq_integral hs2
  change IntegrableOn Q (Ioo 0 1) at hQ
  change (∫ t in Ioo (0 : ℝ) 1, Q t) = _ at hval
  let f (x : ℝ) := Real.exp (-2 * x)
  let f' (x : ℝ) := -2 * f x
  have hder (x : ℝ) (_ : x ∈ Ioi (0 : ℝ)) : HasDerivWithinAt f (f' x) (Ioi 0) x := by
    simpa only [f, f', mul_comm, id_eq, one_mul, mul_one] using
      ((hasDerivAt_id x).const_mul (-2)).exp.hasDerivWithinAt (s := Ioi 0)
  have hinj : InjOn f (Ioi (0 : ℝ)) := by
    intro x _ y _ h
    have hh := Real.exp_injective h
    linarith
  have himage : f '' Ioi 0 = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by simpa using neg_neg_of_pos hx)⟩
    · intro ht
      refine ⟨-Real.log t / 2, ?_, ?_⟩
      · exact div_pos (neg_pos.mpr (Real.log_neg ht.1 ht.2)) two_pos
      · change Real.exp (-2 * (-Real.log t / 2)) = t
        rw [show -2 * (-Real.log t / 2) = Real.log t by ring, Real.exp_log ht.1]
  have hchange : EqOn (fun x ↦ |f' x| • Q (f x)) (fun x ↦ (-2 : ℂ) * K x) (Ioi 0) := by
    intro x _
    have hf : 0 < f x := Real.exp_pos _
    have habs : |f' x| = 2 * f x := by
      rw [show f' x = -(2 * f x) by ring, abs_neg, abs_of_nonneg (by positivity)]
    have hcast : (f x : ℂ) = exp (-2 * (x : ℂ)) := by simp [f, Complex.ofReal_exp]
    have hlog : log (f x : ℂ) = -2 * (x : ℂ) := by
      rw [← Complex.ofReal_log hf.le, show Real.log (f x) = -2 * x from Real.log_exp _]
      push_cast
      rfl
    have hpow : (f x : ℂ) ^ (s / 2 - 1) = exp ((-2 * (x : ℂ)) * (s / 2 - 1)) := by
      rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hf.ne'), hlog]
    simp only [habs, Complex.real_smul, Complex.ofReal_mul, Q, K]
    rw [hpow, hcast]
    rw [show -s * (x : ℂ) = (-2 * (x : ℂ)) + (-2 * (x : ℂ)) * (s / 2 - 1) by ring,
      Complex.exp_add, Complex.ofReal_ofNat]
    ring
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj Q).mp
    (himage.symm ▸ hQ)
  have hKi : IntegrableOn K (Ioi 0) := by
    have htwo := (integrableOn_congr_fun hchange measurableSet_Ioi).mp hi
    have hinv := htwo.const_mul ((-2 : ℂ)⁻¹)
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0), one_mul]
      using hinv
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj Q
  rw [himage, hval, setIntegral_congr_fun measurableSet_Ioi hchange, integral_const_mul] at heq
  refine ⟨hKi, ?_⟩
  rw [logDeriv_GammaReal_eq_digamma hs, digamma_one] at *
  linear_combination -heq / 2

end Masullo
