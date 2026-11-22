module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Lemmas.DigammaIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.LinearCombination

/-! Exponential coordinates for the absolutely integrable Gauss difference. -/

open Complex MeasureTheory Set

namespace Masullo

/-- Write the Gauss integral in log coordinates using `t = exp (-d * x)`. -/
public theorem digamma_sub_one_eq_exponential_integral {w : ℂ} {d : ℝ}
    (hd : 0 < d) (hw : 0 < (w / (d : ℂ)).re) :
    let K := fun x : ℝ ↦ (exp (-(d : ℂ) * (x : ℂ)) - exp (-w * (x : ℂ))) /
      (1 - exp (-(d : ℂ) * (x : ℂ)))
    IntegrableOn K (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), K x) = (digamma (w / (d : ℂ)) - digamma 1) / (d : ℂ) := by
  let K (x : ℝ) := (exp (-(d : ℂ) * (x : ℂ)) - exp (-w * (x : ℂ))) /
    (1 - exp (-(d : ℂ) * (x : ℂ)))
  let Q (t : ℝ) := ((t : ℂ) ^ (w / (d : ℂ) - 1) - 1) / (1 - (t : ℂ))
  obtain ⟨hQ, hval⟩ := digamma_one_sub_eq_integral hw
  change IntegrableOn Q (Ioo 0 1) at hQ
  change (∫ t in Ioo (0 : ℝ) 1, Q t) = _ at hval
  have hd₀ : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  let f (x : ℝ) := Real.exp (-d * x)
  let f' (x : ℝ) := -d * f x
  have hder (x : ℝ) (_ : x ∈ Ioi (0 : ℝ)) : HasDerivWithinAt f (f' x) (Ioi 0) x := by
    simpa only [f, f', mul_comm, id_eq, one_mul, mul_one] using
      ((hasDerivAt_id x).const_mul (-d)).exp.hasDerivWithinAt (s := Ioi 0)
  have hinj : InjOn f (Ioi (0 : ℝ)) := by
    intro x _ y _ h
    exact mul_left_cancel₀ (neg_ne_zero.mpr hd.ne') (Real.exp_injective h)
  have himage : f '' Ioi 0 = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hd) hx)⟩
    · intro ht
      refine ⟨-Real.log t / d, div_pos (neg_pos.mpr (Real.log_neg ht.1 ht.2)) hd, ?_⟩
      change Real.exp (-d * (-Real.log t / d)) = t
      rw [show -d * (-Real.log t / d) = Real.log t by field_simp, Real.exp_log ht.1]
  have hchange : EqOn (fun x ↦ |f' x| • Q (f x)) (fun x ↦ (-(d : ℂ)) * K x) (Ioi 0) := by
    intro x _
    have hf : 0 < f x := Real.exp_pos _
    have habs : |f' x| = d * f x := by
      rw [show f' x = -(d * f x) by simp [f'], abs_neg, abs_of_nonneg (mul_pos hd hf).le]
    have hcast : (f x : ℂ) = exp (-(d : ℂ) * (x : ℂ)) := by
      simp only [f, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
    have hlog : log (f x : ℂ) = -(d : ℂ) * (x : ℂ) := by
      rw [← Complex.ofReal_log hf.le, show Real.log (f x) = -d * x from Real.log_exp _]
      push_cast; rfl
    have hpow : (f x : ℂ) ^ (w / (d : ℂ) - 1) =
        exp ((-(d : ℂ) * (x : ℂ)) * (w / (d : ℂ) - 1)) := by
      rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hf.ne'), hlog]
    simp only [habs, Complex.real_smul, Complex.ofReal_mul, Q, K]
    rw [hpow, hcast, show -w * (x : ℂ) =
      (-(d : ℂ) * (x : ℂ)) + (-(d : ℂ) * (x : ℂ)) * (w / (d : ℂ) - 1) by
        field_simp; ring, Complex.exp_add]
    ring
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj Q).mp
    (himage.symm ▸ hQ)
  have hKi : IntegrableOn K (Ioi 0) := by
    have hscaled := (integrableOn_congr_fun hchange measurableSet_Ioi).mp hi
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hd₀), one_mul]
      using hscaled.const_mul ((-(d : ℂ))⁻¹)
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj Q
  rw [himage, hval, setIntegral_congr_fun measurableSet_Ioi hchange, integral_const_mul] at heq
  refine ⟨hKi, (eq_div_iff hd₀).mpr ?_⟩
  change (∫ x in Ioi (0 : ℝ), K x) * (d : ℂ) = _
  linear_combination heq

end Masullo
