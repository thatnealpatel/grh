module

public import Lemmas.CompactLogMellin
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv

/-! # Applying a real polynomial in the log derivative -/

open MeasureTheory
open scoped BigOperators ContDiff

namespace Masullo

/-- The polynomial differential operator on a real log profile. -/
@[expose] public noncomputable def logPolynomialDeriv (P : Polynomial ℝ) (f : ℝ → ℝ)
    (x : ℝ) : ℝ := ∑ n ∈ P.support, P.coeff n * iteratedDeriv n f x

private theorem contDiff_iteratedDeriv_real {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hf

private theorem tsupport_iteratedDeriv_real_subset (f : ℝ → ℝ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- Differentiating and taking the polynomial combination do not enlarge the support. -/
public theorem logPolynomialDeriv_smooth_supported (P : Polynomial ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (logPolynomialDeriv P f) ∧ tsupport (logPolynomialDeriv P f) ⊆ tsupport f := by
  constructor
  · exact ContDiff.sum fun n _ ↦ contDiff_const.mul (contDiff_iteratedDeriv_real hf n)
  · apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra h
    apply hx
    exact Finset.sum_eq_zero fun n _ ↦ mul_eq_zero_of_right _
      (image_eq_zero_of_notMem_tsupport fun hn ↦ h (tsupport_iteratedDeriv_real_subset f n hn))

private theorem iteratedDeriv_ofReal_log {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    (fun x ↦ Complex.ofReal (iteratedDeriv n f x)) =
      iteratedDeriv n (fun x ↦ Complex.ofReal (f x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ← ih]
    ext x
    exact (((contDiff_iteratedDeriv_real hf n).differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv.symm

/-- Applying `P` to the log derivative multiplies the Mellin transform by `P(-z)`.
The monomial case is the whole-line integration by parts of (B.2.1.31). -/
public theorem compactLogMellin_logPolynomialDeriv (P : Polynomial ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (z : ℂ) :
    compactLogMellin (fun x ↦ (logPolynomialDeriv P f x : ℂ)) z =
      P.eval₂ Complex.ofRealHom (-z) * compactLogMellin (fun x ↦ (f x : ℂ)) z := by
  let g : ℝ → ℂ := fun x ↦ (f x : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hf
  have hgc : HasCompactSupport g := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    exact closure_mono fun x hx ↦ fun h ↦ hx (by simp [g, h])
  let E (x : ℝ) := Complex.exp (z * (x : ℂ))
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hInt (n : ℕ) : Integrable (fun x ↦ (P.coeff n : ℂ) * (iteratedDeriv n g x * E x)) := by
    have hd : Continuous (iteratedDeriv n g) := hg.continuous_iteratedDeriv n (by simp)
    exact ((hd.mul hE).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv_logProfile hgc n).mul_right).const_mul _
  trans ∫ x, ∑ n ∈ P.support, (P.coeff n : ℂ) * (iteratedDeriv n g x * E x)
  · apply integral_congr_ae
    filter_upwards with x
    simp only [logPolynomialDeriv, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [congrFun (iteratedDeriv_ofReal_log hf n) x]
  · rw [integral_finsetSum _ (fun n _ ↦ hInt n), Polynomial.eval₂_eq_sum,
      Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_const_mul]
    change (P.coeff n : ℂ) * compactLogMellin (iteratedDeriv n g) z =
      ((P.coeff n : ℂ) * (-z) ^ n) * compactLogMellin g z
    rw [compactLogMellin_iteratedDeriv hg hgc, mul_assoc]

end Masullo
