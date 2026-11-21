module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Exponential

/-! # The causal exponential vector for a single half-plane zero -/

open scoped ComplexConjugate

namespace Masullo

/-- The normalized causal exponential for a half-plane zero at distance
`a.re > 0` from the boundary, in unweighted log coordinates. -/
public noncomputable def halfLineMellinVector (a : ℂ) (x : ℝ) : ℂ :=
  if 0 ≤ x then (Real.sqrt (2 * a.re) : ℂ) * Complex.exp (-conj a * x) else 0

/-- A causal vector vanishes strictly before its support edge. -/
public theorem halfLineMellinVector_eq_zero_of_neg (a : ℂ) {x : ℝ} (hx : x < 0) :
    halfLineMellinVector a x = 0 := by
  rw [halfLineMellinVector, ite_eq_right (not_le.mpr hx)]

/-- The overlap integrand on the common causal support of the two vectors. -/
public theorem halfLineMellinVector_shift_mul_conj {a : ℂ} (ha : 0 < a.re)
    {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    halfLineMellinVector a (x - y) * conj (halfLineMellinVector a x) =
      Complex.exp (-a * y) * ((↑(2 * a.re) : ℂ) *
        Complex.exp (-(↑(2 * a.re) : ℂ) * ↑(x - y))) := by
  rw [halfLineMellinVector, ite_eq_left (sub_nonneg.mpr hyx), halfLineMellinVector,
    ite_eq_left (hy.trans hyx)]
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_conj]
  have hsq : (↑(Real.sqrt (2 * a.re)) : ℂ) * ↑(Real.sqrt (2 * a.re)) = ↑(2 * a.re) := by
    exact_mod_cast (Real.mul_self_sqrt (show 0 ≤ 2 * a.re by positivity))
  calc
    _ = ((↑(Real.sqrt (2 * a.re)) : ℂ) * ↑(Real.sqrt (2 * a.re))) *
        (Complex.exp (-conj a * ↑(x - y)) * Complex.exp (-a * ↑x)) := by ring
    _ = _ := by
      rw [hsq, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
      congr 2
      rw [← Complex.add_conj a, Complex.ofReal_sub]
      ring

end Masullo
