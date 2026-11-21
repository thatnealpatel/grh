module

public import Lemmas.RationalThetaMellin
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Rational theta Mellin unfolding

This is the nonzero-integer lattice model of the absolutely convergent
norm-section unfolding in Masullo's Theorem 3.2.2.1(2)–(3), pp. 124–125,
and (3.2.2.11), p. 127. The archimedean factor integrates both real rays
against `dt/|t|`, written in logarithmic coordinates. The finite Euler factors in
this model are expressed by the Riemann zeta Dirichlet series. The theorem
neither proves adelic unfolding nor continues the identity to the strip.
-/

open MeasureTheory
open scoped SchwartzMap

namespace Masullo

/-- For arbitrary complex Schwartz input, the rational theta Mellin integral is
absolutely convergent on `1 < z.re` and factors into zeta and the Mellin integral
of the two real rays. No moment or parity assumptions are needed here. -/
public theorem rationalTheta_mellin_eq_zeta_mul (b : 𝓢(ℝ, ℂ)) {z : ℂ} (hz : 1 < z.re) :
    Integrable (fun x : ℝ ↦ rationalTheta b (Real.exp x) * Complex.exp (z * x)) ∧
    (∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)) =
      riemannZeta z * (∫ x : ℝ, rationalMellinIntegrand b z x) := by
  obtain ⟨hint, hsum⟩ := rationalTheta_mellin_hasSum b hz
  refine ⟨hint, ?_⟩
  rw [← hsum.tsum_eq, tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow hz]

end Masullo
