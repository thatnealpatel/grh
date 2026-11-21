module

public import Theorems.RationalThetaInversion
public import Lemmas.HardySobolevWeight

/-!
# Weighted square integrability of rational theta

This verifies finiteness of the real-lattice counterpart of the squared
norm in Masullo's (10.1.1.6), p. 435, with the real-line weight from
(9.2.2.4), p. 412. The reduction from the adelic norm to the log-norm
line and the adelic completion are not constructed here.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

/-- The two-moment theta function has finite squared Hardy–Sobolev norm on
any compact real strip `[α, β]`, including a singleton, after multiplication
by `exp(a*x)`, in the rational lattice model. The symmetric endpoint weight
also makes sense without ordering `α` and `β`. -/
public theorem integrable_rationalTheta_hardySobolev (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) (a α β s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun x : ℝ ↦ ‖rationalTheta b (Real.exp x)‖ ^ 2 *
      max (Real.exp (2 * (a + α) * x)) (Real.exp (2 * (a + β) * x)) *
      (1 + x ^ 2) ^ (s / 2)) := by
  have htheta : Continuous (fun x : ℝ ↦ rationalTheta b (Real.exp x)) :=
    (rationalTheta_continuousOn b).comp_continuous Real.continuous_exp Real.exp_pos
  obtain ⟨N, hN⟩ := exists_nat_ge (max |a + α| |a + β| + s / 2 + 1)
  obtain ⟨C, _, htail⟩ := rationalTheta_uniform_log_bound
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) b) N
  exact integrable_hardySobolevWeight_mul_norm_sq htheta hs (by linarith)
    (htail b (Set.mem_singleton b) hb hFourier)

end Masullo
