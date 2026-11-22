module

public import Theorems.RationalAdeleSameSignTheta
public import Theorems.RationalIdeleHaarComparison
import Mathlib.MeasureTheory.Group.Integral

/-! # Mellin pairing of the two rational Fourier conventions

The finite frequency reflection changes the same-sign pairing in (3.2.2.2),
p. 124, by the value of the paired character at the finite-sign idele.
This is a change of variables on the full idele group, not a continuation
or a convergence theorem.
-/

open NumberField MeasureTheory

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "σ" => rationalAdeleFiniteSign

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace J] [BorelSpace J]

/-- With calibrated rational idele Haar, translating by the finite-sign
involution transfers the printed Fourier Mellin pairing to the repaired one.
The equality holds for totalized Bochner integrals and does not assert that
either integrand is integrable. -/
public theorem integral_rationalAdeleSameSignFourier_mul_char (f : A → ℂ) (d : J →* ℂ) :
    (∫ k : J, rationalAdeleSameSignFourier f (k : A) * d k ∂rationalIdeleHaar) =
      d σ * ∫ k : J, rationalAdeleFourier f (k : A) * d k ∂rationalIdeleHaar := by
  calc
    _ = ∫ k : J, rationalAdeleSameSignFourier f ((σ * k : J) : A) * d (σ * k)
          ∂rationalIdeleHaar :=
      (integral_mul_left_eq_self (μ := rationalIdeleHaar)
        (fun k : J ↦ rationalAdeleSameSignFourier f (k : A) * d k) σ).symm
    _ = ∫ k : J, d σ * (rationalAdeleFourier f (k : A) * d k) ∂rationalIdeleHaar := by
      congr 1
      funext k
      rw [rationalAdeleSameSignFourier_eq, ← Units.val_mul, ← mul_assoc,
        rationalAdeleFiniteSign_mul_self, one_mul, map_mul, mul_left_comm]
    _ = _ := integral_const_mul _ _

end Masullo
