module

public import Theorems.RationalAdeleUnramifiedFourier
public import Lemmas.FinitePlaceSupport
import Lemmas.RationalAdeleAffineIntegral

/-! # Fourier transform of rational adelic boxes

Translation and idele dilation extend the unramified tensor calculation
of Example A.3.1.8, p. 558. With the negative sign of Example A.3.1.5,
the phase of a translation is conjugated, as in the corrected local
calculation for Example A.3.1.6.
-/

open NumberField MeasureTheory
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar
local notation "χ" => rationalAdeleAddChar

/-- The unramified tensor in the coordinates `g⁻¹(x - a)`. At the finite places
it is supported in a translate of a product of dilated local integer rings. -/
@[expose] public noncomputable def rationalAdeleBox (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) (x : A) : ℂ :=
  rationalAdeleUnramified b ((g⁻¹ : J) * (x - a))

private theorem box_at_affine (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) (x : A) :
    rationalAdeleBox b a g (a + (g : A) * x) = rationalAdeleUnramified b x := by
  rw [rationalAdeleBox, add_comm a, add_sub_cancel_right, ← mul_assoc]
  change rationalAdeleUnramified b (((↑((g⁻¹ : J) * g) : A)) * x) = _
  rw [inv_mul_cancel, Units.val_one, one_mul]

public theorem continuous_rationalAdeleBox (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) :
    Continuous (rationalAdeleBox b a g) :=
  (continuous_rationalAdeleUnramified b).comp
    (continuous_const.mul (continuous_id.sub continuous_const))

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- Every translated idele dilation of the unramified Schwartz tensor belongs
to `L¹` for normalized additive adelic Haar. -/
public theorem integrable_rationalAdeleBox (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) :
    Integrable (rationalAdeleBox b a g) μA :=
  integrable_rationalAdele_inv_affine (integrable_rationalAdeleUnramified b) a g

/-- Multiplying a box by the Fourier phase preserves its integrability. -/
public theorem integrable_rationalAdeleBox_mul_conj_char (b : 𝓢(ℝ, ℂ))
    (a : A) (g : J) (y : A) :
    Integrable (fun x ↦ rationalAdeleBox b a g x * conj (χ (x * y))) μA := by
  have hphase : Continuous (fun x : A ↦ conj (χ (x * y))) := Complex.continuous_conj.comp
    (continuous_rationalAdeleAddChar.comp (continuous_id.mul continuous_const))
  apply (integrable_rationalAdeleBox b a g).mul_bdd hphase.aestronglyMeasurable (c := 1)
  exact Filter.Eventually.of_forall fun x ↦ by rw [Complex.norm_conj, norm_rationalAdeleAddChar]

/-- The Fourier integral of the translated box at every adelic frequency.
Translation gives a phase, not a shift in the dual box. The idele norm is the
Jacobian for the substitution `x = a + g*z`. -/
public theorem integral_rationalAdeleBox_mul_conj_char (b : 𝓢(ℝ, ℂ)) (a : A) (g : J) (y : A) :
    (∫ x, rationalAdeleBox b a g x * conj (χ (x * y)) ∂μA) =
      ideleNorm g • (conj (χ (a * y)) * rationalAdeleUnramified (𝓕 b) ((g : A) * y)) := by
  rw [integral_rationalAdele_affine _ a g]
  have h (x : A) : rationalAdeleBox b a g (a + (g : A) * x) *
      conj (χ ((a + (g : A) * x) * y)) =
      conj (χ (a * y)) * (rationalAdeleUnramified b x * conj (χ (x * ((g : A) * y)))) := by
    rw [box_at_affine, add_mul, mul_assoc, mul_left_comm (g : A) x, AddChar.map_add_eq_mul, map_mul]
    ring
  simp_rw [h, integral_const_mul, integral_rationalAdeleUnramified_mul_conj_char]

end Masullo
