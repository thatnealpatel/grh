module

public import Theorems.RationalAdeleBoxThetaInversion
import Lemmas.RationalAdeleAdditiveModulus
import Mathlib.MeasureTheory.Integral.Prod

/-! # Bilinear transposition of the rational adelic Fourier integral

The conjugated pairing in (D.1.1.4), p. 746, is symmetric in rational
adelic coordinates. Fubini applies to the product of two `L¹` inputs
because the character factor has unit norm. The same proof works after
reflection, as needed to use the inverse kernel in (D.1.1.11).
-/

open NumberField MeasureTheory Filter
open scoped ComplexConjugate

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar
local notation "F" => rationalAdeleFourier

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- Both bilinear products are integrable and their integrals agree. Taking
`t = 1` gives transposition of the forward integral, and `t = -1` gives
transposition of the reflected integral. -/
public theorem rationalAdeleFourier_transpose {p q : A → ℂ}
    (hp : Integrable p μA) (hq : Integrable q μA) (t : A) :
    Integrable (fun y ↦ F p (t * y) * q y) μA ∧
      Integrable (fun x ↦ p x * F q (t * x)) μA ∧
      (∫ y, F p (t * y) * q y ∂μA) = ∫ x, p x * F q (t * x) ∂μA := by
  let : SecondCountableTopology A := secondCountableTopology_rationalAdeles
  let : LocallyCompactSpace A := rationalAdeleClosedUnitStrip.locallyCompactSpace_of_addGroup
  let K (x y : A) : ℂ := conj (rationalAdeleAddChar (x * (t * y)))
  have hKx (x y : A) : K x y = K y x := by
    dsimp [K]
    congr 2
    ac_rfl
  have hKc : Continuous (fun z : A × A ↦ K z.1 z.2) := Complex.continuous_conj.comp
    (continuous_rationalAdeleAddChar.comp (continuous_fst.mul (continuous_const.mul continuous_snd)))
  have hKI : Integrable (fun z : A × A ↦ (p z.1 * q z.2) * K z.1 z.2) (Measure.prod μA μA) :=
    (hp.mul_prod hq).mul_bdd hKc.aestronglyMeasurable (c := 1) (Eventually.of_forall fun z ↦
      ((Complex.norm_conj _).trans (norm_rationalAdeleAddChar (z.1 * (t * z.2)))).le)
  have hleft (x : A) : (∫ y, (p x * q y) * K x y ∂μA) = p x * F q (t * x) := by
    rw [rationalAdeleFourier, ← integral_const_mul]
    congr 1
    funext y
    rw [hKx x y, mul_assoc]
  have hright (y : A) : (∫ x, (p x * q y) * K x y ∂μA) = F p (t * y) * q y := by
    rw [rationalAdeleFourier, ← integral_mul_const]
    congr 1
    funext x
    exact mul_right_comm _ _ _
  exact ⟨by simpa only [hright] using hKI.integral_prod_right,
    by simpa only [hleft] using hKI.integral_prod_left,
    by simpa only [hleft, hright] using
      (integral_integral_swap (f := fun x y ↦ (p x * q y) * K x y) hKI).symm⟩

end Masullo
