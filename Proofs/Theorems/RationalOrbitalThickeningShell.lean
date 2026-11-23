module

public import Lemmas.RationalFiniteUnits
public import Theorems.RationalOrbitalPrimeTwo

/-!
# A prime-two obstruction to finite-unit thickening

A shared translate of the canonical log section and a second idele cannot put
both in a thickening with unit 2-component if the second idele has nonunit
2-component. This is a pointwise support test, not a statement about Haar-null
sets or about thickenings that allow nonunit finite coordinates.
-/

open IsDedekindDomain NumberField Set
open scoped WithZero

namespace Masullo

local notation "I" => IdeleGroup (𝓞 ℚ) ℚ
local notation "v₂" => rationalOrbitalPrimeTwoPlace

/-- The multiplicative valuation of the finite 2-component. Value `1` means
that the component is a unit of the local integer ring, not merely of the field. -/
public noncomputable def rationalOrbitalPrimeTwoValuation : I →* ℤᵐ⁰ where
  toFun x := Valued.v ((x : AdeleRing (𝓞 ℚ) ℚ).2 v₂)
  map_one' := Valued.v.map_one
  map_mul' _ _ := Valued.v.map_mul _ _

public theorem rationalOrbitalPrimeTwoValuation_apply (x : I) :
    rationalOrbitalPrimeTwoValuation x = Valued.v ((x : AdeleRing (𝓞 ℚ) ℚ).2 v₂) := by
  unfold rationalOrbitalPrimeTwoValuation
  rfl

/-- Thickening the section by any subset of the finite integral units keeps the
2-component a local unit. Here the range allows all of those units. -/
public theorem rationalOrbitalFiniteUnitThickening_subset :
    range (fun p : Multiplicative ℝ × RationalFiniteUnits ↦
      rationalIdeleLogSection p.1 * rationalFiniteUnitIdele p.2) ⊆
    {x | rationalOrbitalPrimeTwoValuation x = 1} := by
  rintro x ⟨⟨t, u⟩, rfl⟩
  change rationalOrbitalPrimeTwoValuation (_ * _) = 1
  rw [map_mul, rationalOrbitalPrimeTwoValuation_apply, rationalIdeleLogSection_finite,
    map_one, one_mul, rationalOrbitalPrimeTwoValuation_apply,
    rationalFiniteUnitIdele_apply_finite]
  exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp (u v₂).isUnit

/-- If both left translates land in a set with unit 2-component, then the
second input has unit 2-component as well. The translating idele is arbitrary. -/
public theorem rationalOrbitalPrimeTwoValuation_eq_one_of_shared_translate
    {S : Set I} (hS : S ⊆ {x | rationalOrbitalPrimeTwoValuation x = 1})
    (t : Multiplicative ℝ) {h y : I}
    (hx : h * rationalIdeleLogSection t ∈ S) (hy : h * y ∈ S) :
    rationalOrbitalPrimeTwoValuation y = 1 := by
  have hh : rationalOrbitalPrimeTwoValuation h = 1 := by
    have hx' : rationalOrbitalPrimeTwoValuation (h * rationalIdeleLogSection t) = 1 := hS hx
    rwa [map_mul, rationalOrbitalPrimeTwoValuation_apply (rationalIdeleLogSection t),
      rationalIdeleLogSection_finite, map_one, mul_one] at hx'
  have hy' : rationalOrbitalPrimeTwoValuation (h * y) = 1 := hS hy
  rwa [map_mul, hh, one_mul] at hy'

/-- On the nonunit prime-two shell in the second argument, the shared-translate
product of weights supported in `S` vanishes, even after scalar multiplication.
The inverse-translate convention is obtained by taking `h` to be the inverse
of the translating idele. -/
public theorem rationalOrbitalThickeningShell_mul_eq_zero {A : Type*} [MulZeroClass A]
    {S : Set I} (hS : S ⊆ {x | rationalOrbitalPrimeTwoValuation x = 1})
    (w : I → A) (hw : Function.support w ⊆ S) (c : A) (t : Multiplicative ℝ) (h : I)
    {y : I} (hy : rationalOrbitalPrimeTwoValuation y ≠ 1) :
    c * (w (h * rationalIdeleLogSection t) * w (h * y)) = 0 := by
  by_cases hx : w (h * rationalIdeleLogSection t) = 0
  · rw [hx, zero_mul, mul_zero]
  have hz : w (h * y) = 0 := by
    by_contra hz
    exact hy (rationalOrbitalPrimeTwoValuation_eq_one_of_shared_translate hS t (hw hx) (hw hz))
  rw [hz, mul_zero, mul_zero]

end Masullo
