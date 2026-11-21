module

public import Theorems.RationalAdeleWeil
public import Theorems.RationalAdeleCharacter

import Theorems.RationalAdeleAnnihilator

/-!
# Fourier coefficients on the rational adele classes

At diagonal rational frequencies, the Fourier coefficient of the quotient
periodization is the upstairs Fourier integral. This is the rational Borel
`L¹` comparison in Theorem D.1.2.7(1), p. 749, with the negative Fourier sign.
-/

open NumberField MeasureTheory Topology
open scoped ComplexConjugate

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "C" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → C)
local notation "ι" => algebraMap ℚ A

private theorem frequency_invariant (r : ℚ) {a b : A} (h : π a = π b) :
    rationalAdeleAddChar (a * ι r) = rationalAdeleAddChar (b * ι r) := by
  obtain ⟨q, hq⟩ := QuotientAddGroup.eq_iff_sub_mem.mp h
  have heq : a = ι q + b := (sub_eq_iff_eq_add.mp hq.symm)
  rw [heq, add_mul, AddChar.map_add_eq_mul, ← map_mul (ι),
    rationalAdeleAddChar_algebraMap, one_mul]

/-- The quotient character obtained from the upstairs frequency `r ∈ ℚ`. -/
public noncomputable def rationalAdeleClassChar (r : ℚ) : AddChar C ℂ where
  toFun := Quotient.lift (fun a : A ↦ rationalAdeleAddChar (a * ι r))
    (fun _ _ h ↦ frequency_invariant r (Quotient.sound h))
  map_zero_eq_one' := by
    change rationalAdeleAddChar ((0 : A) * ι r) = 1
    rw [zero_mul, AddChar.map_zero_eq_one]
  map_add_eq_mul' c e := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective e
    change rationalAdeleAddChar ((a + b) * ι r) = _
    rw [add_mul, AddChar.map_add_eq_mul]
    rfl

@[simp]
public theorem rationalAdeleClassChar_mk (r : ℚ) (a : A) :
    rationalAdeleClassChar r (π a) = rationalAdeleAddChar (a * ι r) := by
  unfold rationalAdeleClassChar
  rfl

public theorem continuous_rationalAdeleClassChar (r : ℚ) :
    Continuous (rationalAdeleClassChar r : C → ℂ) :=
  (QuotientAddGroup.isQuotientMap_mk rationalDiagonal).continuous_iff.mpr
    (continuous_rationalAdeleAddChar.comp (continuous_id.mul continuous_const))

public theorem norm_rationalAdeleClassChar (r : ℚ) (c : C) :
    ‖rationalAdeleClassChar r c‖ = 1 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  exact norm_rationalAdeleAddChar (a * ι r)

/-- The diagonal rational frequencies distinguish the points of the quotient. -/
public theorem rationalAdeleClassChar_separates {c e : C} (h : c ≠ e) :
    ∃ r : ℚ, rationalAdeleClassChar r c ≠ rationalAdeleClassChar r e := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective e
  by_contra! heq
  apply h
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  obtain ⟨q, hq⟩ := (rationalAdele_orthogonal_iff (a - b)).mp (fun r ↦ by
    rw [sub_mul, AddChar.map_sub_eq_div, ← rationalAdeleClassChar_mk,
      ← rationalAdeleClassChar_mk, heq, div_self]
    exact fun hz ↦ by simpa [hz] using norm_rationalAdeleClassChar r (π b))
  exact ⟨q, hq.symm⟩

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace C] [BorelSpace C]

/-- Weil's formula applied to the integrable function twisted by the conjugate
adelic character. The quotient coefficient uses the same negative Fourier sign
as the upstairs integral. -/
public theorem integral_rationalAdeleComplexPeriodization_mul_conj_char {f : A → ℂ}
    (hf : Measurable f) (hfi : Integrable f rationalAdeleAddHaar) (r : ℚ) :
    (∫ c, rationalAdeleComplexPeriodization f c * conj (rationalAdeleClassChar r c)
      ∂rationalAdeleClassHaar) =
    ∫ a, f a * conj (rationalAdeleAddChar (a * ι r)) ∂rationalAdeleAddHaar := by
  let phase : A → ℂ := fun a ↦ conj (rationalAdeleAddChar (a * ι r))
  have hphase : Continuous phase := Complex.continuous_conj.comp
    (continuous_rationalAdeleAddChar.comp (continuous_id.mul continuous_const))
  have htwist : Integrable (fun a ↦ f a * phase a) rationalAdeleAddHaar :=
    hfi.mul_bdd hphase.aestronglyMeasurable (c := 1) <|
      Filter.Eventually.of_forall fun a ↦ by
        rw [show ‖phase a‖ = 1 from (Complex.norm_conj _).trans (norm_rationalAdeleAddChar _)]
  change _ = ∫ a, f a * phase a ∂rationalAdeleAddHaar
  rw [integral_eq_integral_rationalAdeleComplexPeriodization
    (f := fun a ↦ f a * phase a) (hf.mul hphase.measurable) htwist]
  congr 1
  funext c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [rationalAdeleComplexPeriodization_mk, rationalAdeleComplexPeriodization_mk, ← tsum_mul_right]
  apply tsum_congr
  intro d
  congr 1
  suffices h : π (a + (d : A)) = π a by
    simp only [phase, ← rationalAdeleClassChar_mk, h]
  have hd : π (d : A) = 0 := (QuotientAddGroup.eq_zero_iff (d : A)).mpr d.property
  rw [QuotientAddGroup.mk_add, hd, add_zero]

end Masullo
