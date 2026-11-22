module

public import Theorems.HeckeDirichletFactorization
public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.QuadraticAlgebra

/-!
# The split-prime class sign for ℚ(√-5)

For the finite Euler product (3.2.1.7), p. 124, compute the class sign at
an odd rational prime's degree-one places. The two-class dichotomy and the
norm of the chosen class representative are inputs.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace Masullo

/-- The number field `ℚ(√-5)` in quadratic coordinates. -/
public abbrev QSqrtNegFive := QuadraticAlgebra ℚ (-5) 0

public instance : Fact (¬ IsSquare (-5 : ℚ)) := ⟨by
  rintro ⟨r, hr⟩
  nlinarith [sq_nonneg r]⟩

public noncomputable instance : NumberField QSqrtNegFive where
  to_charZero := inferInstanceAs (CharZero (QuadraticAlgebra ℚ (-5) 0))
  to_finiteDimensional := inferInstanceAs (FiniteDimensional ℚ (QuadraticAlgebra ℚ (-5) 0))

private theorem fundamentalDiscr_negFive : Int.IsFundamentalDiscr (QuadraticAlgebra.discr (-5) 0) := by
  rw [show QuadraticAlgebra.discr (-5 : ℤ) 0 = 4 * (-5) by norm_num [QuadraticAlgebra.discr_def],
    Int.isFundamentalDiscr_four_mul]
  exact ⟨Int.squarefree_natAbs.mp (show Squarefree (5 : ℕ) from (by decide : Nat.Prime 5).prime.squarefree),
    Or.inr (by decide)⟩

/-- Integral coordinates in the basis `1, √-5` of the full ring of integers. -/
public noncomputable def qSqrtNegFiveIntegersEquiv :
    𝓞 QSqrtNegFive ≃ₐ[ℤ] QuadraticAlgebra ℤ (-5) 0 :=
  (QuadraticAlgebra.Int.algEquivIntegralClosure fundamentalDiscr_negFive).symm

local notation "Places" => HeightOneSpectrum (𝓞 QSqrtNegFive)

/-- The integral ideal class of a finite place of `ℚ(√-5)`. -/
public noncomputable def qSqrtNegFivePlaceClass (v : Places) : ClassGroup (𝓞 QSqrtNegFive) :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩

private theorem placeClass_eq_one_iff (v : Places) :
    qSqrtNegFivePlaceClass v = 1 ↔ v.asIdeal.IsPrincipal :=
  ClassGroup.mk0_eq_one_iff _

private theorem span_absNorm_eq_coordinates (a : 𝓞 QSqrtNegFive) :
    ((Ideal.span {a}).absNorm : ℤ) =
      (qSqrtNegFiveIntegersEquiv a).re ^ 2 + 5 * (qSqrtNegFiveIntegersEquiv a).im ^ 2 := by
  rw [Ideal.absNorm_span_singleton, ← Algebra.norm_eq_of_algEquiv qSqrtNegFiveIntegersEquiv a,
    Algebra.norm_quadraticAlgebra_apply, QuadraticAlgebra.norm_def]
  simp only [zero_mul, add_zero]
  rw [show (qSqrtNegFiveIntegersEquiv a).re * (qSqrtNegFiveIntegersEquiv a).re -
      (-5) * (qSqrtNegFiveIntegersEquiv a).im * (qSqrtNegFiveIntegersEquiv a).im =
      (qSqrtNegFiveIntegersEquiv a).re ^ 2 + 5 * (qSqrtNegFiveIntegersEquiv a).im ^ 2 by ring,
    Int.natAbs_of_nonneg (by positivity)]

private theorem coordinates_emod_four (x y : ℤ) :
    (x ^ 2 + 5 * y ^ 2) % 4 = x % 2 + y % 2 := by
  rw [Int.add_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four]
  norm_num
  omega

private theorem odd_sq_emod_eight {x : ℤ} (hx : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  have h := Int.modEq_of_dvd (Int.eight_dvd_sq_sub_one_of_odd (Int.odd_iff.mpr hx))
  exact h.symm

private theorem degreeOne_absNorm (v : Places) (hdeg : v.asIdeal.inertiaDeg ℤ = 1) :
    v.asIdeal.absNorm = (heckeRationalPrime v).val := by
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  simpa only [hdeg, pow_one, heckeRationalPrime] using h.symm

private theorem product_span_of_nonprincipal (v₂ v : Places)
    (hclasses : ∀ c : ClassGroup (𝓞 QSqrtNegFive), c = 1 ∨ c = qSqrtNegFivePlaceClass v₂)
    (hv : ¬ v.asIdeal.IsPrincipal) :
    ∃ a : 𝓞 QSqrtNegFive, v.asIdeal * v₂.asIdeal = Ideal.span {a} := by
  have hv' : qSqrtNegFivePlaceClass v ≠ 1 := mt (placeClass_eq_one_iff v).mp hv
  have h := (hclasses (qSqrtNegFivePlaceClass v)).resolve_left hv'
  have h₂ : qSqrtNegFivePlaceClass v₂ ≠ 1 := h ▸ hv'
  have hinv := (hclasses (qSqrtNegFivePlaceClass v₂)⁻¹).resolve_left (by simpa using h₂)
  have hprod : qSqrtNegFivePlaceClass v = (qSqrtNegFivePlaceClass v₂)⁻¹ := h.trans hinv.symm
  obtain ⟨a, -, ha⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp hprod
  exact ⟨a, ha⟩

/-- With the two-class dichotomy and a norm-two representative as inputs,
any place of residue degree one above an odd rational prime is principal
exactly when the rational prime is `1 mod 4`. This applies to both places
of an odd split prime. The degree condition alone does not assert splitting
or identify the place over `5`. -/
public theorem qSqrtNegFive_split_isPrincipal_iff (v₂ v : Places)
    (h₂ : v₂.asIdeal.absNorm = 2)
    (hclasses : ∀ c : ClassGroup (𝓞 QSqrtNegFive), c = 1 ∨ c = qSqrtNegFivePlaceClass v₂)
    (hdeg : v.asIdeal.inertiaDeg ℤ = 1) (hodd : Odd (heckeRationalPrime v).val) :
    v.asIdeal.IsPrincipal ↔ (heckeRationalPrime v).val % 4 = 1 := by
  let p := (heckeRationalPrime v).val
  have hp : (p : ℤ) % 2 = 1 := Int.odd_iff.mp hodd.natCast
  have hN : v.asIdeal.absNorm = p := degreeOne_absNorm v hdeg
  by_cases hv : v.asIdeal.IsPrincipal
  · obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal v.asIdeal
    change v.asIdeal = Ideal.span {a} at ha
    have h : (p : ℤ) = (qSqrtNegFiveIntegersEquiv a).re ^ 2 +
        5 * (qSqrtNegFiveIntegersEquiv a).im ^ 2 := by
      rw [← hN, ha, span_absNorm_eq_coordinates]
    have hmod := congrArg (· % 4) h
    rw [coordinates_emod_four] at hmod
    have : (p : ℤ) % 4 = 1 := by omega
    exact iff_of_true hv (by exact_mod_cast this)
  · obtain ⟨a, ha⟩ := product_span_of_nonprincipal v₂ v hclasses hv
    have hNa : (Ideal.span {a}).absNorm = p * 2 := by rw [← ha, map_mul, hN, h₂]
    have h := span_absNorm_eq_coordinates a
    rw [hNa, Nat.cast_mul, Nat.cast_ofNat] at h
    have hmod := congrArg (· % 4) h
    rw [coordinates_emod_four] at hmod
    have hx : (qSqrtNegFiveIntegersEquiv a).re % 2 = 1 := by omega
    have hy : (qSqrtNegFiveIntegersEquiv a).im % 2 = 1 := by omega
    have hmod₈ := congrArg (· % 8) h
    rw [Int.add_emod, Int.mul_emod 5, odd_sq_emod_eight hx, odd_sq_emod_eight hy] at hmod₈
    norm_num at hmod₈
    have hp₃ : (p : ℤ) % 4 = 3 := by omega
    have hp₃' : p % 4 = 3 := by exact_mod_cast hp₃
    exact iff_of_false hv (by change p % 4 ≠ 1; omega)

/-- The normalized class character has value `χ₋₄(p)` at every odd
residue-degree-one place above `p`. No idelic character is constructed here. -/
public theorem qSqrtNegFive_split_classCharacter (v₂ v : Places)
    (h₂ : v₂.asIdeal.absNorm = 2)
    (hclasses : ∀ c : ClassGroup (𝓞 QSqrtNegFive), c = 1 ∨ c = qSqrtNegFivePlaceClass v₂)
    (hdeg : v.asIdeal.inertiaDeg ℤ = 1) (hodd : Odd (heckeRationalPrime v).val)
    (χ : ClassGroup (𝓞 QSqrtNegFive) →* ℂ) (hχ : χ (qSqrtNegFivePlaceClass v₂) = -1) :
    χ (qSqrtNegFivePlaceClass v) = dirichletNegFour (heckeRationalPrime v).val := by
  have hp := Nat.odd_iff.mp hodd
  have h := qSqrtNegFive_split_isPrincipal_iff v₂ v h₂ hclasses hdeg hodd
  rw [dirichletNegFour, MulChar.ringHomComp_apply, ZMod.χ₄_nat_eq_if_mod_four, hp]
  simp only [one_ne_zero, ite_false]
  split_ifs with hmod
  · rw [(placeClass_eq_one_iff v).mpr (h.mpr hmod), map_one, map_one]
  · have hv : qSqrtNegFivePlaceClass v ≠ 1 := fun he ↦ hmod (h.mp ((placeClass_eq_one_iff v).mp he))
    rw [(hclasses (qSqrtNegFivePlaceClass v)).resolve_left hv, hχ, map_neg, map_one]

end Masullo
