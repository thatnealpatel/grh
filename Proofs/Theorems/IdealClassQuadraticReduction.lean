module

public import Theorems.IdealClassSplitPrimeSign
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.QuadraticAlgebra.Discriminant

/-!
# Reduction of the integers of ℚ(√-5)

The quotient by `(n)` reduces both integral coordinates modulo `n`. For an
odd rational prime `p`, its discriminant detects when `(p)` is prime, so the
inert factor of the finite Hecke product (3.2.1.7), p. 124, applies.
For `p ≠ 2, 5` with a root of `t² = -5`, evaluation at the two opposite
roots instead identifies the quotient with a product of two fields.
-/

open NumberField
open scoped QuadraticAlgebra

namespace Masullo

local notation "O" => 𝓞 QSqrtNegFive
local notation "Q" n => QuadraticAlgebra (ZMod n) (-5) 0

private def reduceCoordinates (n : ℕ) : QuadraticAlgebra ℤ (-5) 0 →+* Q n where
  toFun z := ⟨z.re, z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

private noncomputable def reduction (n : ℕ) : O →+* Q n :=
  (reduceCoordinates n).comp qSqrtNegFiveIntegersEquiv.toRingEquiv.toRingHom

private theorem reduction_apply (n : ℕ) (z : O) :
    reduction n z = ⟨↑(qSqrtNegFiveIntegersEquiv z).re, ↑(qSqrtNegFiveIntegersEquiv z).im⟩ := rfl

private theorem reduction_surjective (n : ℕ) : Function.Surjective (reduction n) := by
  intro z
  obtain ⟨x, hx⟩ := ZMod.intCast_surjective z.re
  obtain ⟨y, hy⟩ := ZMod.intCast_surjective z.im
  refine ⟨qSqrtNegFiveIntegersEquiv.symm ⟨x, y⟩, ?_⟩
  rw [reduction_apply, AlgEquiv.apply_symm_apply]
  exact QuadraticAlgebra.ext hx hy

private theorem reduction_ker (n : ℕ) : RingHom.ker (reduction n) = Ideal.span {(n : O)} := by
  refine le_antisymm (fun z hz ↦ ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
  · have h := RingHom.mem_ker.mp hz
    rw [reduction_apply, QuadraticAlgebra.ext_iff] at h
    obtain ⟨x, hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp h.1
    obtain ⟨y, hy⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp h.2
    refine Ideal.mem_span_singleton.mpr ⟨qSqrtNegFiveIntegersEquiv.symm ⟨x, y⟩, ?_⟩
    apply qSqrtNegFiveIntegersEquiv.injective
    rw [map_mul, map_natCast, AlgEquiv.apply_symm_apply]
    ext <;> simp [hx, hy]
  · rw [RingHom.mem_ker, map_natCast]
    ext <;> simp

/-- Reduction of both integral coordinates identifies the quotient by `(n)` with the
quadratic algebra over `ZMod n`. No primality assumption is needed. -/
public noncomputable def qSqrtNegFiveQuotientSpanNatEquiv (n : ℕ) :
    (O ⧸ Ideal.span {(n : O)}) ≃+* Q n :=
  (Ideal.quotEquivOfEq (reduction_ker n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (reduction_surjective n))

/-- The quotient equivalence is coordinatewise reduction in the basis `1, √-5`. -/
public theorem qSqrtNegFiveQuotientSpanNatEquiv_mk (n : ℕ) (z : O) :
    qSqrtNegFiveQuotientSpanNatEquiv n (Ideal.Quotient.mk _ z) =
      ⟨((qSqrtNegFiveIntegersEquiv z).re : ZMod n),
        ((qSqrtNegFiveIntegersEquiv z).im : ZMod n)⟩ := by
  rw [qSqrtNegFiveQuotientSpanNatEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, reduction_apply]

/-- An odd rational prime generates a prime ideal of the full ring of integers exactly when
`-5` is not a square modulo that prime. -/
public theorem qSqrtNegFive_isPrime_span_iff_not_isSquare (p : Nat.Primes) (hp : p.val ≠ 2) :
    (Ideal.span {(p.val : O)}).IsPrime ↔ ¬ IsSquare (-5 : ZMod p.val) := by
  rw [← Ideal.Quotient.isDomain_iff_prime,
    (qSqrtNegFiveQuotientSpanNatEquiv p.val).toMulEquiv.isDomain_iff]
  let : Fact (Nat.Prime p.val) := ⟨p.2⟩
  let : NeZero p.val := ⟨p.2.ne_zero⟩
  let : NeZero (2 : ZMod p.val) := ⟨fun h ↦
    ((Nat.dvd_prime Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p.val).mp h)).elim
      p.2.ne_one hp⟩
  let : Finite (Q p.val) := Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm
  have hfield : IsDomain (Q p.val) ↔ IsField (Q p.val) :=
    ⟨fun _ ↦ Finite.isField_of_domain _, IsField.isDomain⟩
  rw [hfield, QuadraticAlgebra.isField_iff_not_isSquare_discr]
  -- Invertibility of 2 makes the discriminant `4 * (-5)` square iff `-5` is square.
  let : Invertible (2 : ZMod p.val) := invertibleOfNonzero two_ne_zero
  rw [← QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr, isSquare_iff_exists_sq]
  simp [eq_comm]

example : (Ideal.span {(11 : O)}).IsPrime := by
  apply (qSqrtNegFive_isPrime_span_iff_not_isSquare ⟨11, by decide⟩ (by decide)).mpr
  rw [isSquare_iff_exists_sq]
  decide

example : ¬ (Ideal.span {(3 : O)}).IsPrime := by
  intro h
  exact (qSqrtNegFive_isPrime_span_iff_not_isSquare ⟨3, by decide⟩ (by decide)).mp h ⟨1, by decide⟩

section Split

variable {R : Type*} {a r : R}

private def evaluateRootPair [CommRing R] (hr : r ^ 2 = a) : QuadraticAlgebra R a 0 →+* R × R :=
  (QuadraticAlgebra.lift ⟨r, by simpa [pow_two] using hr⟩).toRingHom.prod
    (QuadraticAlgebra.lift ⟨-r, by simpa [pow_two] using hr⟩).toRingHom

private theorem evaluateRootPair_apply [CommRing R] (hr : r ^ 2 = a) (z : QuadraticAlgebra R a 0) :
    evaluateRootPair hr z = (z.re + r * z.im, z.re - r * z.im) := by
  simp [evaluateRootPair, QuadraticAlgebra.lift_apply_apply, mul_comm, sub_eq_add_neg]

private theorem evaluateRootPair_bijective [Field R]
    (hr : r ^ 2 = a) (h₂ : (2 : R) ≠ 0) (hr₀ : r ≠ 0) :
    Function.Bijective (evaluateRootPair hr) := by
  have h₂r : 2 * r ≠ 0 := mul_ne_zero h₂ hr₀
  let recover (uv : R × R) : QuadraticAlgebra R a 0 :=
    ⟨(uv.1 + uv.2) / 2, (uv.1 - uv.2) / (2 * r)⟩
  have hleft : Function.LeftInverse recover (evaluateRootPair hr) := by
    intro z
    rw [evaluateRootPair_apply]
    apply QuadraticAlgebra.ext <;> dsimp [recover] <;> field_simp <;> ring
  have hright : Function.RightInverse recover (evaluateRootPair hr) := by
    intro uv
    rw [evaluateRootPair_apply]
    apply Prod.ext <;> dsimp [recover] <;> field_simp <;> ring
  exact ⟨hleft.injective, hright.surjective⟩

end Split

/-- For `p ≠ 2, 5`, a root `r` of `t² = -5` gives a product quotient of the full integer
ring, with evaluations at `r` and `-r` in that order. -/
public noncomputable def qSqrtNegFiveSplitQuotientEquiv (p : Nat.Primes)
    (hp₂ : p.val ≠ 2) (hp₅ : p.val ≠ 5) (r : ZMod p.val) (hr : r ^ 2 = -5) :
    (O ⧸ Ideal.span {(p.val : O)}) ≃+* (ZMod p.val × ZMod p.val) := by
  let : Fact (Nat.Prime p.val) := ⟨p.2⟩
  have h₂ : (2 : ZMod p.val) ≠ 0 := fun h ↦
    ((Nat.dvd_prime Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p.val).mp h)).elim
      p.2.ne_one hp₂
  have hr₀ : r ≠ 0 := by
    intro h
    have h₅ : (5 : ZMod p.val) = 0 := by simpa [h, eq_comm] using hr
    exact ((Nat.dvd_prime Nat.prime_five).mp ((ZMod.natCast_eq_zero_iff 5 p.val).mp h₅)).elim
      p.2.ne_one hp₅
  exact (qSqrtNegFiveQuotientSpanNatEquiv p.val).trans
    (RingEquiv.ofBijective (evaluateRootPair hr) (evaluateRootPair_bijective hr h₂ hr₀))

/-- The class of `x + y√-5` maps to the evaluations of its reduced coordinates. -/
public theorem qSqrtNegFiveSplitQuotientEquiv_mk (p : Nat.Primes)
    (hp₂ : p.val ≠ 2) (hp₅ : p.val ≠ 5) (r : ZMod p.val) (hr : r ^ 2 = -5) (x y : ℤ) :
    qSqrtNegFiveSplitQuotientEquiv p hp₂ hp₅ r hr
        (Ideal.Quotient.mk _ (qSqrtNegFiveIntegersEquiv.symm ⟨x, y⟩)) =
      ((x : ZMod p.val) + r * (y : ZMod p.val), (x : ZMod p.val) - r * (y : ZMod p.val)) := by
  rw [qSqrtNegFiveSplitQuotientEquiv, RingEquiv.trans_apply, RingEquiv.ofBijective_apply,
    evaluateRootPair_apply, qSqrtNegFiveQuotientSpanNatEquiv_mk, AlgEquiv.apply_symm_apply]

example : qSqrtNegFiveSplitQuotientEquiv ⟨3, by decide⟩ (by decide) (by decide) 1 (by decide)
    (Ideal.Quotient.mk _ (qSqrtNegFiveIntegersEquiv.symm ⟨0, 1⟩)) = (1, -1) := by
  simpa only [Int.cast_zero, Int.cast_one, mul_one, zero_add, zero_sub] using
    qSqrtNegFiveSplitQuotientEquiv_mk ⟨3, by decide⟩ (by decide) (by decide) 1 (by decide) 0 1

end Masullo
