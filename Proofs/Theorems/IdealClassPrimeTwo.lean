module

public import Theorems.IdealClassSplitPrimeSign

/-!
# The prime over two in ℚ(√-5)

This supplies the ideal-theoretic input at two for Masullo's finite Euler
product (3.2.1.7), p. 124. It does not construct the idelic character.
-/

open NumberField IsDedekindDomain

namespace Masullo

local notation "O" => 𝓞 QSqrtNegFive

/-- The integral element `√-5` in the quadratic coordinates of the full ring of integers. -/
public noncomputable def qSqrtNegFiveSqrt : O :=
  qSqrtNegFiveIntegersEquiv.symm QuadraticAlgebra.omega

/-- In the integral basis, `√-5` is the quadratic generator. -/
public theorem qSqrtNegFiveIntegersEquiv_sqrt :
    qSqrtNegFiveIntegersEquiv qSqrtNegFiveSqrt = QuadraticAlgebra.omega :=
  qSqrtNegFiveIntegersEquiv.apply_symm_apply _

private noncomputable def reductionTwo : O →+* ZMod 2 :=
  ((QuadraticAlgebra.lift ⟨1, by decide⟩).comp qSqrtNegFiveIntegersEquiv.toAlgHom).toRingHom

private theorem reductionTwo_two : reductionTwo 2 = 0 := by
  rw [map_ofNat]
  decide

private theorem reductionTwo_surjective : Function.Surjective reductionTwo := by
  intro z
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨n, map_intCast reductionTwo n⟩

private theorem reductionTwo_apply (a : O) :
    reductionTwo a = (((qSqrtNegFiveIntegersEquiv a).re +
      (qSqrtNegFiveIntegersEquiv a).im : ℤ) : ZMod 2) := by
  change _ • (1 : ZMod 2) + _ • (1 : ZMod 2) = _
  simp [zsmul_eq_mul]

private theorem coordinates_eq (a : O) :
    a = ((qSqrtNegFiveIntegersEquiv a).re : O) +
      ((qSqrtNegFiveIntegersEquiv a).im : O) * qSqrtNegFiveSqrt := by
  apply qSqrtNegFiveIntegersEquiv.injective
  simp only [map_add, map_mul, map_intCast, qSqrtNegFiveSqrt, AlgEquiv.apply_symm_apply]
  ext <;> simp

/-- The finite place cut out by reducing modulo two and sending `√-5` to one. -/
public noncomputable def qSqrtNegFivePrimeTwo : HeightOneSpectrum O where
  asIdeal := RingHom.ker reductionTwo
  isPrime := RingHom.ker_isPrime reductionTwo
  ne_bot := by
    intro h
    have h₂ : (2 : O) ∈ RingHom.ker reductionTwo := RingHom.mem_ker.mpr reductionTwo_two
    rw [h, Ideal.mem_bot] at h₂
    exact two_ne_zero h₂

/-- The place over two is the ideal `(2, 1 + √-5)` in the full ring of integers. -/
public theorem qSqrtNegFivePrimeTwo_asIdeal :
    qSqrtNegFivePrimeTwo.asIdeal = Ideal.span {(2 : O), 1 + qSqrtNegFiveSqrt} := by
  change RingHom.ker reductionTwo = _
  let I : Ideal O := Ideal.span {(2 : O), 1 + qSqrtNegFiveSqrt}
  have h₂ : (2 : O) ∈ I := Ideal.subset_span (by simp)
  have hα : 1 + qSqrtNegFiveSqrt ∈ I := Ideal.subset_span (by simp)
  refine le_antisymm (fun a ha ↦ ?_) (Ideal.span_le.mpr ?_)
  · change a ∈ I
    have h := RingHom.mem_ker.mp ha
    rw [reductionTwo_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    let x := (qSqrtNegFiveIntegersEquiv a).re
    let y := (qSqrtNegFiveIntegersEquiv a).im
    obtain ⟨k, hk⟩ : (2 : ℤ) ∣ x + y := h
    have hxy : x - y = 2 * (k - y) := by omega
    have hac : a = ((k - y : ℤ) : O) * 2 + (y : O) * (1 + qSqrtNegFiveSqrt) := by
      calc
        a = ((x - y : ℤ) : O) + (y : O) * (1 + qSqrtNegFiveSqrt) := by
          conv_lhs => rw [coordinates_eq a]
          change (x : O) + (y : O) * qSqrtNegFiveSqrt = _
          push_cast
          ring
        _ = _ := by rw [hxy]; push_cast; ring
    rw [hac]
    exact I.add_mem (I.mul_mem_left _ h₂) (I.mul_mem_left _ hα)
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact RingHom.mem_ker.mpr reductionTwo_two
    · apply RingHom.mem_ker.mpr
      rw [map_add, map_one, reductionTwo_apply]
      simp only [qSqrtNegFiveSqrt, AlgEquiv.apply_symm_apply,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_add, Int.cast_one]
      decide

/-- The residue field at the place over two is `𝔽₂`. -/
public noncomputable def qSqrtNegFivePrimeTwo_residueEquiv :
    O ⧸ qSqrtNegFivePrimeTwo.asIdeal ≃+* ZMod 2 :=
  reductionTwo.quotientKerEquivOfSurjective reductionTwo_surjective

/-- The absolute ideal norm of the place over two is two. -/
public theorem qSqrtNegFivePrimeTwo_absNorm : qSqrtNegFivePrimeTwo.asIdeal.absNorm = 2 := by
  rw [Ideal.absNorm_eq_natCard, Nat.card_congr qSqrtNegFivePrimeTwo_residueEquiv.toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

/-- The place lies over the ideal `(2)` in `ℤ`. -/
public theorem qSqrtNegFivePrimeTwo_under :
    qSqrtNegFivePrimeTwo.asIdeal.under ℤ = Ideal.span {(2 : ℤ)} := by
  ext n
  change reductionTwo (algebraMap ℤ O n) = 0 ↔ _
  rw [algebraMap_int_eq]
  change reductionTwo (n : O) = 0 ↔ _
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat, Ideal.mem_span_singleton]

/-- Every prime ideal containing two is the indicated place. -/
public theorem qSqrtNegFivePrimeTwo_unique (P : Ideal O) (hP : P.IsPrime)
    (h₂ : (2 : O) ∈ P) : P = qSqrtNegFivePrimeTwo.asIdeal := by
  have hsq : (1 + qSqrtNegFiveSqrt) ^ 2 = (qSqrtNegFiveSqrt - 2) * 2 := by
    apply qSqrtNegFiveIntegersEquiv.injective
    simp only [map_pow, map_add, map_sub, map_one, map_ofNat, map_mul,
      qSqrtNegFiveSqrt, AlgEquiv.apply_symm_apply]
    ext <;> norm_num [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  have hα : 1 + qSqrtNegFiveSqrt ∈ P :=
    (hP.pow_mem_iff_mem 2 (by decide)).mp (hsq ▸ P.mul_mem_left _ h₂)
  have hmax := RingHom.ker_isMaximal_of_surjective reductionTwo reductionTwo_surjective
  apply (hmax.eq_of_le hP.ne_top ?_).symm
  change qSqrtNegFivePrimeTwo.asIdeal ≤ P
  rw [qSqrtNegFivePrimeTwo_asIdeal]
  exact Ideal.span_le.mpr (by simpa [Set.insert_subset_iff] using And.intro h₂ hα)

/-- This place is not principal: `x² + 5y² = 2` has no integral solution. -/
public theorem qSqrtNegFivePrimeTwo_not_isPrincipal :
    ¬ qSqrtNegFivePrimeTwo.asIdeal.IsPrincipal := by
  intro hP
  let := hP
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal qSqrtNegFivePrimeTwo.asIdeal
  change qSqrtNegFivePrimeTwo.asIdeal = Ideal.span {a} at ha
  have hn := qSqrtNegFive_span_absNorm_eq_coordinates a
  rw [← ha, qSqrtNegFivePrimeTwo_absNorm] at hn
  norm_num at hn
  generalize (qSqrtNegFiveIntegersEquiv a).re = x at hn
  generalize (qSqrtNegFiveIntegersEquiv a).im = y at hn
  have hy : y = 0 := by
    by_contra h
    have hpos := sq_pos_of_ne_zero h
    have hle : 1 ≤ y ^ 2 := by omega
    nlinarith only [hn, hle, sq_nonneg x]
  rw [hy] at hn
  norm_num at hn
  have hx := Int.sq_emod_four x
  omega

/-- The place over two represents a nonidentity ideal class. -/
public theorem qSqrtNegFivePrimeTwo_class_ne_one :
    qSqrtNegFivePlaceClass qSqrtNegFivePrimeTwo ≠ 1 := by
  intro h
  exact qSqrtNegFivePrimeTwo_not_isPrincipal ((qSqrtNegFive_placeClass_eq_one_iff _).mp h)

end Masullo
