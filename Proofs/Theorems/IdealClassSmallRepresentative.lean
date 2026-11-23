module

public import Theorems.IdealClassSplitPrimeSign
public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.QuadraticAlgebra

/-!
# Small integral representatives for the classes of ℚ(√-5)

The field discriminant and signature give a Minkowski bound strictly below
three. This is a finite reduction for the class-group arithmetic used in
the finite Hecke product (3.2.1.7), p. 124.
-/

open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace Masullo

/-- The signed field discriminant in the full integral basis `1, √-5`. -/
public theorem qSqrtNegFive_discr : NumberField.discr QSqrtNegFive = -20 := by
  let b := QuadraticAlgebra.basis (-5 : ℤ) 0
  let e := qSqrtNegFiveIntegersEquiv.symm
  calc
    NumberField.discr QSqrtNegFive = Algebra.discr ℤ (b.map e.toLinearEquiv) :=
      (NumberField.discr_eq_discr _ _).symm
    _ = Algebra.discr ℤ b := (Algebra.discr_eq_discr_of_algEquiv b e).symm
    _ = -20 := by norm_num [b, QuadraticAlgebra.discr_def]

private theorem qSqrtNegFive_finrank : Module.finrank ℚ QSqrtNegFive = 2 :=
  QuadraticAlgebra.finrank_eq_two _ _

/-- The field `ℚ(√-5)` has no real places. -/
public theorem qSqrtNegFive_nrRealPlaces : nrRealPlaces QSqrtNegFive = 0 := by
  classical
  refine Fintype.card_eq_zero_iff.mpr ⟨fun ⟨w, hw⟩ ↦ ?_⟩
  let φ := w.embedding_of_isReal hw
  let a : QSqrtNegFive := QuadraticAlgebra.omega
  have ha : a * a = (-5 : QSqrtNegFive) := by
    norm_num [a, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  have h := congrArg φ ha
  norm_num only [map_mul, map_neg, map_ofNat] at h
  nlinarith [sq_nonneg (φ a)]

/-- The field `ℚ(√-5)` has one complex place. -/
public theorem qSqrtNegFive_nrComplexPlaces : nrComplexPlaces QSqrtNegFive = 1 := by
  have h := card_add_two_mul_card_eq_rank QSqrtNegFive
  rw [qSqrtNegFive_nrRealPlaces, qSqrtNegFive_finrank] at h
  omega

private theorem qSqrtNegFive_minkowski_lt_three : 2 * Real.sqrt 20 / Real.pi < 3 := by
  have hs : Real.sqrt 20 < 9 / 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (20 : ℝ) by norm_num)]
  exact (div_lt_iff₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])

/-- Every class has a nonzero integral representative of absolute norm one or two. -/
public theorem qSqrtNegFive_exists_ideal_in_class_norm_one_or_two
    (c : ClassGroup (𝓞 QSqrtNegFive)) :
    ∃ I : (Ideal (𝓞 QSqrtNegFive))⁰, ClassGroup.mk0 I = c ∧
      ((I : Ideal (𝓞 QSqrtNegFive)).absNorm = 1 ∨ (I : Ideal (𝓞 QSqrtNegFive)).absNorm = 2) := by
  obtain ⟨I, hclass, hI⟩ := NumberField.exists_ideal_in_class_of_norm_le c
  have hlt : ((I : Ideal (𝓞 QSqrtNegFive)).absNorm : ℝ) < 3 := by
    calc
      _ ≤ _ := hI
      _ = 2 * Real.sqrt 20 / Real.pi := by
        norm_num [qSqrtNegFive_finrank, qSqrtNegFive_nrComplexPlaces, qSqrtNegFive_discr,
          Nat.factorial]
        ring
      _ < 3 := qSqrtNegFive_minkowski_lt_three
  have hltNat : (I : Ideal (𝓞 QSqrtNegFive)).absNorm < 3 := by exact_mod_cast hlt
  have hne := Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  exact ⟨I, hclass, by omega⟩

end Masullo
