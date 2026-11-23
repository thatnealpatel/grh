module

public import Theorems.IdealClassTwoClasses
public import Mathlib.NumberTheory.NumberField.DedekindZeta

import Mathlib.Analysis.Real.Pi.Bounds

/-! # The unique complex place and zeta residue of ℚ(√-5) -/

open NumberField NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem (w₀)

namespace Masullo

/-- Every infinite place of `ℚ(√-5)` is complex. -/
public theorem qSqrtNegFive_infinitePlace_isComplex (w : InfinitePlace QSqrtNegFive) :
    w.IsComplex := by
  classical
  have h : IsEmpty {v : InfinitePlace QSqrtNegFive // v.IsReal} :=
    Fintype.card_eq_zero_iff.mp qSqrtNegFive_nrRealPlaces
  exact not_isReal_iff_isComplex.mp (fun hw ↦ h.false ⟨w, hw⟩)

/-- The signature `(0, 1)` gives a unique infinite place. -/
public instance qSqrtNegFive_infinitePlace_subsingleton : Subsingleton (InfinitePlace QSqrtNegFive) :=
  Fintype.card_le_one_iff_subsingleton.mp (by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, qSqrtNegFive_nrRealPlaces,
      qSqrtNegFive_nrComplexPlaces, zero_add])

/-- The trivial class and the class of the prime over two are distinct and exhaust the class group. -/
public theorem qSqrtNegFive_classNumber : classNumber QSqrtNegFive = 2 := by
  classical
  unfold classNumber Fintype.card
  refine Finset.card_eq_two.mpr ⟨1, qSqrtNegFivePlaceClass qSqrtNegFivePrimeTwo,
    qSqrtNegFivePrimeTwo_class_ne_one.symm, ?_⟩
  ext c
  simpa only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton] using
    qSqrtNegFive_class_eq_one_or_primeTwo c

private theorem qSqrtNegFive_unit_eq_one_or_neg_one (u : (𝓞 QSqrtNegFive)ˣ) :
    u = 1 ∨ u = -1 := by
  let a := qSqrtNegFiveIntegersEquiv (u : 𝓞 QSqrtNegFive)
  have hn := qSqrtNegFive_span_absNorm_eq_coordinates (u : 𝓞 QSqrtNegFive)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at hn
  change 1 = a.re ^ 2 + 5 * a.im ^ 2 at hn
  have hy : a.im = 0 := by
    by_contra h
    have hpos := sq_pos_of_ne_zero h
    have hle : 1 ≤ a.im ^ 2 := by omega
    nlinarith only [hn, hle, sq_nonneg a.re]
  have hx : a.re ^ 2 = 1 := by simpa [hy] using hn.symm
  rcases sq_eq_one_iff.mp hx with hx | hx
  · left
    apply _root_.Units.ext
    apply qSqrtNegFiveIntegersEquiv.injective
    rw [_root_.Units.val_one, map_one]
    change a = 1
    exact QuadraticAlgebra.ext (by simpa only [QuadraticAlgebra.re_one] using hx)
      (by simpa only [QuadraticAlgebra.im_one] using hy)
  · right
    apply _root_.Units.ext
    apply qSqrtNegFiveIntegersEquiv.injective
    rw [_root_.Units.val_neg, _root_.Units.val_one, map_neg, map_one]
    change a = -1
    exact QuadraticAlgebra.ext
      (by simpa only [QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one] using hx)
      (by simpa only [QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one, neg_zero] using hy)

/-- The torsion subgroup of the integral units of `ℚ(√-5)` consists of `±1`. -/
public theorem qSqrtNegFive_torsionOrder : NumberField.Units.torsionOrder QSqrtNegFive = 2 := by
  classical
  let := Fintype.ofFinite (NumberField.Units.torsion QSqrtNegFive)
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.mpr ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], ?_⟩
  ext u
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton,
    ← Subtype.val_inj]
  exact qSqrtNegFive_unit_eq_one_or_neg_one u.val

/-- The rank-zero unit regulator of `ℚ(√-5)` is the empty determinant. -/
public theorem qSqrtNegFive_regulator : NumberField.Units.regulator QSqrtNegFive = 1 := by
  classical
  rw [NumberField.Units.regulator_eq_det']
  let : IsEmpty {w : InfinitePlace QSqrtNegFive // w ≠ w₀} :=
    ⟨fun w ↦ w.property (Subsingleton.elim _ _)⟩
  simp only [Matrix.det_isEmpty, abs_one]

/-- The Dedekind zeta residue (the arithmetic volume factor) of `ℚ(√-5)`. -/
public theorem dedekindZeta_residue_qSqrtNegFive :
    NumberField.dedekindZeta_residue QSqrtNegFive = Real.pi / Real.sqrt 5 := by
  have hfour : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hs : Real.sqrt 20 = 2 * Real.sqrt 5 := by
    rw [show (20 : ℝ) = 4 * 5 by norm_num, Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), hfour]
  rw [dedekindZeta_residue_def, qSqrtNegFive_nrRealPlaces, qSqrtNegFive_nrComplexPlaces,
    qSqrtNegFive_regulator, qSqrtNegFive_classNumber, qSqrtNegFive_torsionOrder, qSqrtNegFive_discr]
  norm_num only [pow_zero, pow_one, one_mul, mul_one, Nat.cast_ofNat, Int.cast_neg,
    Int.cast_ofNat, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 20), hs]
  calc
    _ = 4 * Real.pi / (4 * Real.sqrt 5) := by ring
    _ = _ := mul_div_mul_left _ _ (by norm_num)

/-- The arithmetic volume factor for `ℚ(√-5)` is not one. -/
public theorem dedekindZeta_residue_qSqrtNegFive_ne_one :
    NumberField.dedekindZeta_residue QSqrtNegFive ≠ 1 := by
  rw [dedekindZeta_residue_qSqrtNegFive]
  have hs : Real.sqrt 5 < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  apply ne_of_gt
  apply (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))).2
  simpa only [one_mul] using hs.trans Real.pi_gt_three

end Masullo
