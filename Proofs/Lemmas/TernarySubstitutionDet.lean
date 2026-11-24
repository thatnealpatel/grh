module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Determinant of ternary monomial substitution

Source: `2097cfaa:.godel/alice/cheap-filter-occupancy.md:17–29`.
Scope: the ordinary homogeneous degree-nine monomial coefficient matrix for `P(X) ↦ P(TX)`
over `ℝ`, before the covolume step. No lattice or covolume assertion is made here.
Owning check session: `01a20ca9-0415-7de3-a7c2-ad7d2c76dee0`.
-/

open scoped BigOperators
open MvPolynomial

namespace TernarySubstitution

/-- Exponent triples of total degree `n`, with one index per ordinary monomial. -/
public abbrev MonomialIndex (n : ℕ) := ↥(Finset.Nat.antidiagonalTuple 3 n)

/-- The finitely supported exponent of an ordinary monomial. -/
@[expose] public noncomputable def exponent {n : ℕ} (a : MonomialIndex n) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a.val

@[simp] public theorem exponent_apply {n : ℕ} (a : MonomialIndex n) (i : Fin 3) :
    exponent a i = a.val i :=
  Finsupp.equivFunOnFinite_symm_apply_apply _ _

private theorem exponent_injective {n : ℕ} : Function.Injective (@exponent n) :=
  fun _ _ h ↦ Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h)

private theorem exponent_degree {n : ℕ} (a : MonomialIndex n) : (exponent a).degree = n := by
  rw [Finsupp.degree_eq_sum]
  simpa only [exponent_apply] using Finset.Nat.mem_antidiagonalTuple.mp a.property

/-- The substitution `P(X) ↦ P(TX)`, with `X` a column: it sends `X i` to
`∑ j, T i j * X j`. -/
@[expose] public noncomputable def substitution (T : Matrix (Fin 3) (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  aeval fun i ↦ ∑ j, C (T i j) * X j

@[simp] public theorem substitution_X (T : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    substitution T (X i) = ∑ j, C (T i j) * X j :=
  aeval_X _ _

private theorem substitution_C (T : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) :
    substitution T (C r) = C r := by
  rw [← algebraMap_eq, AlgHom.commutes]

/-- In the convention `P ↦ P(TX)`, composition reverses matrix multiplication. -/
public theorem substitution_mul (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    substitution (A * B) = (substitution B).comp (substitution A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, substitution_X, map_sum, map_mul, substitution_C,
    Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

private theorem homogeneous_substitution {n : ℕ} (T : Matrix (Fin 3) (Fin 3) ℝ)
    {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous n) :
    (substitution T p).IsHomogeneous n := by
  simpa only [substitution, one_mul] using hp.aeval (fun i ↦ ∑ j, C (T i j) * X j)
    (n := 1) (fun i ↦ IsHomogeneous.sum _ _ _ fun j _ ↦ (isHomogeneous_X ℝ j).C_mul _)

/-- A homogeneous polynomial is reconstructed from its coefficients in the ordinary monomials,
with coefficient one on each basis monomial and no multinomial normalization. -/
public theorem sum_monomial_coeff {n : ℕ} {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous n) :
    (∑ a : MonomialIndex n, monomial (exponent a) (p.coeff (exponent a))) = p := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_sum]
  by_cases hd : d ∈ p.support
  · have hdeg : d.degree = n := (hp.degree_eq_sum_deg_support hd).symm
    let a : MonomialIndex n := ⟨d, Finset.Nat.mem_antidiagonalTuple.mpr
      ((Finsupp.degree_eq_sum d).symm.trans hdeg)⟩
    have ha : exponent a = d := Finsupp.equivFunOnFinite.symm_apply_apply d
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
    · simp [ha]
    · intro b _ hba
      have hb : exponent b ≠ d := fun h ↦ hba (exponent_injective (h.trans ha.symm))
      simp [coeff_monomial, hb]
  · have hz : p.coeff d = 0 := MvPolynomial.notMem_support_iff.mp hd
    rw [hz]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : exponent a = d <;> simp [coeff_monomial, ha, hz]

/-- The degree-`n` coefficient matrix of `P(X) ↦ P(TX)`. Column `b` is the image of
`X^b` in the ordinary monomial basis; row `a` extracts the coefficient of `X^a`. -/
@[expose] public noncomputable def substitutionMatrix (n : ℕ) (T : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (MonomialIndex n) (MonomialIndex n) ℝ :=
  fun a b ↦ (substitution T (monomial (exponent b) 1)).coeff (exponent a)

/-- The coefficient matrix multiplies the column of ordinary coefficients of a homogeneous
polynomial to give the coefficients after substitution. -/
public theorem coeff_substitution {n : ℕ} (T : Matrix (Fin 3) (Fin 3) ℝ)
    {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous n) (a : MonomialIndex n) :
    (substitution T p).coeff (exponent a) =
      ∑ b : MonomialIndex n, substitutionMatrix n T a b * p.coeff (exponent b) := by
  conv_lhs => rw [← sum_monomial_coeff hp]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  have h : monomial (exponent b) (p.coeff (exponent b)) =
      C (p.coeff (exponent b)) * monomial (exponent b) 1 := by simp [C_mul_monomial]
  rw [h, map_mul, substitution_C, coeff_C_mul, mul_comm]
  rfl

/-- In the column convention, the matrix of `P ↦ P((AB)X)` is the matrix for `B`
times the matrix for `A`. -/
public theorem substitutionMatrix_mul (n : ℕ) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    substitutionMatrix n (A * B) = substitutionMatrix n B * substitutionMatrix n A := by
  ext a b
  have h := homogeneous_substitution A (isHomogeneous_monomial (1 : ℝ) (exponent_degree b))
  simpa only [substitutionMatrix, substitution_mul, AlgHom.comp_apply, Matrix.mul_apply] using
    coeff_substitution B h a

private theorem substitution_diagonal_X (D : Fin 3 → ℝ) (i : Fin 3) :
    substitution (Matrix.diagonal D) (X i) = C (D i) * X i := by
  simp [substitution_X, Matrix.diagonal_apply, apply_ite C, ite_mul]

private theorem substitution_diagonal_monomial (D : Fin 3 → ℝ) (d : Fin 3 →₀ ℕ) :
    substitution (Matrix.diagonal D) (monomial d 1) = monomial d (∏ i, D i ^ d i) := by
  calc
    substitution (Matrix.diagonal D) (monomial d 1) =
        ∏ i, (C (D i) * X i) ^ d i := by
      rw [substitution, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype]
      · refine Finset.prod_congr rfl fun i _ ↦ ?_
        have h := substitution_diagonal_X D i
        rw [substitution_X] at h
        rw [h]
      · intro i
        exact pow_zero _
    _ = monomial d (∏ i, D i ^ d i) := by
      simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
      rw [monomial_eq, Finsupp.prod_fintype]
      intro i
      exact pow_zero _

private theorem substitutionMatrix_diagonal (n : ℕ) (D : Fin 3 → ℝ) :
    substitutionMatrix n (Matrix.diagonal D) =
      Matrix.diagonal (fun a : MonomialIndex n ↦ ∏ i, D i ^ a.val i) := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [substitutionMatrix, substitution_diagonal_monomial, coeff_monomial]
  · have h' : exponent b ≠ exponent a := fun e ↦ h (exponent_injective e.symm)
    simp [substitutionMatrix, substitution_diagonal_monomial, coeff_monomial, h', h]

private theorem substitution_transvection_X (i j : Fin 3) (c : ℝ) (k : Fin 3) :
    substitution (Matrix.transvection i j c) (X k) =
      if k = i then X i + C c * X j else X k := by
  simp only [substitution_X, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add, add_mul, Finset.sum_add_distrib, apply_ite C, ite_mul,
    map_one, one_mul, map_zero, zero_mul]
  by_cases h : k = i
  · subst k
    simp
  · simp [h, Ne.symm h]

private theorem substitution_transvection_erase (i j : Fin 3) (c : ℝ) (d : Fin 3 →₀ ℕ) :
    substitution (Matrix.transvection i j c) (monomial (d.erase i) 1) =
      monomial (d.erase i) 1 := by
  rw [substitution, aeval_monomial, map_one, one_mul, ← prod_X_pow_eq_monomial]
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [Finsupp.support_erase] at hk
  have hk' := (Finset.mem_erase.mp hk).1
  have h := substitution_transvection_X i j c k
  rw [substitution_X, ite_eq_right hk'] at h
  exact congrArg (fun p : MvPolynomial (Fin 3) ℝ ↦ p ^ (d.erase i) k) h

-- The summand at k = d i is the original monomial; all other summands lower exponent i.
private theorem substitution_transvection_monomial (i j : Fin 3) (c : ℝ) (d : Fin 3 →₀ ℕ) :
    substitution (Matrix.transvection i j c) (monomial d 1) =
      ∑ k ∈ Finset.range (d i + 1),
        monomial (d.erase i + Finsupp.single i k + Finsupp.single j (d i - k))
          (c ^ (d i - k) * ((d i).choose k : ℝ)) := by
  have hfactor : monomial d (1 : ℝ) = monomial (d.erase i) 1 * X i ^ d i := by
    rw [X_pow_eq_monomial, monomial_mul_monomial, Finsupp.erase_add_single, one_mul]
  rw [hfactor, map_mul, substitution_transvection_erase, map_pow, substitution_transvection_X,
    ite_eq_left rfl, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow, ← map_pow, C_mul_X_pow_eq_monomial, X_pow_eq_monomial, ← map_natCast C]
  rw [← mul_assoc, ← mul_assoc, monomial_mul_monomial, monomial_mul_monomial, one_mul, one_mul,
    mul_comm _ (C _), C_mul_monomial, mul_comm]

private theorem coeff_substitution_transvection_of_le (i j : Fin 3) (hij : i ≠ j)
    (c : ℝ) (d e : Fin 3 →₀ ℕ) (hde : d i ≤ e i) :
    (substitution (Matrix.transvection i j c) (monomial d 1)).coeff e =
      (monomial d 1 : MvPolynomial (Fin 3) ℝ).coeff e := by
  rw [substitution_transvection_monomial, coeff_sum, Finset.sum_range_succ]
  have hzero : (∑ k ∈ Finset.range (d i),
      (monomial (d.erase i + Finsupp.single i k + Finsupp.single j (d i - k))
        (c ^ (d i - k) * ((d i).choose k : ℝ))).coeff e) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hne : d.erase i + Finsupp.single i k + Finsupp.single j (d i - k) ≠ e := by
      intro he
      have hki : k = e i := by
        simpa [Finsupp.single_eq_of_ne hij] using DFunLike.congr_fun he i
      exact (Nat.not_lt_of_ge (hki.symm ▸ hde)) (Finset.mem_range.mp hk)
    rw [coeff_monomial, ite_eq_right hne]
  rw [hzero, zero_add]
  simp [Finsupp.erase_add_single]

private theorem det_substitutionMatrix_transvection (n : ℕ) (i j : Fin 3)
    (hij : i ≠ j) (c : ℝ) : (substitutionMatrix n (Matrix.transvection i j c)).det = 1 := by
  classical
  let M := substitutionMatrix n (Matrix.transvection i j c)
  let block : MonomialIndex n → ℕ := fun a ↦ exponent a i
  have htri : M.BlockTriangular block := by
    intro a b h
    have hne : exponent b ≠ exponent a := fun e ↦ (ne_of_lt h) (DFunLike.congr_fun e i)
    exact (coeff_substitution_transvection_of_le i j hij c _ _ h.le).trans (by
      simp [coeff_monomial, hne])
  rw [htri.det]
  have hblock (k : ℕ) : M.toSquareBlock block k = 1 := by
    ext a b
    have hab : exponent b.val i ≤ exponent a.val i := (b.property.trans a.property.symm).le
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    change (substitution (Matrix.transvection i j c) (monomial (exponent b.val) 1)).coeff
      (exponent a.val) = _
    rw [coeff_substitution_transvection_of_le i j hij c _ _ hab, coeff_monomial]
    have heq : exponent b.val = exponent a.val ↔ a = b :=
      ⟨fun h ↦ Subtype.ext (exponent_injective h.symm), fun h ↦ by subst b; rfl⟩
    simp only [heq]
  simp [hblock]

-- Sum the exponents over the triples of total degree 9, by kernel reduction.
set_option maxRecDepth 8192 in
private theorem exponent_sum_nine (i : Fin 3) :
    (∑ a : MonomialIndex 9, a.val i) = 165 := by
  rw [← Finset.sum_subtype _ (fun _ ↦ Iff.rfl) (fun a : Fin 3 → ℕ ↦ a i)]
  fin_cases i <;> decide

private theorem det_substitutionMatrix_diagonal_nine (D : Fin 3 → ℝ) :
    (substitutionMatrix 9 (Matrix.diagonal D)).det = (Matrix.diagonal D).det ^ 165 := by
  rw [substitutionMatrix_diagonal, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum, exponent_sum_nine, Finset.prod_pow]

/-- The signed degree-nine substitution determinant, in the ordinary monomial basis.
The identity holds also for singular matrices. -/
public theorem det_substitutionMatrix_nine (T : Matrix (Fin 3) (Fin 3) ℝ) :
    (substitutionMatrix 9 T).det = T.det ^ 165 := by
  apply Matrix.diagonal_transvection_induction
    (fun M ↦ (substitutionMatrix 9 M).det = M.det ^ 165) T
  · intro D _
    exact det_substitutionMatrix_diagonal_nine D
  · rintro ⟨i, j, hij, c⟩
    rw [Matrix.TransvectionStruct.det, one_pow]
    exact det_substitutionMatrix_transvection 9 i j hij c
  · intro A B hA hB
    rw [substitutionMatrix_mul, Matrix.det_mul, Matrix.det_mul, hA, hB, mul_pow, mul_comm]

/-- The absolute determinant at degree nine, with `165 = Nat.choose (9 + 2) 3`. -/
public theorem abs_det_substitutionMatrix_nine (T : Matrix (Fin 3) (Fin 3) ℝ) :
    |(substitutionMatrix 9 T).det| = |T.det| ^ Nat.choose (9 + 2) 3 := by
  rw [det_substitutionMatrix_nine, abs_pow]
  rfl

end TernarySubstitution
