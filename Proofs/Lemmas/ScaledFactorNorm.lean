module

public import Lemmas.EvaluationKernelCovolume
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# A uniform scaled coefficient bound for a factor of a degree-nine form

Source: `710dec242ab2:.godel/alice/cheap-filter-occupancy.md:19–35`, used at 37–60.
Scan pin: `f8c831a3e7afbcdd3488a3ad51afa8cea6e9fc99` (unchanged through `c3cb30e1`).
Scope: given the factorization, transfer the degree-nine norm bound to the same factor
in ordinary scaled-box coordinates. No divisibility, point count, or price assertion.
Owning check session: `01a20e06-2914-72b5-a0f3-35d7c4cdf9e8`.
-/

@[expose] public section

noncomputable section

open MvPolynomial Module TernarySubstitution EvaluationKernelCovolume
open scoped Matrix

namespace ScaledFactorNorm

abbrev Form := MvPolynomial (Fin 3) ℝ
abbrev Coeff (n : ℕ) := EuclideanSpace ℝ (MonomialIndex n)

/-- Ordinary monomial coefficients in the orthonormal scaled-box point coordinates. -/
def coefficients (n : ℕ) (P : Form) : Coeff n :=
  WithLp.toLp 2 fun a ↦ P.coeff (exponent a)

/-- Synthesize a form with no normalization of the ordinary monomials. In degree nine
this takes exactly the `Coeff9` returned by `EvaluationKernelShortForm.exists_short_form`. -/
def polynomial (n : ℕ) (v : Coeff n) : Form :=
  ∑ a : MonomialIndex n, monomial (exponent a) (v a)

private theorem exponent_degree {n : ℕ} (a : MonomialIndex n) : (exponent a).degree = n := by
  rw [Finsupp.degree_eq_sum]
  simpa only [exponent_apply] using Finset.Nat.mem_antidiagonalTuple.mp a.property

private theorem exponent_injective (n : ℕ) : Function.Injective (@exponent n) :=
  fun _ _ h ↦ Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h)

@[simp] theorem polynomial_isHomogeneous (n : ℕ) (v : Coeff n) :
    (polynomial n v).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ fun a _ ↦ isHomogeneous_monomial _ (exponent_degree a)

@[simp] theorem polynomial_coefficients {n : ℕ} {P : Form} (hP : P.IsHomogeneous n) :
    polynomial n (coefficients n P) = P := sum_monomial_coeff hP

@[simp] theorem coefficients_polynomial (n : ℕ) (v : Coeff n) :
    coefficients n (polynomial n v) = v := by
  classical
  ext a
  change (∑ b : MonomialIndex n, monomial (exponent b) (v b)).coeff (exponent a) = v a
  rw [coeff_sum, Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · simp [coeff_monomial]
  · intro b _ hba
    rw [coeff_monomial, ite_eq_right (fun h ↦ hba (exponent_injective n h))]

/-- Same norm as in the degree-nine evaluation kernel when `P` is represented there. -/
theorem norm_polynomial9 (v : Coeff9) : ‖coefficients 9 (polynomial 9 v)‖ = ‖v‖ := by
  rw [coefficients_polynomial]

private theorem polynomial_smul (n : ℕ) (r : ℝ) (v : Coeff n) :
    polynomial n (r • v) = C r * polynomial n v := by
  simp only [polynomial, Finset.mul_sum, C_mul_monomial, PiLp.smul_apply, smul_eq_mul]

private theorem coefficients_C_mul (n : ℕ) (r : ℝ) (P : Form) :
    coefficients n (C r * P) = r • coefficients n P := by
  ext a
  exact coeff_C_mul _ _ _

private theorem eval_monomial_sum {n : ℕ} (v : Coeff n) (x : Fin 3 → ℝ) :
    eval x (polynomial n v) = ∑ a : MonomialIndex n, v a * ∏ j, x j ^ a.val j := by
  rw [polynomial, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [exponent_apply]

/-- Synthesis also preserves the degree-nine evaluation used by the short-form lemma. -/
theorem eval_polynomial9 {ι : Type*} [Fintype ι] (p : ι → Fin 3 → ℝ) (v : Coeff9) (i : ι) :
    eval (p i) (polynomial 9 v) = evaluation9 p v i := by
  rw [eval_monomial_sum, evaluation9_apply]
  simp only [mul_comm]

private theorem eval_substitution (T : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ)
    (P : Form) : eval x (substitution T P) = eval (T.mulVec x) P := by
  have h : (aeval x).comp (substitution T) = aeval (R := ℝ) (T.mulVec x) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Matrix.mulVec, dotProduct]
  exact DFunLike.congr_fun h P

private theorem isHomogeneous_substitution {n : ℕ} (T : Matrix (Fin 3) (Fin 3) ℝ)
    {P : Form} (hP : P.IsHomogeneous n) : (substitution T P).IsHomogeneous n := by
  simpa only [substitution, one_mul] using hP.aeval (fun i ↦ ∑ j, C (T i j) * X j)
    (n := 1) (fun i ↦ IsHomogeneous.sum _ _ _ fun j _ ↦ (isHomogeneous_X ℝ j).C_mul _)

private theorem substitution_one : substitution (1 : Matrix (Fin 3) (Fin 3) ℝ) =
    AlgHom.id ℝ Form := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [Matrix.one_apply, apply_ite C, ite_mul]

private theorem substitution_injective (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : IsUnit T.det) :
    Function.Injective (substitution T) := by
  have h : (substitution T⁻¹).comp (substitution T) = AlgHom.id ℝ Form := by
    rw [← substitution_mul, Matrix.mul_nonsing_inv _ hT, substitution_one]
  have hinv : Function.LeftInverse (substitution T⁻¹) (substitution T) :=
    fun P ↦ DFunLike.congr_fun h P
  exact hinv.injective

/-- The cofactor, in scaled coordinates, is the pullback of an integer polynomial
in the chosen lattice basis. The real degree is imposed separately on the actual form. -/
def IntegralIn (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (P : Form) : Prop :=
  ∃ Q : MvPolynomial (Fin 3) ℤ,
    P = substitution (latticeCoordinates b) (MvPolynomial.map (Int.castRingHom ℝ) Q)

private theorem continuous_product_coefficients (m n : ℕ) :
    Continuous fun z : Coeff m × Coeff n ↦
      coefficients (m + n) (polynomial m z.1 * polynomial n z.2) := by
  classical
  apply (PiLp.continuous_toLp 2 (fun _ : MonomialIndex (m + n) ↦ ℝ)).comp
  apply continuous_pi
  intro c
  simp only [polynomial, Finset.sum_mul, Finset.mul_sum, coeff_sum, monomial_mul_monomial,
    coeff_monomial]
  apply continuous_finsetSum _
  intro b _
  apply continuous_finsetSum _
  intro a _
  split_ifs
  · have ha : Continuous fun z : Coeff m × Coeff n ↦ z.1 a :=
      (PiLp.continuous_apply 2 (fun _ : MonomialIndex m ↦ ℝ) a).comp continuous_fst
    have hb : Continuous fun z : Coeff m × Coeff n ↦ z.2 b :=
      (PiLp.continuous_apply 2 (fun _ : MonomialIndex n ↦ ℝ) b).comp continuous_snd
    exact ha.mul hb
  · exact continuous_const

private def purePower (n : ℕ) : MonomialIndex n :=
  ⟨fun j ↦ if j = 0 then n else 0, Finset.Nat.mem_antidiagonalTuple.mpr (by simp)⟩

private theorem coeff_sphere_nonempty (n : ℕ) : (Metric.sphere (0 : Coeff n) 1).Nonempty := by
  refine ⟨EuclideanSpace.basisFun (MonomialIndex n) ℝ (purePower n), ?_⟩
  rw [Metric.mem_sphere, dist_zero_right]
  exact (EuclideanSpace.basisFun (MonomialIndex n) ℝ).orthonormal.norm_eq_one _

/-- On two fixed-degree coefficient spheres, the product norm has a positive minimum. -/
private theorem exists_mul_lower_bound (m n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ G B : Form, G.IsHomogeneous m → B.IsHomogeneous n →
      c * (‖coefficients m G‖ * ‖coefficients n B‖) ≤ ‖coefficients (m + n) (G * B)‖ := by
  let S := Metric.sphere (0 : Coeff m) 1 ×ˢ Metric.sphere (0 : Coeff n) 1
  let f (z : Coeff m × Coeff n) := ‖coefficients (m + n) (polynomial m z.1 * polynomial n z.2)‖
  have hS : IsCompact S := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn
    ((coeff_sphere_nonempty m).prod (coeff_sphere_nonempty n))
    (continuous_product_coefficients m n).norm.continuousOn
  change z.1 ∈ Metric.sphere (0 : Coeff m) 1 ∧ z.2 ∈ Metric.sphere (0 : Coeff n) 1 at hz
  have nonzero (k : ℕ) {v : Coeff k} (hv : v ∈ Metric.sphere (0 : Coeff k) 1) :
      polynomial k v ≠ 0 := by
    intro h
    have h0 : v = 0 := by
      rw [← coefficients_polynomial k v, h]
      ext a
      simp [coefficients]
    simp [h0] at hv
  have hf : 0 < f z := by
    apply norm_pos_iff.mpr
    intro h
    have hh := (polynomial_isHomogeneous m z.1).mul (polynomial_isHomogeneous n z.2)
    have hp := polynomial_coefficients hh
    rw [h] at hp
    exact mul_ne_zero (nonzero m hz.1) (nonzero n hz.2) (by simpa [polynomial] using hp.symm)
  refine ⟨f z, hf, ?_⟩
  intro G B hG hB
  let u := coefficients m G
  let v := coefficients n B
  change f z * (‖u‖ * ‖v‖) ≤ _
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := (‖u‖⁻¹ • u, ‖v‖⁻¹ • v)
  have hw : w ∈ S := by
    change ‖u‖⁻¹ • u ∈ Metric.sphere (0 : Coeff m) 1 ∧
      ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Coeff n) 1
    simp [norm_smul, hu'.ne', hv'.ne']
  have hle : f z ≤ f w := hmin hw
  have hform : polynomial m w.1 * polynomial n w.2 = C (‖u‖⁻¹ * ‖v‖⁻¹) * (G * B) := by
    change polynomial m (‖u‖⁻¹ • u) * polynomial n (‖v‖⁻¹ • v) = _
    rw [polynomial_smul, polynomial_smul, polynomial_coefficients hG,
      polynomial_coefficients hB, map_mul]
    ac_rfl
  have hnorm : f w = (‖u‖ * ‖v‖)⁻¹ * ‖coefficients (m + n) (G * B)‖ := by
    change ‖coefficients (m + n) (polynomial m w.1 * polynomial n w.2)‖ = _
    rw [hform, coefficients_C_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), mul_inv]
  rw [hnorm] at hle
  exact (le_div_iff₀ (mul_pos hu' hv')).mp (by simpa only [div_eq_mul_inv, mul_comm] using hle)

private theorem IntegralIn.eval_eq_int {b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    {P : Form} (hP : IntegralIn b P) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ Submodule.span ℤ (Set.range b)) : ∃ z : ℤ, (z : ℝ) = eval x.ofLp P := by
  obtain ⟨Q, rfl⟩ := hP
  choose z hz using (b.mem_span_iff_repr_mem ℤ x).mp hx
  have hcoord : (latticeCoordinates b).mulVec x.ofLp = fun i ↦ (z i : ℝ) := by
    funext i
    rw [show ((latticeCoordinates b).mulVec x.ofLp) i = b.repr x i from
      congrFun ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix_mulVec_repr b x) i, ← hz i]
    rfl
  refine ⟨eval z Q, ?_⟩
  rw [eval_substitution, hcoord, eval_map]
  exact MvPolynomial.hom_eval₂ Q (RingHom.id ℤ) (Int.castRingHom ℝ) z

private theorem sum_zsmul_apply (p : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (z : Fin 3 → ℤ) (i : Fin 3) : (∑ j, z j • p j) i = ∑ j, (z j : ℝ) * p j i := by
  simp only [← Int.cast_smul_eq_zsmul ℝ]
  let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := PiLp.projₗ 2 (fun _ : Fin 3 ↦ ℝ) i
  change L (∑ j, (z j : ℝ) • p j) = ∑ j, (z j : ℝ) • L (p j)
  simp only [map_sum, map_smul]

/-- The grid uses integer combinations of the actual points. Nonsingularity is only
required over `ℝ`, so the points need not generate the original lattice over `ℤ`. -/
private theorem exists_grid_evaluation {n : ℕ} (hn : n ≤ 9) {P : Form}
    (hP : P.IsHomogeneous n) (hP0 : P ≠ 0) (R : ℝ)
    (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (p : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hi : LinearIndependent ℝ p) (hm : ∀ j, p j ∈ Submodule.span ℤ (Set.range b))
    (hp : ∀ j i, |p j i| ≤ R) :
    ∃ x : EuclideanSpace ℝ (Fin 3), x ∈ Submodule.span ℤ (Set.range b) ∧
      (∀ i, |x i| ≤ 27 * R) ∧ eval x.ofLp P ≠ 0 := by
  let T : Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦ p j i
  have hcol : LinearIndependent ℝ T.col :=
    hi.map' (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective)
  have hT : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (Matrix.mulVec_injective_iff.mpr hcol))
  let Q := substitution T P
  have hQ : Q.IsHomogeneous n := isHomogeneous_substitution T hP
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hP0
    exact substitution_injective T hT (h.trans (map_zero (substitution T)).symm)
  let S : Finset ℝ := (Finset.range 10).map (Nat.castEmbedding (R := ℝ))
  have hcard : S.card = 10 := by simp [S]
  have hdeg (i : Fin 3) : Q.degreeOf i < S.card := by
    rw [hcard]
    exact (degreeOf_le_totalDegree Q i).trans_lt (hQ.totalDegree_le.trans_lt (by omega))
  have hsome : ∃ t : Fin 3 → ℝ, (∀ i, t i ∈ S) ∧ eval t Q ≠ 0 := by
    by_contra! h
    exact hQ0 (eq_zero_of_eval_zero_at_prod_finset Q (fun _ ↦ S) hdeg h)
  obtain ⟨t, ht, heval⟩ := hsome
  have hz' (j : Fin 3) : ∃ k : ℕ, k < 10 ∧ (k : ℝ) = t j := by
    obtain ⟨k, hk, he⟩ := Finset.mem_map.mp (ht j)
    exact ⟨k, Finset.mem_range.mp hk, he⟩
  choose k hk hkt using hz'
  let z (j : Fin 3) : ℤ := k j
  let x : EuclideanSpace ℝ (Fin 3) := ∑ j, z j • p j
  have hx (i : Fin 3) : x i = ∑ j, t j * p j i := by
    rw [sum_zsmul_apply]
    simp only [z, Int.cast_natCast, hkt]
  refine ⟨x, Submodule.sum_mem _ (fun j _ ↦ Submodule.smul_mem _ _ (hm j)), ?_, ?_⟩
  · intro i
    have ht' (j : Fin 3) : |t j| ≤ 9 := by
      rw [← hkt, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (show k j ≤ 9 by have := hk j; omega)
    calc
      |x i| ≤ ∑ j, |t j * p j i| := by rw [hx]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, 9 * R := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (ht' j) (hp j i) (abs_nonneg _) (by norm_num)
      _ = 27 * R := by simp [nsmul_eq_mul]; ring
  · have he : T.mulVec t = x.ofLp := by
      funext i
      rw [hx]
      simp only [Matrix.mulVec, dotProduct, T, mul_comm]
    rw [eval_substitution, he] at heval
    exact heval

private theorem eval_bound {n : ℕ} {P : Form} (hP : P.IsHomogeneous n)
    (x : Fin 3 → ℝ) (K : ℝ) (hx : ∀ j, |x j| ≤ K) :
    |eval x P| ≤ (Fintype.card (MonomialIndex n) : ℝ) * K ^ n * ‖coefficients n P‖ := by
  let v := coefficients n P
  have he : eval x P = ∑ a : MonomialIndex n, v a * ∏ j, x j ^ a.val j :=
    (congrArg (eval x) (polynomial_coefficients hP).symm).trans (eval_monomial_sum v x)
  rw [he]
  calc
    _ ≤ ∑ a : MonomialIndex n, |v a * ∏ j, x j ^ a.val j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : MonomialIndex n, ‖v‖ * K ^ n := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v a)
        _ (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _) (norm_nonneg v)
      simp only [abs_pow]
      calc
        _ ≤ ∏ j, K ^ a.val j := Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
          (fun j _ ↦ pow_le_pow_left₀ (abs_nonneg _) (hx j) _)
        _ = K ^ n := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.Nat.mem_antidiagonalTuple.mp a.property]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Given `A = G * B` with `A ≠ 0`, the actual homogeneous factor `G` has scaled
Euclidean coefficient norm at most `C * ‖A‖₂`. The degrees of `G` and `B` imply that
`A` is homogeneous of degree nine. The constant depends only on the scaled coordinate box;
`p` consists of three independent points of the lattice but need not be a lattice basis. -/
theorem exists_uniform_factor_norm_bound (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e : ℕ), 2 ≤ e → e ≤ 5 →
      ∀ (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
        (p : Fin 3 → EuclideanSpace ℝ (Fin 3)),
        LinearIndependent ℝ p → (∀ j, p j ∈ Submodule.span ℤ (Set.range b)) →
        (∀ j i, |p j i| ≤ R) →
        ∀ A G B : Form, A ≠ 0 → A = G * B →
          G.IsHomogeneous e → B.IsHomogeneous (9 - e) → IntegralIn b B →
          ‖coefficients e G‖ ≤ C * ‖coefficients 9 A‖ := by
  let K : ℝ := max 1 (27 * R)
  let D (e : ℕ) : ℝ := (Fintype.card (MonomialIndex (9 - e)) : ℝ) * K ^ (9 - e)
  let c (e : ℕ) : ℝ := (exists_mul_lower_bound e (9 - e)).choose
  have hc (e : ℕ) : 0 < c e := (exists_mul_lower_bound e (9 - e)).choose_spec.1
  have hD (e : ℕ) : 0 ≤ D e :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  let M (e : ℕ) := D e / c e
  let t : Finset ℕ := Finset.Icc 2 5
  have ht : t.Nonempty := ⟨2, by simp [t]⟩
  obtain ⟨e₀, _, hmax⟩ := t.exists_max_image M ht
  refine ⟨max 1 (M e₀), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro e he he' b p hi hp hbox A G B hA hAB hG hB hInt
  have hsum : e + (9 - e) = 9 := by omega
  have hB0 : B ≠ 0 := by
    intro hb
    exact hA (by rw [hAB, hb, mul_zero])
  obtain ⟨x, hx, hxbox, heval⟩ := exists_grid_evaluation (Nat.sub_le 9 e) hB hB0 R b p
    hi hp hbox
  obtain ⟨z, hz⟩ := hInt.eval_eq_int hx
  have hz0 : z ≠ 0 := by
    intro h
    exact heval (by simpa [h] using hz.symm)
  have hval : 1 ≤ |eval x.ofLp B| := by
    rw [← hz, ← Int.cast_abs, ← Int.cast_one (R := ℝ)]
    exact_mod_cast Int.one_le_abs hz0
  have hcofactor : 1 ≤ D e * ‖coefficients (9 - e) B‖ :=
    hval.trans (eval_bound hB x.ofLp K (fun i ↦ (hxbox i).trans (le_max_right _ _)))
  have hmul := (exists_mul_lower_bound e (9 - e)).choose_spec.2 G B hG hB
  change c e * (‖coefficients e G‖ * ‖coefficients (9 - e) B‖) ≤ _ at hmul
  rw [hsum, ← hAB] at hmul
  have hmain : c e * ‖coefficients e G‖ ≤ D e * ‖coefficients 9 A‖ := by
    calc
      _ = (c e * ‖coefficients e G‖) * 1 := (mul_one _).symm
      _ ≤ (c e * ‖coefficients e G‖) * (D e * ‖coefficients (9 - e) B‖) :=
        mul_le_mul_of_nonneg_left hcofactor (mul_nonneg (hc e).le (norm_nonneg _))
      _ = D e * (c e * (‖coefficients e G‖ * ‖coefficients (9 - e) B‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmul (hD e)
  calc
    ‖coefficients e G‖ ≤ (D e * ‖coefficients 9 A‖) / c e :=
      (le_div_iff₀ (hc e)).mpr (by simpa only [mul_comm] using hmain)
    _ = M e * ‖coefficients 9 A‖ := by dsimp [M]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((hmax e (Finset.mem_Icc.mpr ⟨he, he'⟩)).trans (le_max_right _ _)) (norm_nonneg _)

end ScaledFactorNorm
