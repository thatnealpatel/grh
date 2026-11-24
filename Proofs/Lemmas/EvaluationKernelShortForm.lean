module

public import Lemmas.EvaluationKernelCovolume
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# A short integral form in the degree-nine evaluation kernel

Source: `710dec242ab2:.godel/alice/cheap-filter-occupancy.md:17–35`, route 2 at
scan pin `1730648dc8b4`. Scope: from bounded lattice representatives and evaluation
nullity at least fifteen, construct a nonzero integral degree-nine form vanishing on the
whole family, with the norm taken in the ordinary scaled-box monomial coefficients.
This does not derive the nullity from a component equation or bound its primitive factor.
Owner session: `01a20dea-9bff-7af6-950c-47bd0e521e1e`.
-/

@[expose] public section

noncomputable section

open EvaluationKernelCovolume MeasureTheory Module Submodule TernarySubstitution
open scoped Matrix

namespace EvaluationKernelShortForm

/-- Keep actual rows that span all the rows, so the kernel is unchanged even in rank zero. -/
private theorem exists_independent_subfamily {ι : Type*} [Fintype ι]
    (p : ι → EuclideanSpace ℝ (Fin 3)) :
    ∃ (k : ℕ) (e : Fin k → ι),
      Function.Surjective (evaluation9 (fun i j ↦ p (e i) j)) ∧
        (evaluation9 (fun i j ↦ p (e i) j)).ker = (evaluation9 (fun i j ↦ p i j)).ker := by
  classical
  let row (i : ι) (a : MonomialIndex 9) : ℝ := ∏ j, p i j ^ a.val j
  -- The selected row set can be empty; the same argument then gives a zero target.
  obtain ⟨s, hind, hmax⟩ := exists_maximal_linearIndepOn ℝ row
  let : Fintype s := Fintype.ofFinite s
  let f := (Fintype.equivFin s).symm
  let e : Fin (Fintype.card s) → ι := Subtype.val ∘ f
  let M : Matrix (Fin (Fintype.card s)) (MonomialIndex 9) ℝ := fun i ↦ row (e i)
  have hrow : LinearIndependent ℝ M.row := hind.comp f f.injective
  have hrestricted (A : Coeff9) (i : Fin (Fintype.card s)) :
      evaluation9 (fun j l ↦ p (e j) l) A i = M.mulVec A.ofLp i := evaluation9_apply _ _ _
  refine ⟨_, e, ?_, ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := hrow.mulVec_surjective y.ofLp
    refine ⟨WithLp.toLp 2 a, ?_⟩
    ext i
    exact (hrestricted _ i).trans (congrFun ha i)
  · apply le_antisymm
    · intro A hA
      let d := (dotProductBilin ℝ ℝ) A.ofLp
      have heval (i : ι) : d (row i) = evaluation9 (fun j l ↦ p j l) A i := by
        rw [evaluation9_apply]
        change (∑ a, A a * row i a) = _
        simp only [row, mul_comm]
      have hs : span ℝ (row '' s) ≤ d.ker := by
        apply span_le.mpr
        rintro _ ⟨j, hj, rfl⟩
        obtain ⟨i, hi⟩ := f.surjective ⟨j, hj⟩
        have hei : e i = j := congrArg Subtype.val hi
        apply LinearMap.mem_ker.mpr
        have hz := congrArg (fun y : EuclideanSpace ℝ (Fin (Fintype.card s)) ↦ y i)
          (LinearMap.mem_ker.mp hA)
        rw [heval, ← hei]
        simpa only [evaluation9_apply, WithLp.ofLp_zero, Pi.zero_apply] using hz
      apply LinearMap.mem_ker.mpr
      ext i
      rw [← heval]
      apply LinearMap.mem_ker.mp
      by_cases hi : i ∈ s
      · exact hs (subset_span ⟨i, hi, rfl⟩)
      · obtain ⟨a, ha, hamem⟩ := hmax i hi
        exact (d.ker.smul_mem_iff ha).mp (hs hamem)
    · intro A hA
      apply LinearMap.mem_ker.mpr
      ext i
      have hz := congrArg (fun y : EuclideanSpace ℝ ι ↦ y (e i)) (LinearMap.mem_ker.mp hA)
      simpa only [evaluation9_apply, WithLp.ofLp_zero, Pi.zero_apply] using hz

open MvPolynomial in
/-- A generator recorded in scaled coordinates evaluates as the original lattice monomial. -/
private theorem evaluation_substituted_basis {ι : Type*} [Fintype ι]
    (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (p : ι → Fin 3 → ℝ)
    (a : MonomialIndex 9) (i : ι) :
    evaluation9 p (substitutionEquiv9 T hT (coeffBasis9 a)) i =
      ∏ j, (T.mulVec (p i)) j ^ a.val j := by
  classical
  let g := monomial (exponent a) (1 : ℝ)
  have hg : (substitution T g).IsHomogeneous 9 := by
    have ha : (exponent a).degree = 9 := by
      rw [Finsupp.degree_eq_sum]
      simpa only [exponent_apply] using Finset.Nat.mem_antidiagonalTuple.mp a.property
    simpa only [substitution, one_mul] using (isHomogeneous_monomial (1 : ℝ) ha).aeval
      (fun j ↦ ∑ k, C (T j k) * X k) (n := 1)
      (fun j ↦ IsHomogeneous.sum _ _ _ fun k _ ↦ (isHomogeneous_X ℝ k).C_mul _)
  have hcoord (c : MonomialIndex 9) : (substitutionEquiv9 T hT (coeffBasis9 a)) c =
      (substitution T g).coeff (exponent c) := by
    change (coeffBasis9.repr ((substitutionEquiv9 T hT).toLinearMap (coeffBasis9 a))) c = _
    rw [show (substitutionEquiv9 T hT).toLinearMap =
        Matrix.toLin coeffBasis9 coeffBasis9 (substitutionMatrix 9 T) from
      LinearEquiv.coe_ofIsUnitDet _]
    rw [← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]
    rfl
  have hcomp : (aeval (p i)).comp (substitution T) = aeval (R := ℝ) (T.mulVec (p i)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [Matrix.mulVec, dotProduct]
  calc
    _ = (aeval (p i)) (substitution T g) := by
      rw [evaluation9_apply, ← sum_monomial_coeff hg, map_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [hcoord, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
      simp only [exponent_apply, Algebra.algebraMap_self_apply, mul_comm]
    _ = (aeval (T.mulVec (p i))) g := DFunLike.congr_fun hcomp g
    _ = _ := by
      change aeval (T.mulVec (p i)) (monomial (exponent a) (1 : ℝ)) = _
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
      simp only [exponent_apply, map_one, one_mul]

/-- The actual evaluation image is discrete, since it lies in the integer coordinate lattice. -/
private theorem evaluation_image_discrete {ι : Type*} [Fintype ι]
    (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (p : ι → EuclideanSpace ℝ (Fin 3))
    (hMem : ∀ i, p i ∈ span ℤ (Set.range b)) :
    DiscreteTopology (imageLattice
      (coefficientLattice9 (latticeCoordinates b) (latticeCoordinates_det_ne_zero b))
      (evaluation9 (fun i j ↦ p i j))) := by
  let T := latticeCoordinates b
  let hT : T.det ≠ 0 := latticeCoordinates_det_ne_zero b
  let J := evaluation9 (fun i j ↦ p i j)
  let I := imageLattice (coefficientLattice9 T hT) J
  have hI : I ≤ coordinateLattice ι := by
    change (coefficientLattice9 T hT).map (J.restrictScalars ℤ) ≤ _
    rw [Submodule.map_le_iff_le_comap]
    apply span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply (mem_coordinateLattice_iff _).2
    intro i
    choose z hz using (b.mem_span_iff_repr_mem ℤ (p i)).mp (hMem i)
    have hcoord (j : Fin 3) : (T.mulVec (p i).ofLp) j = b.repr (p i) j :=
      congrFun ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix_mulVec_repr b (p i)) j
    refine ⟨∏ j, z j ^ a.val j, ?_⟩
    change ((∏ j, z j ^ a.val j : ℤ) : ℝ) =
      J ((coeffBasis9.map (substitutionEquiv9 T hT)) a) i
    rw [Int.cast_prod, Basis.map_apply, evaluation_substituted_basis]
    simp only [Int.cast_pow, hcoord, ← hz, algebraMap_int_eq]
    rfl
  exact DiscreteTopology.of_continuous_injective
    (f := fun x : I ↦ (⟨x.val, hI x.property⟩ : coordinateLattice ι))
    (continuous_subtype_val.subtype_mk _)
    (fun _ _ h ↦ Subtype.ext (congrArg (fun y : coordinateLattice ι ↦ y.val) h))

/-- The radius `dim(E) * R` ball contains an orthonormal coordinate cube of side `2R`. -/
private theorem cube_volume_le_ball {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (R : ℝ) :
    ENNReal.ofReal (2 * R) ^ finrank ℝ V ≤
      volume (Metric.closedBall (0 : V) ((finrank ℝ V : ℝ) * R)) := by
  let n := finrank ℝ V
  let o := stdOrthonormalBasis ℝ V
  let u : V → (Fin n → ℝ) := WithLp.ofLp ∘ o.repr
  let Q : Set (Fin n → ℝ) := Set.Icc (fun _ ↦ -R) (fun _ ↦ R)
  have hu : MeasurePreserving u volume volume :=
    (PiLp.volume_preserving_ofLp (Fin n)).comp o.measurePreserving_repr
  have hvol : volume (u ⁻¹' Q) = ENNReal.ofReal (2 * R) ^ n := by
    rw [hu.measure_preimage (isClosed_Icc.measurableSet.nullMeasurableSet : NullMeasurableSet Q volume),
      Real.volume_Icc_pi]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hvol]
  apply measure_mono
  intro x hx
  change (fun _ ↦ -R) ≤ u x ∧ u x ≤ fun _ ↦ R at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖x‖ = ‖∑ i, (o.repr x) i • o i‖ := by rw [o.sum_repr]
    _ ≤ ∑ i, ‖(o.repr x) i • o i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, R := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, o.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs]
      exact abs_le.mpr ⟨hx.1 i, hx.2 i⟩
    _ = _ := by simp [nsmul_eq_mul, n]

private theorem minkowski_of_covolume_le_pow {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Nontrivial V] (K : Submodule ℤ V) [DiscreteTopology K] [IsZLattice ℝ K]
    (R : ℝ) (hR : 0 ≤ R) (hvol : ZLattice.covolume K volume ≤ R ^ finrank ℝ V) :
    ∃ x : V, x ≠ 0 ∧ x ∈ K ∧ ‖x‖ ≤ (finrank ℝ V : ℝ) * R := by
  let b := (Free.chooseBasis ℤ K).ofZLatticeBasis ℝ K
  have hfund : IsAddFundamentalDomain K.toAddSubgroup (ZSpan.fundamentalDomain b) volume :=
    ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ K) volume
  let : Countable K.toAddSubgroup := (inferInstance : Countable K)
  have hv : (volume : Measure V) (ZSpan.fundamentalDomain b) ≤
      ENNReal.ofReal (R ^ finrank ℝ V) := by
    have hfinite : (volume : Measure V) (ZSpan.fundamentalDomain b) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfinite, ← measureReal_def,
      ← ZLattice.covolume_eq_measure_fundamentalDomain K volume hfund]
    exact ENNReal.ofReal_le_ofReal hvol
  let r : ℝ := (finrank ℝ V : ℝ) * R
  have hball := cube_volume_le_ball (V := V) R
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), ENNReal.ofReal_ofNat, mul_pow,
    mul_comm, ← ENNReal.ofReal_pow hR] at hball
  have hsymm : ∀ x ∈ Metric.closedBall (0 : V) r, -x ∈ Metric.closedBall (0 : V) r := by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hx
  obtain ⟨x, hx, hxb⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure hfund
    hsymm (convex_closedBall 0 r) (isCompact_closedBall 0 r)
    ((mul_le_mul' hv le_rfl).trans hball)
  exact ⟨x.val, fun h ↦ hx (Subtype.ext h), x.property, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hxb⟩

/-- Uniformly over the point lattice and all finite families of bounded lattice points, a
real evaluation kernel of dimension at least fifteen contains a short nonzero integral form.
The coefficients and norm are in ordinary scaled Euclidean monomials; integrality is in `b`.
-/
theorem exists_short_form (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type*} [Fintype ι] (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
        (p : ι → EuclideanSpace ℝ (Fin 3)),
        (∀ i, p i ∈ span ℤ (Set.range b)) → (∀ i j, |p i j| ≤ B) →
        15 ≤ finrank ℝ (evaluation9 (fun i j ↦ p i j)).ker →
        ∃ A : Coeff9, A ≠ 0 ∧
          A ∈ coefficientLattice9 (latticeCoordinates b) (latticeCoordinates_det_ne_zero b) ∧
          (∀ i, evaluation9 (fun j l ↦ p j l) A i = 0) ∧
          ‖A‖ ≤ C * max 1 ((ZLattice.covolume (span ℤ (Set.range b)) volume)⁻¹ ^ 11) := by
  let N := Fintype.card (MonomialIndex 9)
  have hN : N = 55 := by decide
  let K : ℝ := N.factorial * (max 1 ((N : ℝ) * B ^ 9)) ^ N
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.factorial_pos N) (one_le_pow₀ (le_max_left _ _))
  refine ⟨N * K, mul_pos (by exact_mod_cast (show 0 < N by omega)) (by linarith), ?_⟩
  intro ι _ b p hMem hp hdim
  obtain ⟨k, e, hJ, hker⟩ := exists_independent_subfamily p
  let q : Fin k → EuclideanSpace ℝ (Fin 3) := p ∘ e
  let J := evaluation9 (fun i j ↦ q i j)
  let L := coefficientLattice9 (latticeCoordinates b) (latticeCoordinates_det_ne_zero b)
  let Λ := kernelLattice L J
  have hq (i : Fin k) : q i ∈ span ℤ (Set.range b) := hMem (e i)
  let : DiscreteTopology (imageLattice L J) := evaluation_image_discrete b q hq
  let : IsZLattice ℝ Λ := kernelLattice_full L J hJ
  let n := finrank ℝ J.ker
  have hn : 15 ≤ n := by
    change 15 ≤ finrank ℝ (evaluation9 (fun i j ↦ p (e i) j)).ker
    exact hker.symm ▸ hdim
  let : Nontrivial J.ker := finrank_pos_iff.mp (by omega : 0 < n)
  have hnN : n ≤ N := by
    simpa only [finrank_euclideanSpace] using J.ker.finrank_le
  let δ := ZLattice.covolume (span ℤ (Set.range b)) volume
  have hδ : 0 < δ := ZLattice.covolume_pos _ _
  let M : ℝ := max 1 (δ⁻¹ ^ 11)
  have hM : 1 ≤ M := le_max_left _ _
  -- Taking both factors at least one lets the inequalities use n ≥ 15 without roots.
  let R := K * M
  have hR : 0 ≤ R := mul_nonneg (by linarith) (by linarith)
  have hv : ZLattice.covolume Λ volume ≤ R ^ n := by
    calc
      _ ≤ δ⁻¹ ^ 165 * K :=
        evaluation9_kernel_covolume_le_uniform b q hJ hq B hB (fun i ↦ hp (e i))
      _ ≤ M ^ n * K ^ n := by
        apply mul_le_mul _ _ (by linarith) (pow_nonneg (by linarith) _)
        · rw [show δ⁻¹ ^ 165 = (δ⁻¹ ^ 11) ^ 15 by rw [← pow_mul]]
          exact (pow_le_pow_left₀ (pow_nonneg (inv_nonneg.mpr hδ.le) _) (le_max_right _ _) _).trans
            (pow_le_pow_right₀ hM hn)
        · simpa only [pow_one] using pow_le_pow_right₀ hK (by omega : 1 ≤ n)
      _ = _ := (mul_pow M K n).symm.trans (congrArg (· ^ n) (mul_comm M K))
  obtain ⟨x, hx, hxΛ, hxnorm⟩ := minkowski_of_covolume_le_pow Λ R hR hv
  have hz := x.property
  change x.val ∈ (evaluation9 (fun i j ↦ p (e i) j)).ker at hz
  rw [hker] at hz
  refine ⟨x.val, fun h ↦ hx (Subtype.ext h), hxΛ, ?_, ?_⟩
  · intro i
    have hi := congrArg (fun y : EuclideanSpace ℝ ι ↦ y i) (LinearMap.mem_ker.mp hz)
    simpa only [WithLp.ofLp_zero, Pi.zero_apply] using hi
  · change ‖x‖ ≤ (N * K) * M
    rw [mul_assoc]
    exact hxnorm.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnN) hR)

end EvaluationKernelShortForm
