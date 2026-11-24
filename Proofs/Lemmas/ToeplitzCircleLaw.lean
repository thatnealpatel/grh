module

public import Lemmas.ZeroPrefixCosine
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Finite circle laws for positive Toeplitz prefixes

Sources: `3d2886df:.godel/bob/finite-cutoff-budget.md`, lines 11–15,
and the positive completion used at `b5622851:.godel/adhoc/chi4-exterior.md`,
lines 27–37 (source pin `d500be7b`).

Scope: finite nonnegative angular weights, with no arithmetic realization claimed.
The Gram factor and the extension of the partial shift do not require strict positivity.

Owning check session: `01a20f1a-0f71-75d4-a170-6751dc7ee00a`.
-/

open scoped BigOperators InnerProductSpace

namespace Masullo.ZeroPrefixCosine

/-- Real positivity gives a Gram factor, which can be read in complex Euclidean space. -/
private theorem exists_gram {n : ℕ} {m : ℕ → ℝ} (hT : ToeplitzPositive n m) :
    ∃ u : Fin (n + 1) → EuclideanSpace ℂ (Fin (n + 1)),
      ∀ i j, ⟪u i, u j⟫_ℂ = (m (Nat.dist i.val j.val) : ℂ) := by
  classical
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j ↦ m (Nat.dist i.val j.val)
  have hpsd : T.PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨.ext ?_, ?_⟩
    · intro i j
      simp [T, Nat.dist_comm]
    · intro v
      let a (k : ℕ) : ℝ := if hk : k < n + 1 then v ⟨k, hk⟩ else 0
      have ha (i : Fin (n + 1)) : a i.val = v i := dite_eq_left i.isLt
      have ht := hT a
      rw [← Fin.sum_univ_eq_sum_range] at ht
      simp_rw [← Fin.sum_univ_eq_sum_range] at ht
      simpa [T, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc,
        ha] using ht
  have hfactor : ∃ B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, T = B.conjTranspose * B := by
    open scoped MatrixOrder Matrix.Norms.L2Operator in
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg
    exact ⟨B, hB⟩
  obtain ⟨B, hB⟩ := hfactor
  refine ⟨fun i ↦ WithLp.toLp 2 fun k ↦ (B k i : ℂ), ?_⟩
  intro i j
  have hij : (∑ k, B k i * B k j) = m (Nat.dist i.val j.val) := by
    simpa [T, Matrix.mul_apply, Matrix.conjTranspose_apply] using
      (congrArg (fun C : Matrix _ _ ℝ ↦ C i j) hB).symm
  rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp]
  simpa [dotProduct, mul_comm] using congrArg Complex.ofReal hij

/-- Linear combinations of a finite family, with no independence assumption. -/
private def combinations {E : Type*} [AddCommGroup E] [Module ℂ E] {n : ℕ}
    (u : Fin n → E) : (Fin n → ℂ) →ₗ[ℂ] E where
  toFun a := ∑ i, a i • u i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, mul_smul]

/-- Equal Gram matrices give an isometry on the range of the first combination map. -/
private theorem exists_isometry_of_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {n : ℕ} (v w : Fin n → E)
    (h : ∀ i j, ⟪v i, v j⟫_ℂ = ⟪w i, w j⟫_ℂ) :
    ∃ U : E →ₗᵢ[ℂ] E, ∀ i, U (v i) = w i := by
  classical
  let A := combinations v
  let B := combinations w
  have hnorm (a : Fin n → ℂ) : ‖A a‖ = ‖B a‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (A a), norm_sq_eq_re_inner (𝕜 := ℂ) (B a)]
    congr 1
    change ⟪∑ i, a i • v i, ∑ i, a i • v i⟫_ℂ = ⟪∑ i, a i • w i, ∑ i, a i • w i⟫_ℂ
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, h]
  have hker : A.ker ≤ B.ker := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    exact norm_eq_zero.mp (by rw [← hnorm, ha, norm_zero])
  -- The second combination map descends through the kernel of the first.
  let L := (A.ker.liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hL (a : Fin n → ℂ) : L (A.quotKerEquivRange (Submodule.Quotient.mk a)) = B a := by
    simp [L, Submodule.liftQ_apply]
  have hLnorm (x : A.range) : ‖L x‖ = ‖x‖ := by
    obtain ⟨a, ha⟩ := x.property
    have hxa : A.quotKerEquivRange (Submodule.Quotient.mk a) = x :=
      Subtype.ext ((A.quotKerEquivRange_apply_mk a).trans ha)
    rw [← hxa, hL, ← hnorm]
    exact congrArg norm (A.quotKerEquivRange_apply_mk a).symm
  let V : A.range →ₗᵢ[ℂ] E := ⟨L, hLnorm⟩
  refine ⟨V.extend, fun i ↦ ?_⟩
  let a : Fin n → ℂ := fun j ↦ if j = i then 1 else 0
  have single_apply (u : Fin n → E) : combinations u a = u i := by
    change (∑ j, a j • u j) = u i
    rw [Finset.sum_eq_single i]
    · simp [a]
    · intro j _ hj
      simp [a, hj]
    · simp
  let x := A.quotKerEquivRange (Submodule.Quotient.mk a)
  have hx : (x : E) = v i := (A.quotKerEquivRange_apply_mk a).trans (single_apply v)
  rw [← hx, V.extend_apply]
  exact (hL a).trans (single_apply w)

/-- Split off an eigenline at a time to obtain the moments of a complex isometry.
Each weight is the squared norm of the vector's component on its eigenline. -/
private theorem isometry_spectral_moments (d : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E],
      Module.finrank ℂ E = d → ∀ (U : E →ₗᵢ[ℂ] E) (x : E),
        ∃ (w : Fin d → ℝ) (z : Fin d → ℂ), (∀ i, 0 ≤ w i) ∧ (∀ i, ‖z i‖ = 1) ∧
          ∀ j : ℕ, (∑ i, (w i : ℂ) * (z i) ^ j) = ⟪x, (U.toLinearMap ^ j) x⟫_ℂ := by
  induction d with
  | zero =>
    intro E _ _ _ hd U x
    have : Subsingleton E := Module.finrank_zero_iff.mp hd
    have hx : x = 0 := Subsingleton.elim _ _
    exact ⟨Fin.elim0, Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun j ↦ by simp [hx]⟩
  | succ d ih =>
    intro E _ _ _ hd U x
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [hd]; omega)
    let S : Module.End ℂ E := U.toLinearMap
    obtain ⟨μ, hμ⟩ := S.exists_eigenvalue
    obtain ⟨e, he⟩ := hμ.exists_hasEigenvector
    have hUe : U e = μ • e := he.apply_eq_smul
    have he0 : e ≠ 0 := he.2
    have hnormμ : ‖μ‖ = 1 := by
      apply mul_right_cancel₀ (norm_ne_zero_iff.mpr he0)
      calc
        ‖μ‖ * ‖e‖ = ‖μ • e‖ := (norm_smul _ _).symm
        _ = ‖U e‖ := congrArg norm hUe.symm
        _ = 1 * ‖e‖ := by rw [U.norm_map, one_mul]
    have hμne : μ ≠ 0 := by
      intro h0
      simp [h0] at hnormμ
    let P : Submodule ℂ E := ℂ ∙ e
    have hPdim : Module.finrank ℂ Pᗮ = d := by
      have : Fact (Module.finrank ℂ E = d + 1) := ⟨hd⟩
      exact Submodule.finrank_orthogonal_span_singleton he0
    -- The complement is invariant: the eigenline is mapped onto itself by `U`.
    have hPmap (y : E) (hy : y ∈ Pᗮ) : U y ∈ Pᗮ := by
      have hye : ⟪e, y⟫_ℂ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hy
      have hpre : U (μ⁻¹ • e) = e := by
        rw [map_smul, hUe, smul_smul, inv_mul_cancel₀ hμne, one_smul]
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [← hpre, U.inner_map_map, inner_smul_left, hye, mul_zero]
    let V : Pᗮ →ₗᵢ[ℂ] Pᗮ :=
      ⟨(S.comp Pᗮ.subtype).codRestrict Pᗮ (fun y ↦ hPmap y y.property), fun y ↦ U.norm_map y⟩
    have hpow (j : ℕ) (y : Pᗮ) : ((V.toLinearMap ^ j) y : E) = (S ^ j) y := by
      induction j with
      | zero => simp
      | succ j hj =>
        rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_apply_eq_comp]
        change U (((V.toLinearMap ^ j) y : Pᗮ) : E) = U ((S ^ j) y)
        rw [hj]
    let a := P.starProjection x
    let b : Pᗮ := ⟨x - a, P.sub_starProjection_mem_orthogonal x⟩
    have ha : a ∈ P := P.starProjection_apply_mem x
    have hab : a + (b : E) = x := by change a + (x - a) = x; abel
    have hapow (j : ℕ) : (S ^ j) a = μ ^ j • a := by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
      rw [← hc, map_smul, he.pow_apply, smul_comm]
    obtain ⟨w, z, hw, hz, hspec⟩ := ih hPdim V b
    refine ⟨Fin.cons (‖a‖ ^ 2) w, Fin.cons μ z, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.cons_zero] using sq_nonneg ‖a‖
      · simpa only [Fin.cons_succ] using hw j
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.cons_zero] using hnormμ
      · simpa only [Fin.cons_succ] using hz j
    · intro j
      have hab₀ : ⟪a, ((V.toLinearMap ^ j) b : Pᗮ)⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal ha ((V.toLinearMap ^ j) b).property
      have hba₀ : ⟪(b : E), a⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal ha b.property
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hspec]
      rw [← hab, map_add, hapow, ← hpow, inner_add_left, inner_add_right, inner_add_right,
        inner_smul_right, inner_smul_right, hab₀, hba₀, mul_zero, add_zero, zero_add,
        inner_self_eq_norm_sq_to_K, Complex.ofReal_pow, mul_comm (μ ^ j)]
      rfl

/-- Every positive Toeplitz prefix is realized by at most `n + 1` weighted angles.
Their weights sum to `m 0`, the cosine moments are `m j`, and the sine moments
are zero through order `n`, including order zero. No nonsingularity or nonzero
mass assumption is needed. -/
public theorem exists_circleLaw_of_toeplitzPositive {n : ℕ} {m : ℕ → ℝ}
    (hT : ToeplitzPositive n m) :
    ∃ w θ : Fin (n + 1) → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = m 0 ∧
      ∀ j : ℕ, j ≤ n →
        moment Finset.univ w θ j = m j ∧
          (∑ i, w i * Real.sin ((j : ℝ) * θ i)) = 0 := by
  obtain ⟨u, hgram⟩ := exists_gram hT
  obtain ⟨U, hU⟩ := exists_isometry_of_gram (u ∘ Fin.castSucc) (u ∘ Fin.succ) (by
    intro i j
    simp only [Function.comp_apply, hgram, Fin.val_castSucc, Fin.val_succ, Nat.dist_succ_succ])
  have horbit (j : ℕ) (hj : j < n + 1) : (U.toLinearMap ^ j) (u 0) = u ⟨j, hj⟩ := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp, ih (by omega)]
      exact hU ⟨j, by omega⟩
  obtain ⟨w, z, hw, hz, hspec⟩ :=
    isometry_spectral_moments (n + 1) finrank_euclideanSpace_fin U (u 0)
  let θ (i : Fin (n + 1)) := (z i).arg
  have hpolar (j : ℕ) (i : Fin (n + 1)) :
      z i ^ j = (Real.cos ((j : ℝ) * θ i) : ℂ) + (Real.sin ((j : ℝ) * θ i) : ℂ) * Complex.I := by
    have harg : Complex.exp ((θ i : ℂ) * Complex.I) = z i := by
      simpa [θ, hz i] using Complex.norm_mul_exp_arg_mul_I (z i)
    rw [← harg, ← Complex.exp_nat_mul, ← mul_assoc]
    simp [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_mul]
  have hmom (j : ℕ) (hj : j ≤ n) :
      moment Finset.univ w θ j = m j ∧ (∑ i, w i * Real.sin ((j : ℝ) * θ i)) = 0 := by
    have hs := hspec j
    rw [horbit j (by omega), hgram] at hs
    change (∑ i, (w i : ℂ) * z i ^ j) = (m (Nat.dist 0 j) : ℂ) at hs
    rw [Nat.dist_zero_left] at hs
    exact ⟨by simpa [moment, Complex.re_sum, Complex.mul_re, hpolar, ← Complex.ofReal_mul,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin] using congrArg Complex.re hs,
      by simpa [Complex.im_sum, Complex.mul_im, hpolar, ← Complex.ofReal_mul,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin] using congrArg Complex.im hs⟩
  exact ⟨w, θ, hw, by simpa [moment] using (hmom 0 (Nat.zero_le n)).1, hmom⟩

/-- A positive Toeplitz prefix with `m 0 = 1` admits a finite probability law on angles. -/
public theorem exists_probabilityCircleLaw_of_toeplitzPositive {n : ℕ} {m : ℕ → ℝ}
    (hT : ToeplitzPositive n m) (h₀ : m 0 = 1) :
    ∃ w θ : Fin (n + 1) → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ j : ℕ, j ≤ n →
        moment Finset.univ w θ j = m j ∧
          (∑ i, w i * Real.sin ((j : ℝ) * θ i)) = 0 := by
  obtain ⟨w, θ, hw, hmass, hmom⟩ := exists_circleLaw_of_toeplitzPositive hT
  exact ⟨w, θ, hw, hmass.trans h₀, hmom⟩

end Masullo.ZeroPrefixCosine
