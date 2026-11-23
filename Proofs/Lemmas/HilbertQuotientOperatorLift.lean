module

public import Lemmas.HilbertDenseQuotient
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Zero extension of Hilbert quotient operators

For the quotient realized as an orthogonal complement, extend an operator by
zero on the closed subspace being quotiented out. This transports finite and
absolutely operator-norm summable rank-one presentations. No trace ideal is
assumed or constructed here.
-/

open InnerProductSpace

namespace Masullo

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `S B Q`, with `Q` the quotient projection and `S` the inclusion
of the orthogonal complement, is isometric in operator norm. -/
public noncomputable def hilbertQuotientOperatorLift (T : Submodule ℂ H) :
    (Tᗮ →L[ℂ] Tᗮ) →ₗᵢ[ℂ] (H →L[ℂ] H) where
  toFun B := Tᗮ.subtypeL.comp (B.comp (hilbertQuotientProjection T))
  map_add' B C := by ext x; rfl
  map_smul' c B := by ext x; rfl
  norm_map' B := by
    let L := Tᗮ.subtypeL.comp (B.comp (hilbertQuotientProjection T))
    change ‖L‖ = ‖B‖
    apply le_antisymm
    · refine L.opNorm_le_bound (norm_nonneg B) (fun x ↦ ?_)
      change ‖B (hilbertQuotientProjection T x)‖ ≤ ‖B‖ * ‖x‖
      exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (Tᗮ.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _))
    · refine B.opNorm_le_bound (norm_nonneg L) (fun y ↦ ?_)
      have hy := L.le_opNorm (y : H)
      change ‖B (Tᗮ.orthogonalProjectionOnto (y : H))‖ ≤ ‖L‖ * ‖y‖ at hy
      rwa [Tᗮ.orthogonalProjectionOnto_mem_subspace_eq_self] at hy

/-- The canonical lift applies the quotient operator between projection and inclusion. -/
public theorem hilbertQuotientOperatorLift_apply (T : Submodule ℂ H) (B : Tᗮ →L[ℂ] Tᗮ) (x : H) :
    hilbertQuotientOperatorLift T B x = (B (hilbertQuotientProjection T x) : H) := by
  rw [hilbertQuotientOperatorLift]
  rfl

/-- If `B` descends from `A`, the lift is projection *after* `A`. -/
public theorem hilbertQuotientOperatorLift_of_intertwine (T : Submodule ℂ H)
    (B : Tᗮ →L[ℂ] Tᗮ) (A : H →L[ℂ] H)
    (h : ∀ x, B (hilbertQuotientProjection T x) = hilbertQuotientProjection T (A x)) :
    hilbertQuotientOperatorLift T B = Tᗮ.starProjection.comp A := by
  ext x
  exact congrArg Subtype.val (h x)

/-- The pullback of the Riesz row of `v` along the quotient projection is the
Riesz row of its ambient lift; the inner product is linear in the input. -/
public theorem hilbertQuotientOperatorLift_rankOne (T : Submodule ℂ H) (u v : Tᗮ) :
    hilbertQuotientOperatorLift T (rankOne ℂ u v) = rankOne ℂ (u : H) (v : H) := by
  ext x
  rw [hilbertQuotientOperatorLift_apply, rankOne_apply, rankOne_apply]
  change ⟪v, Tᗮ.orthogonalProjectionOnto x⟫_ℂ • (u : H) = ⟪(v : H), x⟫_ℂ • (u : H)
  rw [Tᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- Arbitrary finite rank-one cutoffs extend term by term in the same order. -/
public theorem hilbertQuotientOperatorLift_sum_rankOne {ι : Type*} (T : Submodule ℂ H)
    (c : Finset ι) (u v : ι → Tᗮ) :
    hilbertQuotientOperatorLift T (∑ j ∈ c, rankOne ℂ (u j) (v j)) =
      ∑ j ∈ c, rankOne ℂ (u j : H) (v j : H) := by
  simpa only [LinearIsometry.coe_toLinearMap, hilbertQuotientOperatorLift_rankOne] using
    map_sum (hilbertQuotientOperatorLift T).toLinearMap (fun j ↦ rankOne ℂ (u j) (v j)) c

/-- Transfer an actual norm-product-summable quotient remainder with pointwise
synthesis. The rank-one terms keep their norm products (inherited norms), and
sum to the lifted operator in operator norm. -/
public theorem hilbertQuotientOperatorLift_hasSum_rankOne {ι : Type*} (T : Submodule ℂ H)
    (B : Tᗮ →L[ℂ] Tᗮ) (u v : ι → Tᗮ)
    (h : Summable fun j ↦ ‖u j‖ * ‖v j‖)
    (hB : ∀ x, HasSum (fun j ↦ rankOne ℂ (u j) (v j) x) (B x)) :
    (Summable fun j ↦ ‖rankOne ℂ (u j : H) (v j : H)‖) ∧
      HasSum (fun j ↦ rankOne ℂ (u j : H) (v j : H)) (hilbertQuotientOperatorLift T B) := by
  have hs : Summable fun j ↦ ‖rankOne ℂ (u j) (v j)‖ := by
    simpa only [norm_rankOne] using h
  have heq : (∑' j, rankOne ℂ (u j) (v j)) = B := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := hs.of_norm.hasSum.mapL (ContinuousLinearMap.apply ℂ Tᗮ x)
    simpa only [ContinuousLinearMap.apply_apply] using hx.unique (hB x)
  refine ⟨?_, ?_⟩
  · simp only [norm_rankOne]
    exact h
  · have hb := heq ▸ hs.of_norm.hasSum
    simpa only [LinearIsometry.coe_toContinuousLinearMap, hilbertQuotientOperatorLift_rankOne] using
      hb.mapL (hilbertQuotientOperatorLift T).toContinuousLinearMap

end Masullo
