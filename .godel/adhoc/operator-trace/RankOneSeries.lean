import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space

open scoped InnerProductSpace
open InnerProductSpace

namespace AdHoc

/-- A Hilbert-basis diagonal for an explicitly summable rank-one presentation.
The inner product is linear in its second argument. No finite-dimensional
trace or a priori basis-independence is assumed. -/
theorem hasSum_diagonal {ι κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (u v : κ → H)
    (h : Summable fun n => ‖u n‖ * ‖v n‖)
    (hT : ∀ x, HasSum (fun n => rankOne ℂ (u n) (v n) x) (T x)) :
    (Summable fun n => ⟪v n, u n⟫_ℂ) ∧
      HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (∑' n, ⟪v n, u n⟫_ℂ) := by
  let d (p : κ × ι) := ⟪b p.2, u p.1⟫_ℂ * ⟪v p.1, b p.2⟫_ℂ
  have row (n : κ) : (Summable fun i => ‖d (n, i)‖) ∧
      (∑' i, ‖d (n, i)‖) ≤ ‖u n‖ * ‖v n‖ := by
    have hn (i : ι) : ‖d (n,i)‖ = ‖b.repr (u n) i‖ * ‖b.repr (v n) i‖ := by
      simp only [d, norm_mul, b.repr_apply_apply]
      rw [norm_inner_symm (v n) (b i)]
    simp only [hn]
    simpa using lp.tsum_mul_le_mul_norm (by rw [Real.holderConjugate_iff]; norm_num)
      (b.repr (u n)) (b.repr (v n))
  have hd : Summable d := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun p => norm_nonneg (d p))).2
    exact ⟨fun n => (row n).1, h.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
      (fun n => (row n).2)⟩
  have col (i : ι) : HasSum (fun n => d (n, i)) ⟪b i, T (b i)⟫_ℂ := by
    simpa only [d, innerSL_apply_apply, inner_right_rankOne_apply] using
      (hT (b i)).mapL (innerSL ℂ (b i))
  have tr (n : κ) : HasSum (fun i => d (n,i)) ⟪v n, u n⟫_ℂ := by
    simpa only [d, mul_comm] using b.hasSum_inner_mul_inner (v n) (u n)
  have htotal := hd.hasSum.prod_fiberwise tr
  refine ⟨htotal.summable, ?_⟩
  rw [htotal.tsum_eq, ← (Equiv.prodComm ι κ).tsum_eq d]
  exact hd.prod_symm.hasSum.prod_fiberwise col

/-- Right composition of a pointwise synthesis series gives an operator-norm convergent
rank-one series. Its second vectors represent the functionals `(a n).comp Q` by Riesz. -/
theorem hasSum_rankOne_comp {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S Q : H →L[ℂ] H) (u : κ → H) (a : κ → H →L[ℂ] ℂ)
    (h : Summable fun n => ‖u n‖ * ‖a n‖)
    (hS : ∀ x, HasSum (fun n => a n x • u n) (S x)) :
    let v (n : κ) := (toDual ℂ H).symm ((a n).comp Q)
    (Summable fun n => ‖rankOne ℂ (u n) (v n)‖) ∧
      HasSum (fun n => rankOne ℂ (u n) (v n)) (S.comp Q) := by
  let v (n : κ) := (toDual ℂ H).symm ((a n).comp Q)
  have hv : Summable fun n => ‖rankOne ℂ (u n) (v n)‖ := by
    apply (h.mul_right ‖Q‖).of_nonneg_of_le (fun n => norm_nonneg _)
    intro n
    rw [norm_rankOne, show ‖v n‖ = ‖(a n).comp Q‖ from (toDual ℂ H).symm.norm_map _, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((a n).opNorm_comp_le Q) (norm_nonneg _)
  refine ⟨hv, ?_⟩
  have hs := hv.of_norm.hasSum
  have hs_eq : (∑' n, rankOne ℂ (u n) (v n)) = S.comp Q := by
    ext x
    have heval := hs.mapL (ContinuousLinearMap.apply ℂ H x)
    simp only [ContinuousLinearMap.apply_apply, rankOne_apply, v, toDual_symm_apply,
      ContinuousLinearMap.comp_apply] at heval ⊢
    exact heval.unique (hS (Q x))
  exact hs_eq ▸ hs

/-- For any Hilbert basis, the diagonal sum of the right-composed operator is the sum of
`a n (Q (u n))`. No projection or commutation assumption on `Q` is needed. -/
theorem hasSum_diagonal_comp {ι κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (b : HilbertBasis ι ℂ H) (S Q : H →L[ℂ] H)
    (u : κ → H) (a : κ → H →L[ℂ] ℂ) (h : Summable fun n => ‖u n‖ * ‖a n‖)
    (hS : ∀ x, HasSum (fun n => a n x • u n) (S x)) :
    (Summable fun n => a n (Q (u n))) ∧
      HasSum (fun i => ⟪b i, (S.comp Q) (b i)⟫_ℂ) (∑' n, a n (Q (u n))) := by
  let v (n : κ) := (toDual ℂ H).symm ((a n).comp Q)
  obtain ⟨hnorm, hsum⟩ := hasSum_rankOne_comp S Q u a h hS
  have hv : Summable fun n => ‖u n‖ * ‖v n‖ := by
    simpa only [norm_rankOne] using hnorm
  have hT (x : H) : HasSum (fun n => rankOne ℂ (u n) (v n) x) ((S.comp Q) x) := by
    simpa only [ContinuousLinearMap.apply_apply] using
      hsum.mapL (ContinuousLinearMap.apply ℂ H x)
  simpa only [v, toDual_symm_apply, ContinuousLinearMap.comp_apply] using
    hasSum_diagonal b (S.comp Q) u v hv hT

end AdHoc
