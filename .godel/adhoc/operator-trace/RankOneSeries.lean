import Mathlib.Analysis.InnerProductSpace.l2Space

open scoped InnerProductSpace
open InnerProductSpace

namespace AdHoc

/-- A Hilbert-basis diagonal for an explicitly summable rank-one presentation.
The inner product is linear in its second argument. No finite-dimensional
trace or a priori basis-independence is assumed. -/
theorem hasSum_diagonal {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (u v : ℕ → H)
    (h : Summable fun n => ‖u n‖ * ‖v n‖)
    (hT : ∀ x, HasSum (fun n => rankOne ℂ (u n) (v n) x) (T x)) :
    (Summable fun n => ⟪v n, u n⟫_ℂ) ∧
      HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (∑' n, ⟪v n, u n⟫_ℂ) := by
  let d (p : ℕ × ι) := ⟪b p.2, u p.1⟫_ℂ * ⟪v p.1, b p.2⟫_ℂ
  have row (n : ℕ) : (Summable fun i => ‖d (n, i)‖) ∧
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
  have tr (n : ℕ) : HasSum (fun i => d (n,i)) ⟪v n, u n⟫_ℂ := by
    simpa only [d, mul_comm] using b.hasSum_inner_mul_inner (v n) (u n)
  have htotal := hd.hasSum.prod_fiberwise tr
  refine ⟨htotal.summable, ?_⟩
  rw [htotal.tsum_eq, ← (Equiv.prodComm ι ℕ).tsum_eq d]
  exact hd.prod_symm.hasSum.prod_fiberwise col

end AdHoc
