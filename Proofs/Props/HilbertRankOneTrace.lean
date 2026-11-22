module

public import Lemmas.RankOneSeries

/-! # The diagonal trace of a summable rank-one series

Hilbert-space form of the comparison in Appendix C.3. The trace is the diagonal sum,
not the sum of the absolute values of the diagonal entries.
-/

open InnerProductSpace
open scoped InnerProductSpace

namespace Masullo.OperatorTrace

/-- A Hilbert-basis diagonal for an explicitly summable rank-one presentation.
The inner product is linear in its second argument. No finite-dimensional
trace or a priori basis-independence is assumed. -/
public theorem hasSum_diagonal {ι κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (u v : κ → H)
    (h : Summable fun n ↦ ‖u n‖ * ‖v n‖)
    (hT : ∀ x, HasSum (fun n ↦ rankOne ℂ (u n) (v n) x) (T x)) :
    (Summable fun n ↦ ⟪v n, u n⟫_ℂ) ∧
      HasSum (fun i ↦ ⟪b i, T (b i)⟫_ℂ) (∑' n, ⟪v n, u n⟫_ℂ) :=
  hasSum_diagonal_of_rankOne b T u v h hT

end Masullo.OperatorTrace
