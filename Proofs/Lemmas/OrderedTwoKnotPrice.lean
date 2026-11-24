module

public import Lemmas.SharedKnotCell
public import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The ordered two-knot price on a shared Bernstein cell

Source: `a585cb27:.godel/bob/eight-piece-deletion-33.md:205–237`.
Consumer: `a585cb27:.godel/bob/check-refined-frontier-33.py:24–50` (the ordered
maximum in `double_costs`). The argument is unchanged at discovery pin `69d5d309`
and selection base `432066cd`.
Owning check session: `01a20ee2-df11-780c-9cc1-8715404fb242`.

Scope: two ordered normalized positions in one closed cell, including the
boundary and diagonal. Both use the same three primitive-vector controls.
The price sums all three atom supports before maximizing over ordered pairs.
This is the exact interpolation step, without derivative errors or slab tables.
-/

@[expose] public section

namespace Masullo.OrderedTwoKnotPrice

open Set SharedKnotCell
open SplitAtomBernstein (Moment Score)
open scoped BigOperators

noncomputable section

/-- The three quadratic Bernstein weights in ascending control order. -/
def quadraticWeight (u : ℝ) (i : Fin 3) : ℝ :=
  ![(1 - u) ^ 2, 2 * u * (1 - u), u ^ 2] i

/-- Quadratic Bernstein interpolation of the common primitive controls. -/
def quadratic (C : Fin 3 → Primitive) (u : ℝ) : Primitive :=
  ∑ i, quadraticWeight u i • C i

/-- The joint score of the three consecutive primitive differences. -/
def price (H : Primitive → ℝ) (L R x y : Primitive) : ℝ :=
  H (L - x) + H (x - y) + H (y - R)

-- The ordered pairs are 00, 01, 02, 11, 12, 22.
private def row (k : Fin 6) : Fin 3 := ![0, 0, 0, 1, 1, 2] k

private def col (k : Fin 6) : Fin 3 := ![0, 1, 2, 1, 2, 2] k

private theorem row_le_col (k : Fin 6) : row k ≤ col k := by
  fin_cases k <;> decide

private def couplingWeight (s t : ℝ) (k : Fin 6) : ℝ :=
  ![(1 - t) ^ 2, 2 * (1 - t) * (t - s), (t - s) ^ 2,
    2 * s * (1 - t), 2 * s * (t - s), s ^ 2] k

private theorem couplingWeight_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (k : Fin 6) : 0 ≤ couplingWeight s t k := by
  have hgap : 0 ≤ t - s := sub_nonneg.mpr hst
  have hrest : 0 ≤ 1 - t := sub_nonneg.mpr ht
  fin_cases k <;> simp [couplingWeight] <;> positivity

private theorem sum_couplingWeight (s t : ℝ) : ∑ k, couplingWeight s t k = 1 := by
  simp [couplingWeight, Fin.sum_univ_succ]
  ring

private theorem row_marginal (s t : ℝ) (i : Fin 3) :
    ∑ k ∈ Finset.univ with row k = i, couplingWeight s t k = quadraticWeight s i := by
  rw [Finset.sum_filter]
  fin_cases i <;> simp [Fin.sum_univ_succ, couplingWeight, row, quadraticWeight] <;> ring

private theorem col_marginal (s t : ℝ) (i : Fin 3) :
    ∑ k ∈ Finset.univ with col k = i, couplingWeight s t k = quadraticWeight t i := by
  rw [Finset.sum_filter]
  fin_cases i <;> simp [Fin.sum_univ_succ, couplingWeight, col, quadraticWeight] <;> ring

private theorem sum_coupling_smul (C : Fin 3 → Primitive) (s t u : ℝ) (idx : Fin 6 → Fin 3)
    (hm : ∀ i, ∑ k ∈ Finset.univ with idx k = i, couplingWeight s t k = quadraticWeight u i) :
    (∑ k, couplingWeight s t k • C (idx k)) = quadratic C u := by
  rw [← Finset.sum_fiberwise Finset.univ idx (fun k ↦ couplingWeight s t k • C (idx k))]
  unfold quadratic
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hm i, Finset.sum_smul]
  exact Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2]

/-- A bound on every ordered control-pair price also bounds the interpolated
price at any two ordered positions in the closed cell. Only convexity of `H`
is needed. -/
theorem price_le_of_pair_bounds (H : Primitive → ℝ) (hH : ConvexOn ℝ univ H)
    (C : Fin 3 → Primitive) (L R : Primitive) {s t B : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (hB : ∀ i j : Fin 3, i ≤ j → price H L R (C i) (C j) ≤ B) :
    price H L R (quadratic C s) (quadratic C t) ≤ B := by
  let w := couplingWeight s t
  let x : Fin 6 → Primitive := fun k ↦ C (row k)
  let y : Fin 6 → Primitive := fun k ↦ C (col k)
  have hw : ∀ k, 0 ≤ w k := couplingWeight_nonneg hs hst ht
  have hw1 : ∑ k, w k = 1 := sum_couplingWeight s t
  have hx : (∑ k, w k • x k) = quadratic C s := sum_coupling_smul C s t s row (row_marginal s t)
  have hy : (∑ k, w k • y k) = quadratic C t := sum_coupling_smul C s t t col (col_marginal s t)
  have hL : (∑ k, w k • (L - x k)) = L - quadratic C s := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hw1, one_smul, hx]
  have hM : (∑ k, w k • (x k - y k)) = quadratic C s - quadratic C t := by
    simp only [smul_sub, Finset.sum_sub_distrib, hx, hy]
  have hR : (∑ k, w k • (y k - R)) = quadratic C t - R := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hw1, one_smul, hy]
  have hJ (v : Fin 6 → Primitive) : H (∑ k, w k • v k) ≤ ∑ k, w k * H (v k) := by
    simpa only [smul_eq_mul] using hH.map_sum_le (fun k _ ↦ hw k) hw1 (fun k _ ↦ mem_univ (v k))
  unfold price
  rw [← hL, ← hM, ← hR]
  calc
    _ ≤ (∑ k, w k * H (L - x k)) + (∑ k, w k * H (x k - y k)) +
        (∑ k, w k * H (y k - R)) :=
      add_le_add (add_le_add (hJ fun k ↦ L - x k) (hJ fun k ↦ x k - y k)) (hJ fun k ↦ y k - R)
    _ = ∑ k, w k * price H L R (x k) (y k) := by
      simp only [price, mul_add, Finset.sum_add_distrib]
    _ ≤ ∑ k, w k * B :=
      Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hB _ _ (row_le_col k)) (hw k)
    _ = B := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The actual atom support on `[0,1]`, in `SharedKnotCell.halfScore`'s
`(-X, -T(X), u)` orientation. The input is a start-minus-stop difference. -/
def atomSupport (v : Primitive) : ℝ :=
  sSup ((halfScore v 0).eval '' Icc 0 1)

private theorem eval_le_atomSupport (v : Primitive) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (halfScore v 0).eval u ≤ atomSupport v := by
  have hc : Continuous (halfScore v 0).eval := by
    unfold Score.eval Moment.eval
    fun_prop
  exact le_csSup (isCompact_Icc.image hc).bddAbove ⟨u, hu, rfl⟩

/-- The supremum of the signed linear atom scores is convex. -/
theorem convexOn_atomSupport : ConvexOn ℝ univ atomSupport := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  change
    sSup ((halfScore (a • x + b • y) 0).eval '' Icc 0 1) ≤ a * atomSupport x + b * atomSupport y
  apply csSup_le ((nonempty_Icc.mpr zero_le_one).image _)
  rintro _ ⟨u, hu, rfl⟩
  have hlin : (halfScore (a • x + b • y) 0).eval u =
      a * (halfScore x 0).eval u + b * (halfScore y 0).eval u := by
    simp [halfScore, Score.eval, smul_eq_mul]
    ring
  rw [hlin]
  exact add_le_add (mul_le_mul_of_nonneg_left (eval_le_atomSupport x hu) ha)
    (mul_le_mul_of_nonneg_left (eval_le_atomSupport y hu) hb)

/-- The maximum of the same three-support score over exactly the ordered pairs
of control indices, including the three diagonal pairs. -/
def orderedPairMax (H : Primitive → ℝ) (C : Fin 3 → Primitive) (L R : Primitive) : ℝ :=
  (Finset.univ.filter fun p : Fin 3 × Fin 3 ↦ p.1 ≤ p.2).sup'
    ⟨(0, 0), by simp⟩ (fun p ↦ price H L R (C p.1) (C p.2))

/-- Closed same-cell ordered two-knot interpolation for the signed atom support. -/
theorem atomSupport_price_le_orderedPairMax (C : Fin 3 → Primitive) (L R : Primitive) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    price atomSupport L R (quadratic C s) (quadratic C t) ≤ orderedPairMax atomSupport C L R := by
  refine price_le_of_pair_bounds atomSupport convexOn_atomSupport C L R hs hst ht ?_
  intro i j hij
  have hmem : (i, j) ∈ (Finset.univ.filter fun p : Fin 3 × Fin 3 ↦ p.1 ≤ p.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  unfold orderedPairMax
  exact Finset.le_sup' (fun p : Fin 3 × Fin 3 ↦ price atomSupport L R (C p.1) (C p.2)) hmem

end

end Masullo.OrderedTwoKnotPrice
