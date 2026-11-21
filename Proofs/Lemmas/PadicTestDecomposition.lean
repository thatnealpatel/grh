module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # A finite ball decomposition for rational local tests -/

open scoped Padic BigOperators
open Function Set Metric

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

/-- A compactly supported locally constant function vanishing at zero is
assembled from finitely many equal-radius balls avoiding zero. -/
public theorem padicTest_eq_sum_closedBalls {E : Type*} [AddCommMonoid E]
    {u : ℚ_[p] → E} (hu : IsLocallyConstant u) (hc : HasCompactSupport u) (h₀ : u 0 = 0) :
    ∃ (n : ℕ) (s : Finset (Set ℚ_[p])) (a : s → ℚ_[p]),
      (∀ i, ((p : ℝ)⁻¹) ^ n < ‖a i‖) ∧
      u = fun x ↦ ∑ i : s, (closedBall (a i) (((p : ℝ)⁻¹) ^ n)).indicator (fun _ ↦ u (a i)) x := by
  classical
  let U (v : E) := {x : ℚ_[p] | u x = v}
  have hopen (v : E) : IsOpen (U v) := hu.isOpen_fiber v
  have hsupp : tsupport u = support u := by
    apply (show IsClosed (support u) from (hopen 0).isClosed_compl).closure_eq
  have hk : IsCompact (support u) := hsupp ▸ hc
  obtain ⟨δ, hδ, hf⟩ := lebesgue_number_lemma_of_metric hk hopen (by
    intro x _
    exact mem_iUnion.mpr ⟨u x, rfl⟩)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ hp)
  let r := ((p : ℝ)⁻¹) ^ n
  have hr : 0 < r := pow_pos (inv_pos.mpr (zero_lt_one.trans hp)) n
  let C (x : support u) := closedBall (x : ℚ_[p]) r
  have hconst (x : support u) {y : ℚ_[p]} (hy : y ∈ C x) : u y = u x := by
    obtain ⟨v, hv⟩ := hf x x.property
    exact (hv ((mem_closedBall.mp hy).trans_lt hn)).trans
      (hv (mem_ball_self hδ)).symm
  obtain ⟨t, ht⟩ := hk.elim_finite_subcover C
    (fun x ↦ IsUltrametricDist.isOpen_closedBall (x : ℚ_[p]) hr.ne') (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_closedBall_self hr.le⟩)
  let s := t.image C
  have hpre (i : s) : ∃ x ∈ t, C x = i.val := Finset.mem_image.mp i.property
  choose b hb hC using hpre
  have hsep (i : s) : r < ‖(b i : ℚ_[p])‖ := by
    by_contra! h
    have hmem : (0 : ℚ_[p]) ∈ C (b i) := by
      simpa [C, dist_zero_left] using h
    exact (b i).property ((hconst (b i) hmem).symm.trans h₀)
  have hdisj {i j : s} (h : i ≠ j) : Disjoint (C (b i)) (C (b j)) := by
    rcases IsUltrametricDist.closedBall_eq_or_disjoint (b i : ℚ_[p]) (b j : ℚ_[p]) r with e | d
    · exact False.elim (h (Subtype.ext ((hC i).symm.trans (e.trans (hC j)))))
    · exact d
  have hcover {x : ℚ_[p]} (hx : x ∈ support u) : ∃ i : s, x ∈ C (b i) := by
    obtain ⟨y, hy⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
    let i : s := ⟨C y, Finset.mem_image.mpr ⟨y, hyt, rfl⟩⟩
    exact ⟨i, (hC i).symm ▸ hxy⟩
  refine ⟨n, s, fun i ↦ b i, hsep, ?_⟩
  funext x
  change u x = ∑ i : s, (C (b i)).indicator (fun _ ↦ u (b i)) x
  by_cases hx : x ∈ support u
  · obtain ⟨i, hi⟩ := hcover hx
    rw [Finset.sum_eq_single i, indicator_of_mem hi]
    · exact hconst (b i) hi
    · intro j _ hji
      exact indicator_of_notMem (fun hj ↦ Set.disjoint_left.mp (hdisj hji) hj hi) _
    · simp
  · have hz : u x = 0 := notMem_support.mp hx
    rw [hz, Finset.sum_eq_zero]
    intro i _
    exact indicator_of_notMem (fun hi ↦ (b i).property ((hconst (b i) hi).symm.trans hz)) _

end Masullo
