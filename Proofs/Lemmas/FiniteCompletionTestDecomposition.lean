module

public import Lemmas.FiniteCompletionAddHaar
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-! # A finite principal-ball decomposition for finite completions -/

open Function IsDedekindDomain Metric NumberField Set

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

/-- A locally constant test vanishing off the integer ring is a finite sum over
that ring's disjoint balls of one radius realized by a completion unit. -/
public theorem finiteCompletionTest_eq_sum_principalBalls {E : Type*} [AddCommMonoid E]
    {u : F → E} (hu : IsLocallyConstant u) (hzero : ∀ x, x ∉ O → u x = 0) :
    ∃ (r : Fˣ) (s : Finset (Set F)) (a : s → O), ∀ x : F,
      u x = ∑ i : s, ({y : F | (↑r⁻¹ : F) * (y - (a i : F)) ∈ O} : Set F).indicator
        (fun _ ↦ u (a i : F)) x := by
  classical
  have hk : IsCompact (O : Set F) := isCompact_iff_compactSpace.mpr
    (compactSpace_finiteCompletionIntegers K v)
  let U (z : E) := {x : F | u x = z}
  obtain ⟨δ, hδ, hU⟩ := lebesgue_number_lemma_of_metric hk hu.isOpen_fiber
    (c := U) (fun x _ ↦ mem_iUnion.mpr ⟨u x, rfl⟩)
  obtain ⟨π, hπ⟩ := (Valued.v : Valuation F (WithZero (Multiplicative ℤ)))
    |>.exists_isUniformizer_of_isCyclic_of_nontrivial
  have hπ_norm : ‖(π : F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (lt_min hδ zero_lt_one) hπ_norm
  let r : Fˣ := Units.mk0 (π : F) hπ.ne_zero ^ n
  let ρ := ‖(r : F)‖
  have hρ : 0 < ρ := norm_pos_iff.mpr r.ne_zero
  have hsmall : ρ < min δ 1 := by simpa [ρ, r, norm_pow] using hn
  have hball (a : F) : {x : F | (↑r⁻¹ : F) * (x - a) ∈ O} = closedBall a ρ := by
    ext x
    change (↑r⁻¹ : F) * (x - a) ∈ (O : Set F) ↔ x ∈ closedBall a ρ
    simp only [finiteCompletionIntegers_eq_closedBall v, mem_closedBall, dist_eq_norm,
      sub_zero, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, norm_div, div_le_iff₀ hρ,
      one_mul, ρ]
  let C (x : O) := closedBall (x : F) ρ
  have hCsubset (a : O) : C a ⊆ (O : Set F) := by
    intro x hx
    have ha : (a : F) ∈ (O : Set F) := a.property
    rw [finiteCompletionIntegers_eq_closedBall v] at ha ⊢
    exact (IsUltrametricDist.dist_triangle_max x (a : F) 0).trans
      (max_le ((mem_closedBall.mp hx).trans (hsmall.trans_le (min_le_right ..)).le)
        (mem_closedBall.mp ha))
  have hconst (a : O) {x : F} (hx : x ∈ C a) : u x = u (a : F) := by
    obtain ⟨z, hz⟩ := hU a a.property
    exact (hz ((mem_closedBall.mp hx).trans_lt (hsmall.trans_le (min_le_left ..)))).trans
      (hz (mem_ball_self hδ)).symm
  obtain ⟨t, ht⟩ := hk.elim_finite_subcover C
    (fun a ↦ IsUltrametricDist.isOpen_closedBall (a : F) hρ.ne') (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_closedBall_self hρ.le⟩)
  let s := t.image C
  have hpre (i : s) : ∃ a ∈ t, C a = i.val := Finset.mem_image.mp i.property
  choose a ha hC using hpre
  have hdisj {i j : s} (h : i ≠ j) : Disjoint (C (a i)) (C (a j)) := by
    rcases IsUltrametricDist.closedBall_eq_or_disjoint (a i : F) (a j : F) ρ with e | d
    · exact False.elim (h (Subtype.ext ((hC i).symm.trans (e.trans (hC j)))))
    · exact d
  have hcover {x : F} (hx : x ∈ O) : ∃ i : s, x ∈ C (a i) := by
    obtain ⟨y, hy⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
    let i : s := ⟨C y, Finset.mem_image.mpr ⟨y, hyt, rfl⟩⟩
    exact ⟨i, (hC i).symm ▸ hxy⟩
  refine ⟨r, s, a, fun x ↦ ?_⟩
  simp only [hball]
  change u x = ∑ i : s, (C (a i)).indicator (fun _ ↦ u (a i : F)) x
  by_cases hx : x ∈ O
  · obtain ⟨i, hi⟩ := hcover hx
    rw [Finset.sum_eq_single i, indicator_of_mem hi]
    · exact hconst (a i) hi
    · intro j _ hji
      exact indicator_of_notMem (fun hj ↦ Set.disjoint_left.mp (hdisj hji) hj hi) _
    · simp
  · rw [hzero x hx]
    symm
    exact Finset.sum_eq_zero fun i _ ↦ indicator_of_notMem (fun hi ↦ hx (hCsubset (a i) hi)) _

end Masullo
