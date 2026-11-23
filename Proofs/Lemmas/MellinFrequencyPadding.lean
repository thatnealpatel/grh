module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Pad a Mellin frequency family for the sequence filter -/

open Function Set

namespace Masullo

/-- Embed any countable family into a sequence, filling unused slots by
nonreal frequencies with total extra displacement at most `δ`. This includes
empty and finite families; each index of the given family is used exactly once
by the embedding. -/
public theorem exists_mellinFrequency_sequence {ι : Type*} [Countable ι] (z : ι → ℂ)
    (hz : ∀ i, (z i).im ≠ 0) (hs : Summable (fun i ↦ Real.pi / |(z i).im|))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : ℕ → ℂ, (∀ n, (w n).im ≠ 0) ∧
      Summable (fun n ↦ Real.pi / |(w n).im|) ∧
      (∑' n, Real.pi / |(w n).im|) ≤ (∑' i, Real.pi / |(z i).im|) + δ ∧
      range z ⊆ range w := by
  obtain ⟨e, he⟩ := exists_injective_nat ι
  let cost (v : ℂ) := Real.pi / |v.im|
  let c : ℕ → ℝ := Function.extend e (fun i ↦ cost (z i)) 0
  have hc : HasSum c (∑' i, cost (z i)) := (hasSum_extend_zero he).mpr hs.hasSum
  -- The dummy frequency in slot n costs δ/2 times the nth term of a geometric series.
  let d (n : ℕ) : ℝ := δ / 2 * (1 / 2) ^ n
  have hd : HasSum d δ := by
    convert (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).mul_left (δ / 2) using 1
    norm_num
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  let dummy (n : ℕ) : ℂ := ⟨0, Real.pi / d n⟩
  have hdim (n : ℕ) : 0 < (dummy n).im := div_pos Real.pi_pos (hdpos n)
  have hdcost (n : ℕ) : cost (dummy n) = d n := by
    change Real.pi / |(dummy n).im| = d n
    rw [abs_of_pos (hdim n)]
    change Real.pi / (Real.pi / d n) = d n
    field_simp [Real.pi_ne_zero, (hdpos n).ne']
  let w := Function.extend e z dummy
  have hw (i : ι) : w (e i) = z i := he.extend_apply z dummy i
  have hbound (n : ℕ) : (w n).im ≠ 0 ∧ cost (w n) ≤ c n + d n := by
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [hw, show c (e i) = cost (z i) from he.extend_apply _ _ _]
      exact ⟨hz i, le_add_of_nonneg_right (hdpos _).le⟩
    · rw [show w n = dummy n from extend_apply' _ _ _ hn,
          show c n = 0 from extend_apply' _ _ _ hn, hdcost, zero_add]
      exact ⟨(hdim n).ne', le_rfl⟩
  have hcd := hc.add hd
  have hws : Summable (fun n ↦ cost (w n)) := hcd.summable.of_nonneg_of_le
    (fun _ ↦ div_nonneg Real.pi_pos.le (abs_nonneg _)) (fun n ↦ (hbound n).2)
  refine ⟨w, fun n ↦ (hbound n).1, hws, ?_, ?_⟩
  · exact (hws.tsum_le_tsum (fun n ↦ (hbound n).2) hcd.summable).trans_eq hcd.tsum_eq
  · rintro _ ⟨i, rfl⟩
    exact ⟨e i, hw i⟩

end Masullo
