module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Positive complete blocks for the quadratic character modulo 8

The character χ₈ = (8/·) vanishes on even integers and has signs `+, −, −, +`
on the odd residues `1, 3, 5, 7`. For real `σ > 0`, each complete block is positive:
strict convexity of `x ↦ x ^ (-σ)` makes the slope on the later of the two
width-two intervals larger than the slope on the earlier one.

Every nonempty complete-block sum contains the same positive first block. The
resulting lower bound survives passage to a real limit, **if** the sums converge.
This file neither proves convergence nor identifies a block-sum limit with
`L(σ, χ₈)`. With that analytic identification, the bound would exclude zeros
at positive real arguments for this character only. It says nothing about
nonreal zeros or RH/GRH.
-/

open Filter Set
open scoped BigOperators Topology

namespace Chi8Block

/-- The four nonzero terms in block `m`, using real bases and real exponents. -/
@[expose] public noncomputable def block (σ : ℝ) (m : ℕ) : ℝ :=
  (8 * (m : ℝ) + 1) ^ (-σ) - (8 * (m : ℝ) + 3) ^ (-σ) -
    (8 * (m : ℝ) + 5) ^ (-σ) + (8 * (m : ℝ) + 7) ^ (-σ)

private theorem strictConvexOn_neg_rpow {σ : ℝ} (hσ : 0 < σ) :
    StrictConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ (-σ)) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi (0 : ℝ))
  · intro x hx
    exact (Real.continuousAt_rpow_const x (-σ) (Or.inl (ne_of_gt hx))).continuousWithinAt
  · rw [interior_Ioi]
    intro x hx
    change 0 < x at hx
    change 0 < deriv (deriv (fun y : ℝ => y ^ (-σ))) x
    rw [show deriv (fun y : ℝ => y ^ (-σ)) = fun y => -σ * y ^ (-σ - 1) from
        funext fun y => Real.deriv_rpow_const y (-σ)]
    rw [((Real.hasDerivAt_rpow_const (p := -σ - 1) (Or.inl hx.ne')).const_mul (-σ)).deriv,
      ← mul_assoc]
    exact mul_pos (mul_pos_of_neg_of_neg (neg_lt_zero.mpr hσ) (by linarith))
      (Real.rpow_pos_of_pos hx _)

/-- Each block is positive by comparing the slopes on its two width-two intervals. -/
public theorem block_pos {σ : ℝ} (hσ : 0 < σ) (m : ℕ) : 0 < block σ m := by
  let t : ℝ := 8 * (m : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have h1 : t + 1 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have h3 : t + 3 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have h5 : t + 5 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have h7 : t + 7 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by linarith)
  have hc := strictConvexOn_neg_rpow hσ
  -- Compare both slopes to the slope on the intervening interval [t + 3, t + 5].
  have hs := (hc.slope_strict_mono_adjacent h1 h5 (y := t + 3) (by linarith) (by linarith)).trans
    (hc.slope_strict_mono_adjacent h3 h7 (y := t + 5) (by linarith) (by linarith))
  rw [show t + 3 - (t + 1) = 2 by linarith, show t + 7 - (t + 5) = 2 by linarith] at hs
  change 0 < (t + 1) ^ (-σ) - (t + 3) ^ (-σ) - (t + 5) ^ (-σ) + (t + 7) ^ (-σ)
  linarith

/-- The sum of the first `N` complete blocks, indexed from `0` to `N - 1`. -/
@[expose] public noncomputable def blockSum (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, block σ m

/-- Every nonempty complete-block sum is bounded below by the first block. -/
public theorem first_block_le_blockSum {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) :
    block σ 0 ≤ blockSum σ N := by
  unfold blockSum
  exact Finset.single_le_sum (fun m _ => (block_pos hσ m).le) (Finset.mem_range.mpr hN)

/-- In particular, every nonempty complete-block sum is strictly positive. -/
public theorem blockSum_pos {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) :
    0 < blockSum σ N :=
  (block_pos hσ 0).trans_le (first_block_le_blockSum hσ hN)

/-- Any real limit of the complete-block sums is positive; convergence is a hypothesis. -/
public theorem limit_pos {σ L : ℝ} (hσ : 0 < σ)
    (hL : Tendsto (blockSum σ) atTop (𝓝 L)) : 0 < L := by
  apply (block_pos hσ 0).trans_le
  apply ge_of_tendsto hL
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact first_block_le_blockSum hσ hN

end Chi8Block
