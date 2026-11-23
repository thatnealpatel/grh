module

public import Theorems.RationalShortStripInertia
import Theorems.StripTraceWidthLimit
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.LeftRight

/-!
# Width jumps of the short rational strip trace

The open strip takes its left limit. The signed jump from the right is the
negative full-order sum on the wall, including for an infinite wall. A
continuous extension of the tested scalar from a set accumulating on both
sides forces this sum to vanish. A zero sum for one pair of tests does not
exclude zeros on the wall. No geometric extension is constructed here.
-/

open Complex Filter MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

local notation "M[" u "]" => compactLogMellin (fun t ↦ ((u : ℝ → ℝ) t : ℂ))

/-- The signed contribution of the exact wall, with ordinary Mellin products
and one factor of the full analytic order for each distinct zero. -/
@[expose] public noncomputable def rationalShortStripWallTrace (b : ℝ) (u v : ℝ → ℝ) : ℂ :=
  -∑' ρ : {ρ : criticalStripZetaZeros | |(shiftedZetaZero ρ).re| = b},
    (zetaZeroOrder ρ.val : ℂ) * M[u] (shiftedZetaZero ρ.val) * M[v] (shiftedZetaZero ρ.val)

private theorem openSum_left {ι : Type*} (d : ι → ℝ) (t : ι → ℂ)
    (hs : Summable fun i ↦ ‖t i‖) (b : ℝ) :
    Tendsto (fun a ↦ ∑' i : {i | d i < a}, t i.val) (𝓝[<] b)
      (𝓝 (∑' i : {i | d i < b}, t i.val)) := by
  classical
  have h := tendsto_stripWidth_zeroSum (α := b) (radius := d) (full := fun _ ↦ 1)
    (edge := fun _ ↦ 0) (f := t) (fun _ ↦ Nat.zero_le _) (by simpa using hs)
  simp only [Nat.cast_one, one_mul] at h
  refine h.congr (fun a ↦ ?_)
  rw [tsum_subtype]
  apply tsum_congr
  intro i
  by_cases hi : d i < a <;> simp [stripWidthMultiplicity, Set.indicator, hi]

private theorem openSum_right {ι : Type*} (d : ι → ℝ) (t : ι → ℂ)
    (hs : Summable fun i ↦ ‖t i‖) (b : ℝ) :
    Tendsto (fun a ↦ ∑' i : {i | d i < a}, t i.val) (𝓝[>] b)
      (𝓝 ((∑' i : {i | d i < b}, t i.val) + ∑' i : {i | d i = b}, t i.val)) := by
  classical
  simp_rw [tsum_subtype]
  rw [← (hs.of_norm.indicator {i | d i < b}).tsum_add (hs.of_norm.indicator {i | d i = b})]
  apply tendsto_tsum_of_dominated_convergence hs
  · intro i
    refine tendsto_const_nhds.congr' ?_
    rcases lt_trichotomy (d i) b with hi | hi | hi
    · filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hi)] with a ha
      simp [Set.indicator, hi, ne_of_lt hi, ha]
    · filter_upwards [show ∀ᶠ a in 𝓝[>] b, b < a from eventually_mem_nhdsWithin] with a ha
      simp [Set.indicator, hi, ha]
    · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hi)] with a ha
      simp [Set.indicator, hi.not_gt, ne_of_gt hi, ha.not_gt]
  · exact Eventually.of_forall fun a i ↦ by by_cases hi : d i < a <;> simp [Set.indicator, hi]

set_option linter.concreteInstances false

section

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {b l r : ℝ} (hl : 0 < l) (hr : r + r ≤ Real.log 2) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hsu : tsupport u ⊆ Ioo l r) (hsv : tsupport v ⊆ Ioo l r)
include hl hr hu hv hsu hsv

/-- The left limit is the value of the strict strip even at an occupied wall. -/
public theorem tendsto_rationalShortStripTrace_left :
    Tendsto (fun a ↦ rationalShortStripTrace a u v) (𝓝[<] b) (𝓝 (rationalShortStripTrace b u v)) :=
  (openSum_left (fun ρ : criticalStripZetaZeros ↦ |(shiftedZetaZero ρ).re|) _
    (rationalShortStripTrace_decomposition (a := b) hl hr hu hv hsu hsv).1 b).neg

/-- The right limit includes every zero on the boundary. -/
public theorem tendsto_rationalShortStripTrace_right :
    Tendsto (fun a ↦ rationalShortStripTrace a u v) (𝓝[>] b)
      (𝓝 (rationalShortStripTrace b u v + rationalShortStripWallTrace b u v)) := by
  have h := (openSum_right (fun ρ : criticalStripZetaZeros ↦ |(shiftedZetaZero ρ).re|) _
    (rationalShortStripTrace_decomposition (a := b) hl hr hu hv hsu hsv).1 b).neg
  simpa only [rationalShortStripTrace, rationalShortStripWallTrace, rationalRadialStripZeros,
    neg_add] using h

/-- Right-minus-left width jump of a single short-window test pair. -/
public theorem tendsto_rationalShortStripTrace_jump :
    Tendsto (fun a ↦ rationalShortStripTrace a u v - rationalShortStripTrace b u v) (𝓝[>] b)
      (𝓝 (rationalShortStripWallTrace b u v)) := by
  simpa only [add_sub_cancel_left] using
    (tendsto_rationalShortStripTrace_right (b := b) hl hr hu hv hsu hsv).sub_const
      (rationalShortStripTrace b u v)

/-- Continuity at `b` is equivalent to cancellation of this tested wall sum. -/
public theorem continuousAt_rationalShortStripTrace_iff :
    ContinuousAt (fun a ↦ rationalShortStripTrace a u v) b ↔ rationalShortStripWallTrace b u v = 0 := by
  have hright := tendsto_rationalShortStripTrace_right (b := b) hl hr hu hv hsu hsv
  constructor
  · intro h
    exact add_eq_left.mp (tendsto_nhds_unique hright h.continuousWithinAt.tendsto)
  · intro hw
    rw [hw, add_zero] at hright
    exact continuousAt_iff_continuous_left'_right'.2
      ⟨tendsto_rationalShortStripTrace_left hl hr hu hv hsu hsv, hright⟩

/-- A common extension from widths approaching `b` on both sides forces the
wall sum to vanish. Neither membership of `b` in `S` nor agreement at `b` is
assumed. Continuity is only required along `S`. -/
public theorem rationalShortStripWallTrace_eq_zero_of_extension {S : Set ℝ} {E : ℝ → ℂ}
    (hleft : b ∈ closure (S ∩ Iio b)) (hright : b ∈ closure (S ∩ Ioi b))
    (hE : ContinuousWithinAt E S b) (heq : EqOn (fun a ↦ rationalShortStripTrace a u v) E S) :
    rationalShortStripWallTrace b u v = 0 := by
  have transfer (U : Set ℝ) : Tendsto (fun a ↦ rationalShortStripTrace a u v) (𝓝[S ∩ U] b) (𝓝 (E b)) := by
    apply (hE.mono (inter_subset_left (s := S) (t := U))).tendsto.congr'
    filter_upwards [show ∀ᶠ a in 𝓝[S ∩ U] b, a ∈ S ∩ U from eventually_mem_nhdsWithin] with a ha
    exact (heq ha.1).symm
  have := mem_closure_iff_nhdsWithin_neBot.mp hleft
  have := mem_closure_iff_nhdsWithin_neBot.mp hright
  have left := tendsto_nhds_unique
    ((tendsto_rationalShortStripTrace_left hl hr hu hv hsu hsv).mono_left
      (nhdsWithin_mono b inter_subset_right)) (transfer (Iio b))
  have right := tendsto_nhds_unique
    ((tendsto_rationalShortStripTrace_right hl hr hu hv hsu hsv).mono_left
      (nhdsWithin_mono b inter_subset_right)) (transfer (Ioi b))
  exact add_eq_left.mp (right.trans left.symm)

end

end Masullo
