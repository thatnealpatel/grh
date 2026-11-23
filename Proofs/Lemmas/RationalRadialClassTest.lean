module

public import Props.IdeleClassStripTrace
public import Theorems.RationalIdeleClassHaar

import Lemmas.RationalIdeleUnitWindow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Rational radial Bruhat tests on the idèle classes -/

open Filter NumberField Set
open scoped Classical ContDiff Topology

namespace Masullo

/-- Extend the positive log profile by zero on the nonpositive half-line. -/
private noncomputable def positiveLogProfile (F : ℝ → ℂ) (y : ℝ) : ℂ :=
  if 0 < y then F (Real.log y) else 0

private theorem contDiff_positiveLogProfile {F : ℝ → ℂ} (hf : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : ContDiff ℝ ∞ (positiveLogProfile F) := by
  obtain ⟨a, ha⟩ := hc.bddBelow
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · have hlog : ContDiffAt ℝ ∞ Real.log y := Real.contDiffAt_log.mpr hy.ne'
    apply (hf.contDiffAt.comp y hlog).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact ite_eq_left (show 0 < t from ht)
  · -- The lower support bound makes the extension zero on a neighborhood of `y`.
    have hy' : y < Real.exp a := (le_of_not_gt hy).trans_lt (Real.exp_pos a)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hy'] with t ht
    by_cases ht' : 0 < t
    · rw [positiveLogProfile, ite_eq_left ht']
      by_contra hF
      exact (not_lt_of_ge (ha (subset_tsupport F hF)))
        ((Real.log_lt_iff_lt_exp ht').mpr ht)
    · exact ite_eq_right ht'

/-- A smooth compactly supported profile of the log norm is a Bruhat test on the
rational idèle classes. -/
public theorem isIdeleClassTest_rationalRadial {F : ℝ → ℂ} (hf : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    IsIdeleClassTest (fun c : RationalIdeleClasses ↦ F (Real.log (ideleClassNorm c))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hc.bddBelow
    obtain ⟨b, hb⟩ := hc.bddAbove
    have hstrip := isCompact_rationalIdeleClass_normStrip (v := Real.exp b) (Real.exp_pos a)
    refine hstrip.of_isClosed_subset (isClosed_tsupport _) ?_
    apply closure_minimal _ (isClosed_Icc.preimage continuous_ideleClassNorm)
    intro c h
    have hF : Real.log (ideleClassNorm c) ∈ tsupport F := subset_tsupport F h
    exact ⟨(Real.le_log_iff_exp_le (ideleClassNorm_pos c)).mp (ha hF),
      (Real.log_le_iff_le_exp (ideleClassNorm_pos c)).mp (hb hF)⟩
  · intro c
    let v : {w : InfinitePlace ℚ // w.IsReal} := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
    let r (z : mixedEmbedding.mixedSpace ℚ) : ℝ := z.1 v
    have hr : ContDiff ℝ ∞ r := (contDiff_apply ℝ (fun _ ↦ ℝ) v).comp contDiff_fst
    refine ⟨fun z ↦ positiveLogProfile F (ideleClassNorm c * r z),
      (contDiff_positiveLogProfile hf hc).comp (contDiff_const.mul hr), ?_⟩
    filter_upwards [isOpen_rationalIdeleUnitWindow.mem_nhds one_mem_rationalIdeleUnitWindow]
      with x hx
    -- In this window all finite norm factors are one and the real coordinate is positive.
    have hxpos : 0 < rationalIdeleReal x := hx.1
    have hfin := finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow hx
    have hnorm : ideleNorm x = rationalIdeleReal x := by
      rw [ideleNorm_eq_abs_rationalIdeleReal x hfin, abs_of_pos hxpos]
    have hcoord : r (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.val.1) = rationalIdeleReal x := rfl
    rw [map_mul, ideleClassNorm_mk, hnorm, hcoord, positiveLogProfile,
      ite_eq_left (mul_pos (ideleClassNorm_pos c) hxpos)]

end Masullo
