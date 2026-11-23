module

public import Lemmas.FloorGridPhysical
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Phase means of physical floor-grid columns

Pair on one fine dyadic shell with the inverse envelope times the Jacobian of the fine
phase coordinate. On a level-`j` column, the coarser coordinate runs through exactly
`2 ^ (J - j)` full periods, with a compensating constant Jacobian ratio.
-/

open MeasureTheory Set

namespace Masullo

private noncomputable def phaseMeanLo (J : ℕ) : ℝ := (J : ℝ) * Real.log 2
private noncomputable def phaseMeanHi (J : ℕ) : ℝ := ((J : ℝ) + 1) * Real.log 2

private theorem phaseMeanLo_le_hi (J : ℕ) : phaseMeanLo J ≤ phaseMeanHi J := by
  unfold phaseMeanLo phaseMeanHi
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.log_nonneg one_le_two)

private theorem phaseMean_envelope_pos (a x : ℝ) : 0 < floorGridEnvelope a x := by
  unfold floorGridEnvelope
  positivity

private noncomputable def phaseMeanWeight (a : ℝ) (J : ℕ) (x : ℝ) : ℝ :=
  (Real.exp x / (2 : ℝ) ^ J) / floorGridEnvelope a x

private theorem phaseMeanWeight_continuous (a : ℝ) (J : ℕ) :
    Continuous (phaseMeanWeight a J) := by
  unfold phaseMeanWeight
  refine Continuous.div (by fun_prop) ?_ (fun x ↦ (phaseMean_envelope_pos a x).ne')
  unfold floorGridEnvelope
  fun_prop

private theorem phaseMeanWeight_memLp (a : ℝ) (J : ℕ) :
    MemLp ((Icc (phaseMeanLo J) (phaseMeanHi J)).indicator (phaseMeanWeight a J)) 2 volume := by
  let s := Icc (phaseMeanLo J) (phaseMeanHi J)
  have hs : MeasurableSet s := measurableSet_Icc
  let : IsFiniteMeasure (volume.restrict s) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top (μ := volume)).ne
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (K := s)
    (phaseMeanWeight_continuous a J).norm.continuousOn
  rw [memLp_indicator_iff_restrict hs.nullMeasurableSet]
  refine MemLp.of_bound (phaseMeanWeight_continuous a J).aestronglyMeasurable C ?_
  exact ae_restrict_of_forall_mem hs fun x hx ↦ hC (mem_image_of_mem _ hx)

private noncomputable def phaseMeanTest (a : ℝ) (J : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (phaseMeanWeight_memLp a J).toLp _

/-- The normalized phase mean at level `J`, as a continuous real linear functional on the
physical `L²` space. Its test vector is supported on the level-`J` dyadic shell. -/
public noncomputable def floorGridPhaseMean (a : ℝ) (J : ℕ) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] ℝ :=
  innerSL ℝ (phaseMeanTest a J)

/-- The phase mean applied to an arbitrary physical vector is the weighted integral of its
representative on the fine shell. -/
public theorem floorGridPhaseMean_apply (a : ℝ) (J : ℕ) (v : Lp ℝ 2 (volume : Measure ℝ)) :
    floorGridPhaseMean a J v =
      ∫ x in (J : ℝ) * Real.log 2..((J : ℝ) + 1) * Real.log 2,
        ((Real.exp x / (2 : ℝ) ^ J) / floorGridEnvelope a x) * v x := by
  change floorGridPhaseMean a J v =
    ∫ x in phaseMeanLo J..phaseMeanHi J, phaseMeanWeight a J x * v x
  rw [floorGridPhaseMean, innerSL_apply_apply, L2.inner_def,
    intervalIntegral.integral_of_le (phaseMeanLo_le_hi J), ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (phaseMeanWeight_memLp a J)] with x hx
  rw [Real.inner_apply, show phaseMeanTest a J x = _ from hx]
  by_cases hs : x ∈ Icc (phaseMeanLo J) (phaseMeanHi J) <;> simp [hs]

private noncomputable def phaseStep (k : ℕ) (t : ℝ) : ℝ :=
  ((⌊(k : ℝ) * Int.fract t⌋ : ℤ) : ℝ)

private theorem phaseStep_periodic (k : ℕ) : Function.Periodic (phaseStep k) 1 :=
  fun x ↦ by simp only [phaseStep, Int.fract_add_one]

private theorem phaseStep_intervalIntegrable (k : ℕ) (u v : ℝ) :
    IntervalIntegrable (phaseStep k) volume u v := by
  rw [intervalIntegrable_iff']
  let : IsFiniteMeasure (volume.restrict (uIcc u v)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.measure_lt_top (μ := volume)).ne
  have hm : Measurable (phaseStep k) := by
    unfold phaseStep
    fun_prop
  refine memLp_one_iff_integrable.mp (MemLp.of_bound hm.aestronglyMeasurable (k : ℝ) ?_)
  apply ae_of_all
  intro x
  have hn : (0 : ℝ) ≤ (k : ℝ) * Int.fract x := mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _)
  rw [phaseStep, Real.norm_of_nonneg (by exact_mod_cast Int.floor_nonneg.mpr hn)]
  exact (Int.floor_le _).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) (Int.fract_lt_one x).le)

private theorem phaseStep_integral_periods (k n : ℕ) :
    (∫ t in (n : ℝ)..2 * (n : ℝ), phaseStep k t) =
      (n : ℝ) * ∫ t in (0 : ℝ)..1, phaseStep k t := by
  have h := (phaseStep_periodic k).intervalIntegral_add_zsmul_eq (n : ℤ) (n : ℝ)
    (phaseStep_intervalIntegrable k)
  rw [(phaseStep_periodic k).intervalIntegral_add_eq (n : ℝ) 0] at h
  simpa [zsmul_eq_mul, two_mul] using h

private theorem phaseStep_eqOn (k : ℕ) :
    EqOn (phaseStep k) (fun t ↦ ((⌊(k : ℝ) * t⌋ : ℤ) : ℝ)) (Ioo (0 : ℝ) 1) := by
  intro t ht
  rw [phaseStep, Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩]

private theorem phaseStep_integral_two : (∫ t in (0 : ℝ)..1, phaseStep 2 t) = 1 / 2 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (phaseStep_intervalIntegrable 2 0 (1 / 2)) (phaseStep_intervalIntegrable 2 (1 / 2) 1)]
  have hlo : (∫ t in (0 : ℝ)..1 / 2, phaseStep 2 t) = ∫ _ in (0 : ℝ)..1 / 2, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    rw [phaseStep_eqOn 2 (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht.1, ht.2.trans (by norm_num)⟩)]
    have h : ⌊(2 : ℝ) * t⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa using congrArg (fun m : ℤ ↦ (m : ℝ)) h
  have hhi : (∫ t in (1 / 2 : ℝ)..1, phaseStep 2 t) = ∫ _ in (1 / 2 : ℝ)..1, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨(by norm_num : (0 : ℝ) < 1 / 2).trans ht.1, ht.2⟩
    rw [phaseStep_eqOn 2 ht']
    have h : ⌊(2 : ℝ) * t⌋ = 1 := Int.floor_eq_iff.mpr <| by
      norm_num
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa using congrArg (fun m : ℤ ↦ (m : ℝ)) h
  rw [hlo, hhi]
  norm_num

private theorem phaseMean_dyadic_integral (j J k : ℕ) (hj : j ≤ J) :
    (∫ x in phaseMeanLo J..phaseMeanHi J,
      (Real.exp x / (2 : ℝ) ^ J) * phaseStep k (Real.exp x / (2 : ℝ) ^ j)) =
        ∫ t in (0 : ℝ)..1, phaseStep k t := by
  let n : ℕ := 2 ^ (J - j)
  have hn : (n : ℝ) ≠ 0 := by dsimp [n]; positivity
  have hp : (2 : ℝ) ^ J = (2 : ℝ) ^ j * (n : ℝ) := by
    dsimp [n]
    push_cast
    rw [← pow_add, Nat.add_sub_of_le hj]
  let f (x : ℝ) := Real.exp x / (2 : ℝ) ^ j
  have hderiv (x : ℝ) : HasDerivAt f (f x) x := (Real.hasDerivAt_exp x).div_const _
  have hs := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := phaseMeanLo J) (b := phaseMeanHi J) (f := f) (f' := f) (g := phaseStep k)
    (fun x _ ↦ (hderiv x).continuousAt.continuousWithinAt)
    (fun x _ ↦ hderiv x)
    (fun x _ ↦ by dsimp [f]; positivity)
  have hlo : f (phaseMeanLo J) = (n : ℝ) := by
    simp only [f, phaseMeanLo, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), hp]
    field_simp
  have hhi : f (phaseMeanHi J) = 2 * (n : ℝ) := by
    simp only [f, phaseMeanHi, add_mul, one_mul, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), hp]
    field_simp
  have hratio (x : ℝ) : Real.exp x / (2 : ℝ) ^ J = (n : ℝ)⁻¹ * f x := by
    dsimp [f]
    rw [hp]
    field_simp
  simp only [hlo, hhi] at hs
  simp_rw [hratio, mul_assoc, intervalIntegral.integral_const_mul]
  have hs' : (∫ x in phaseMeanLo J..phaseMeanHi J, f x * phaseStep k (f x)) =
      (n : ℝ) * ∫ t in (0 : ℝ)..1, phaseStep k t := by
    simpa only [Function.comp_apply, mul_comm (f _), phaseStep_integral_periods] using hs
  change (n : ℝ)⁻¹ * (∫ x in phaseMeanLo J..phaseMeanHi J, f x * phaseStep k (f x)) = _
  rw [hs', inv_mul_cancel_left₀ hn]

private theorem floorGridPhaseMean_column_period (a : ℝ) (ha : a < 1 / 2) (j J k : ℕ)
    (hj : j ≤ J) : floorGridPhaseMean a J (floorGridColumn a ha j k) =
      ∫ t in (0 : ℝ)..1, phaseStep k t := by
  rw [floorGridPhaseMean_apply, ← phaseMean_dyadic_integral j J k hj]
  change (∫ x in phaseMeanLo J..phaseMeanHi J, _ * _) =
    (∫ x in phaseMeanLo J..phaseMeanHi J, _ * _)
  simp only [intervalIntegral.integral_of_le (phaseMeanLo_le_hi J)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (floorGridColumn_ae a ha j k)] with x hx
  simp only [hx, floorGridPhase, phaseStep]
  rw [← mul_assoc, div_mul_cancel₀ _ (phaseMean_envelope_pos a x).ne']

/-- All physical columns from levels `j ≤ J` have the flat-period phase mean at level `J`.
The formula holds for every natural `k`, in particular for all `k ≥ 2`. -/
public theorem floorGridPhaseMean_column (a : ℝ) (ha : a < 1 / 2) (j J k : ℕ)
    (hj : j ≤ J) : floorGridPhaseMean a J (floorGridColumn a ha j k) =
      ∫ t in (0 : ℝ)..1, ((⌊(k : ℝ) * t⌋ : ℤ) : ℝ) := by
  rw [floorGridPhaseMean_column_period a ha j J k hj]
  exact intervalIntegral.integral_congr_Ioo_of_le zero_le_one (phaseStep_eqOn k)

/-- A `k = 2` column has exact normalized mean `1/2` on every finer dyadic shell. -/
public theorem floorGridPhaseMean_column_two (a : ℝ) (ha : a < 1 / 2) (j J : ℕ)
    (hj : j ≤ J) : floorGridPhaseMean a J (floorGridColumn a ha j 2) = 1 / 2 := by
  rw [floorGridPhaseMean_column_period a ha j J 2 hj, phaseStep_integral_two]

end Masullo
