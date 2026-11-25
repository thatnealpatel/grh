module

public import Lemmas.UnitIntervalMellinEval
public import Lemmas.BalancedFractMellin
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # An interior zeta zero obstructs unit-interval approximation -/

open Complex MeasureTheory Set

namespace Masullo

/-- Lebesgue measure restricted to the open unit interval. -/
public noncomputable abbrev unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Ioo 0 1)

/-- The balanced unit-interval fractional-part column with scale `a`. -/
@[expose] public noncomputable def balancedFract (a x : ℝ) : ℂ :=
  ofReal (Int.fract (a / x)) - a * ofReal (Int.fract (1 / x))

private theorem memLp_balancedFract (a : ℝ) :
    MemLp (balancedFract a) 2 unitIntervalMeasure := by
  have hm (b : ℝ) : Measurable (fun x : ℝ ↦ ofReal (Int.fract (b / x))) :=
    continuous_ofReal.measurable.comp (measurable_fract.comp (measurable_const.div measurable_id))
  have : IsFiniteMeasure unitIntervalMeasure := by
    change IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo 0 1))
    exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; simp⟩
  have hmeas : Measurable (balancedFract a) := (hm a).sub (measurable_const.mul (hm 1))
  refine MemLp.of_bound hmeas.aestronglyMeasurable (1 + ‖(a : ℂ)‖) ?_
  refine Filter.Eventually.of_forall fun x ↦ ?_
  have hb (y : ℝ) : ‖ofReal (Int.fract y)‖ ≤ 1 := by
    rw [norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  unfold balancedFract
  refine (norm_sub_le _ _).trans (add_le_add (hb _) ?_)
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb (1 / x)) (norm_nonneg (a : ℂ))

/-- A balanced column as an element of the unit-interval `L²` space. -/
public noncomputable def balancedFractLp (a : ℝ) : Lp ℂ 2 unitIntervalMeasure :=
  (memLp_balancedFract a).toLp (balancedFract a)

/-- The closed complex span of the balanced columns with scales in `(0,1)`. -/
public noncomputable def balancedFractClosedSpan : Submodule ℂ (Lp ℂ 2 unitIntervalMeasure) :=
  (Submodule.span ℂ (balancedFractLp '' Ioo 0 1)).topologicalClosure

/-- Each right-of-center critical-strip zero gives a positive lower bound for the
full-family approximation distance of the constant function `1`. -/
public theorem sqrt_div_norm_le_infDist_balancedFractClosedSpan {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hρ₁ : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
    Real.sqrt (2 * ρ.re - 1) / ‖ρ‖ ≤ Metric.infDist
      ((memLp_const (μ := unitIntervalMeasure) (p := 2) (1 : ℂ)).toLp (fun _ : ℝ ↦ 1))
      (balancedFractClosedSpan : Set (Lp ℂ 2 unitIntervalMeasure)) := by
  let one := (memLp_const (μ := unitIntervalMeasure) (p := 2) (1 : ℂ)).toLp (fun _ : ℝ ↦ 1)
  obtain ⟨F, hF, happly, hone⟩ := exists_unitInterval_mellinEval ρ hρ
  have hker : balancedFractClosedSpan ≤ F.ker := by
    apply Submodule.topologicalClosure_minimal _ _ F.isClosed_ker
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ha, rfl⟩
    change F ((memLp_balancedFract a).toLp (balancedFract a)) = 0
    rw [(happly _ (memLp_balancedFract a)).2]
    unfold balancedFract
    rw [integral_balancedFract_mul_cpow ha.1 ha.2.le (by linarith) hρ₁, hzero, zero_div, mul_zero]
  have hs : 0 < Real.sqrt (2 * ρ.re - 1) := Real.sqrt_pos.2 (by linarith)
  change _ ≤ Metric.infDist one _
  apply (Metric.le_infDist ⟨0, balancedFractClosedSpan.zero_mem⟩).mpr
  intro y hy
  have hy' : F y = 0 := hker hy
  have hle := F.le_opNorm (one - y)
  change F one = ρ⁻¹ at hone
  rw [map_sub, hone, hy', sub_zero, norm_inv, hF] at hle
  rw [dist_eq_norm, div_eq_mul_inv, mul_comm]
  rw [mul_comm, ← div_eq_mul_inv] at hle
  exact (le_div_iff₀ hs).mp hle

end Masullo
