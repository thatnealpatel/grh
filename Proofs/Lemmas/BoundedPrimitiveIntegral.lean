module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Filter MeasureTheory Set
open scoped Topology

namespace Masullo

private theorem primitive_hasDerivWithinAt_right
    {A B : ℝ → ℂ} {a : ℂ} (hA : Measurable A)
    (hAr : ∀ x ≥ 1, ContinuousWithinAt A (Ici x) x)
    (hB : ∀ x, B x = ∫ t in (1 : ℝ)..x, (A t - a))
    {x : ℝ} (hx : 1 ≤ x) (hi : IntervalIntegrable (fun t ↦ A t - a) volume 1 x) :
    HasDerivWithinAt B (A x - a) (Ioi x) x := by
  rw [show B = fun y ↦ ∫ t in (1 : ℝ)..y, (A t - a) from funext hB]
  have h : HasDerivWithinAt (fun y ↦ ∫ t in (1 : ℝ)..y, (A t - a)) (A x - a)
      (Ici x) x :=
    intervalIntegral.integral_hasDerivWithinAt_right hi
      (hA.sub_const a).stronglyMeasurable.stronglyMeasurableAtFilter
      (((hAr x hx).sub continuousWithinAt_const).mono Ioi_subset_Ici_self)
  exact h.mono Ioi_subset_Ici_self

private theorem primitive_cpow_parts_on_interval
    {A B : ℝ → ℂ} {a w : ℂ}
    (hB' : ∀ x ≥ 1, HasDerivWithinAt B (A x - a) (Ioi x) x)
    (hBc : ContinuousOn B (Ici 1)) (hB₁ : B 1 = 0)
    (hD : ∀ x : ℝ, 1 ≤ x → HasDerivAt (fun t : ℝ ↦ (t : ℂ)^(-(w + 1)))
      (-(w + 1) * (x : ℂ)^(-(w + 2))) x)
    {y : ℝ} (hy : 1 ≤ y)
    (hi : IntervalIntegrable (fun t ↦ (A t - a) * (t : ℂ)^(-(w + 1))) volume 1 y)
    (hj : IntervalIntegrable (fun t ↦ B t * (t : ℂ)^(-(w + 2))) volume 1 y) :
    (∫ t in (1 : ℝ)..y, (A t - a) * (t : ℂ)^(-(w + 1))) -
      (w + 1) * (∫ t in (1 : ℝ)..y, B t * (t : ℂ)^(-(w + 2))) =
      B y * (y : ℂ)^(-(w + 1)) := by
  have hcont : ContinuousOn (fun t ↦ B t * (t : ℂ)^(-(w + 1))) (Icc 1 y) :=
    (hBc.mono Icc_subset_Ici_self).mul fun x hx ↦ (hD x hx.1).continuousAt.continuousWithinAt
  have hj' := hj.const_mul (w + 1)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hy hcont
    (f' := fun t ↦ (A t - a) * (t : ℂ)^(-(w + 1)) - (w + 1) * (B t * (t : ℂ)^(-(w + 2))))
    (fun x hx ↦ by
      convert (hB' x hx.1.le).mul (hD x hx.1.le).hasDerivWithinAt using 1
      ring)
    (hi.sub hj')
  simpa only [intervalIntegral.integral_sub hi hj', intervalIntegral.integral_const_mul,
    hB₁, zero_mul, sub_zero] using h

/-- A bounded measurable multiplier preserves integrability of a complex power on `(1, ∞)`
when the exponent has real part strictly below `-1`. -/
public theorem bounded_mul_cpow_integrable
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))))
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ≥ 1, ‖f x‖ ≤ M) {r : ℂ} (hr : r.re < -1) :
    IntegrableOn (fun x : ℝ ↦ f x * (x : ℂ)^r) (Ioi (1 : ℝ)) := by
  obtain ⟨M, _, hM⟩ := hb
  have hk := integrableOn_Ioi_cpow_of_lt hr (zero_lt_one : (0 : ℝ) < 1)
  refine (hk.norm.const_mul M).mono' (hf.mul hk.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM x hx.le) (norm_nonneg _)

/-- An improper integration-by-parts step for a bounded function with a bounded centered
primitive, assuming only right continuity on the tail. -/
public theorem boundedPrimitive_integral_step
    {A B : ℝ → ℂ} {a : ℂ}
    (hA : Measurable A)
    (hAb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ≥ 1, ‖A x‖ ≤ M)
    (hAr : ∀ x ≥ 1, ContinuousWithinAt A (Set.Ici x) x)
    (hB : ∀ x, B x = ∫ t in (1 : ℝ)..x, (A t - a))
    (hBb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ≥ 1, ‖B x‖ ≤ M)
    {w : ℂ} (hw : 0 < w.re) :
    w * (∫ x in Set.Ioi (1 : ℝ), A x * (x : ℂ)^(-(w+1))) =
      a + w * (w+1) * (∫ x in Set.Ioi (1 : ℝ), B x * (x : ℂ)^(-(w+2))) := by
  obtain ⟨M, hM₀, hM⟩ := hAb
  have hAg (x : ℝ) (hx : 1 ≤ x) : ‖A x - a‖ ≤ M + ‖a‖ :=
    (norm_sub_le _ _).trans (add_le_add (hM x hx) le_rfl)
  have hAm : Measurable (fun x ↦ A x - a) := hA.sub_const a
  have hAi (y : ℝ) (hy : 1 ≤ y) :
      IntervalIntegrable (fun x ↦ A x - a) volume 1 y := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
    have hc : IntegrableOn (fun _ : ℝ ↦ M + ‖a‖) (Ioc 1 y) :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine hc.mono' hAm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hAg x hx.1.le
  have hBc : ContinuousOn B (Ici 1) := by
    intro x hx
    have hlt : x < x + 1 := lt_add_one x
    have hy : 1 ≤ x + 1 := hx.trans hlt.le
    have hc := intervalIntegral.continuousOn_primitive_interval' (hAi (x + 1) hy) left_mem_uIcc
    rw [← show B = fun y ↦ ∫ t in (1 : ℝ)..y, (A t - a) from funext hB, uIcc_of_le hy] at hc
    exact (continuousWithinAt_inter (Iic_mem_nhds hlt)).mp
      (by rw [Ici_inter_Iic]; exact hc x ⟨hx, hlt.le⟩)
  have hB' (x : ℝ) (hx : 1 ≤ x) : HasDerivWithinAt B (A x - a) (Ioi x) x :=
    primitive_hasDerivWithinAt_right hA hAr hB hx (hAi x hx)
  have hB₁ : B 1 = 0 := by rw [hB, intervalIntegral.integral_same]
  have hp : (-(w + 1)).re < -1 := by
    rw [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith
  have hq : (-(w + 2)).re < -1 := by
    rw [Complex.neg_re, Complex.add_re, Complex.re_ofNat]
    linarith
  have hD (x : ℝ) (hx : 1 ≤ x) : HasDerivAt (fun t : ℝ ↦ (t : ℂ)^(-(w + 1)))
      (-(w + 1) * (x : ℂ)^(-(w + 2))) x := by
    have hp₀ : -(w + 1) ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hp
      norm_num at hp
    rw [show -(w + 2) = -(w + 1) - 1 by ring]
    exact hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le hx).ne' hp₀
  have hi := bounded_mul_cpow_integrable hAm.aestronglyMeasurable
    ⟨M + ‖a‖, add_nonneg hM₀ (norm_nonneg a), hAg⟩ hp
  have hj := bounded_mul_cpow_integrable
    ((hBc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) hBb hq
  -- The boundary term vanishes, by the real-power norm on the positive tail.
  have hdecay : Tendsto (fun x : ℝ ↦ B x * (x : ℂ)^(-(w + 1))) atTop (𝓝 0) := by
    obtain ⟨N, _, hN⟩ := hBb
    have hlim : Tendsto (fun x : ℝ ↦ N * x ^ (-(w + 1)).re) atTop (𝓝 0) := by
      have hn : 0 < -(-(w + 1)).re := by linarith
      simpa only [neg_neg, mul_zero] using (tendsto_rpow_neg_atTop hn).const_mul N
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
    exact mul_le_mul_of_nonneg_right (hN x hx) (Real.rpow_nonneg (zero_le_one.trans hx) _)
  have hparts : (∫ x in Ioi (1 : ℝ), (A x - a) * (x : ℂ)^(-(w + 1))) =
      (w + 1) * (∫ x in Ioi (1 : ℝ), B x * (x : ℂ)^(-(w + 2))) := by
    apply sub_eq_zero.mp
    refine tendsto_nhds_unique
      ((intervalIntegral_tendsto_integral_Ioi 1 hi tendsto_id).sub
        ((intervalIntegral_tendsto_integral_Ioi 1 hj tendsto_id).const_mul (w + 1))) ?_
    refine hdecay.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact (primitive_cpow_parts_on_interval hB' hBc hB₁ hD hy
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr (hi.mono_set Ioc_subset_Ioi_self))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr (hj.mono_set Ioc_subset_Ioi_self))).symm
  -- The constant term is computed by the power antiderivative on `(1, ∞)`.
  have hw₀ : w ≠ 0 := by rintro rfl; simp at hw
  have hk : (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ)^(-(w + 1))) = w⁻¹ := by
    rw [integral_Ioi_cpow_of_lt hp zero_lt_one, show -(w + 1) + 1 = -w by ring]
    simp [div_eq_mul_inv]
  have ha := (integrableOn_Ioi_cpow_of_lt hp (zero_lt_one : (0 : ℝ) < 1)).const_mul a
  have hsplit : (∫ x in Ioi (1 : ℝ), A x * (x : ℂ)^(-(w + 1))) =
      (∫ x in Ioi (1 : ℝ), (A x - a) * (x : ℂ)^(-(w + 1))) +
      a * (∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ)^(-(w + 1))) := by
    rw [← integral_const_mul, ← integral_add hi ha]
    congr 1
    funext x
    ring
  rw [hsplit, hparts, hk, mul_add, ← mul_assoc]
  have hcancel : w * (a * w⁻¹) = a := by
    rw [mul_left_comm, mul_inv_cancel₀ hw₀, mul_one]
  rw [hcancel, add_comm]

end Masullo
