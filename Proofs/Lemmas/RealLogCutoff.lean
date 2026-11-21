module

public import Lemmas.RealLogFourierContact
public import Lemmas.RealLogProfileHaar
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The real log cutoff in additive coordinates -/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Masullo.RealLogCutoff

/-- In the real value coordinate the log cutoff removes an interval on each
sign component. Including zero has no effect on either measure comparison. -/
@[expose] public def logValueSet (ε : ℝ) : Set ℝ :=
  {y | |y| ≤ Real.exp (-ε) ∨ Real.exp ε ≤ |y|}

public theorem measurableSet_logValueSet (ε : ℝ) : MeasurableSet (logValueSet ε) :=
  (measurableSet_le continuous_abs.measurable measurable_const).union
    (measurableSet_le measurable_const continuous_abs.measurable)

public theorem preimage_logValueSet (ε : ℝ) :
    (Units.val : ℝˣ → ℝ) ⁻¹' logValueSet ε = {y : ℝˣ | ε ≤ |Real.log (|(y : ℝ)|)|} := by
  ext y
  have h := abs_pos.mpr (Units.ne_zero y)
  change (|(y : ℝ)| ≤ Real.exp (-ε) ∨ Real.exp ε ≤ |(y : ℝ)|) ↔
    ε ≤ |Real.log (|(y : ℝ)|)|
  rw [← Real.log_le_iff_le_exp h, ← Real.le_log_iff_exp_le h, le_abs]
  constructor
  · rintro (hy | hy)
    · exact Or.inr (by linarith)
    · exact Or.inl hy
  · rintro (hy | hy)
    · exact Or.inr hy
    · exact Or.inl (by linarith)

/-- The log cutoff after translating the identity to zero. -/
@[expose] public def logAddSet (ε : ℝ) : Set ℝ := (fun z : ℝ ↦ 1 + z) ⁻¹' logValueSet ε

private theorem measurableSet_logAddSet (ε : ℝ) : MeasurableSet (logAddSet ε) :=
  (measurableSet_logValueSet ε).preimage (continuous_const.add continuous_id).measurable

private noncomputable def lower (ε : ℝ) : ℝ := 1 - Real.exp (-ε)
private noncomputable def upper (ε : ℝ) : ℝ := Real.exp ε - 1

private theorem lower_pos {ε : ℝ} (hε : 0 < ε) : 0 < lower ε :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hε))

private theorem upper_pos {ε : ℝ} (hε : 0 < ε) : 0 < upper ε :=
  sub_pos.mpr (Real.one_lt_exp_iff.mpr hε)

public theorem integrableOn_logAddSet {u : ℝ → ℂ} (hu : Integrable u) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z ↦ u z / ((|z| : ℝ) : ℂ)) (logAddSet ε) := by
  refine (RealLogFourier.integrableOn_div_abs_cutoff hu (lt_min (lower_pos hε) (upper_pos hε))).mono_set ?_
  intro z hz
  have h := abs_abs_sub_abs_le_abs_sub (1 + z) (1 : ℝ)
  rw [abs_one, show 1 + z - 1 = z by ring] at h
  change |1 + z| ≤ _ ∨ _ ≤ |1 + z| at hz
  change min (lower ε) (upper ε) ≤ |z|
  rcases hz with hz | hz
  · exact (min_le_left _ _).trans ((by unfold lower; linarith : lower ε ≤ -(|1 + z| - 1)).trans
      ((neg_le_abs _).trans h))
  · exact (min_le_right _ _).trans ((by unfold upper; linarith : upper ε ≤ |1 + z| - 1).trans
      ((le_abs_self _).trans h))

/-- Both deleted log neighborhoods disappear almost everywhere, including the
one at the negative unit, where the density of the original kernel is regular. -/
private theorem tendsto_integral_logAddSet {v : ℝ → ℂ} (hv : Integrable v) :
    Tendsto (fun ε ↦ ∫ z in logAddSet ε, v z) (𝓝[Ioi 0] 0) (𝓝 (∫ z, v z)) := by
  simp_rw [← integral_indicator (measurableSet_logAddSet _)]
  apply tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖v z‖)
  · exact .of_forall fun ε ↦ hv.aestronglyMeasurable.indicator (measurableSet_logAddSet ε)
  · exact .of_forall fun ε ↦ .of_forall fun z ↦ by
      by_cases hz : z ∈ logAddSet ε <;> simp [hz]
  · exact hv.norm
  · filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (-2 : ℝ)] with z hz₀ hz₂
    have hne : |1 + z| ≠ 1 := by
      intro h
      rcases abs_choice (1 + z) with hh | hh
      · exact hz₀ (by linarith)
      · exact hz₂ (by linarith)
    refine tendsto_const_nhds.congr' ?_
    suffices ∀ᶠ ε in 𝓝[Ioi 0] (0 : ℝ), z ∈ logAddSet ε by
      filter_upwards [this] with ε hε using (indicator_of_mem hε v).symm
    have hp : Tendsto Real.exp (𝓝[Ioi 0] 0) (𝓝 1) := by
      simpa using Real.continuous_exp.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
    have hn : Tendsto (fun ε : ℝ ↦ Real.exp (-ε)) (𝓝[Ioi 0] 0) (𝓝 1) := by
      simpa [Function.comp_def] using ((Real.continuous_exp.comp continuous_neg).continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
    rcases lt_or_gt_of_ne hne with h | h
    · filter_upwards [hn.eventually (eventually_gt_nhds h)] with ε hε
      exact Or.inl hε.le
    · filter_upwards [hp.eventually (eventually_lt_nhds h)] with ε hε
      exact Or.inr hε.le

private theorem integral_inv_Icc {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) :
    (∫ x in Icc a 1, x⁻¹) = -Real.log a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha',
    integral_inv_of_pos ha one_pos, one_div, Real.log_inv]

private theorem integral_model {ε : ℝ} (hε : 0 < ε) (hu : upper ε ≤ 1) :
    (∫ z in logAddSet ε, if |z| ≤ 1 then |z|⁻¹ else 0) =
      -Real.log (upper ε) - Real.log (lower ε) := by
  let P := Icc (upper ε) 1
  let N := Icc (-1) (-lower ε)
  have hl : lower ε ≤ 1 := by unfold lower; linarith [Real.exp_pos (-ε)]
  have hP : IntegrableOn (fun z : ℝ ↦ |z|⁻¹) P := by
    apply ContinuousOn.integrableOn_Icc
    exact continuous_abs.continuousOn.inv₀ fun z hz ↦
      (abs_pos.mpr (ne_of_gt ((upper_pos hε).trans_le hz.1))).ne'
  have hN : IntegrableOn (fun z : ℝ ↦ |z|⁻¹) N := by
    apply ContinuousOn.integrableOn_Icc
    exact continuous_abs.continuousOn.inv₀ fun z hz ↦
      (abs_pos.mpr (ne_of_lt (hz.2.trans_lt (neg_neg_of_pos (lower_pos hε))))).ne'
  have hd : Disjoint P N := Set.disjoint_left.mpr fun z hp hn ↦ by
    have hp' := (upper_pos hε).trans_le hp.1
    have hn' := hn.2.trans_lt (neg_neg_of_pos (lower_pos hε))
    exact (not_lt_of_ge hp'.le) hn'
  -- On the model support `|z| ≤ 1`, the translated variable `1 + z` is nonnegative.
  have hset : logAddSet ε ∩ {z : ℝ | |z| ≤ 1} = P ∪ N := by
    ext z
    change ((|1 + z| ≤ Real.exp (-ε) ∨ Real.exp ε ≤ |1 + z|) ∧ |z| ≤ 1) ↔ _
    constructor
    · rintro ⟨hz, h₁⟩
      obtain ⟨hl, hr⟩ := abs_le.mp h₁
      rw [abs_of_nonneg (by linarith)] at hz
      rcases hz with hz | hz
      · exact Or.inr ⟨hl, by dsimp [lower]; linarith⟩
      · exact Or.inl ⟨by dsimp [upper]; linarith, hr⟩
    · intro hz
      have hz' : -1 ≤ z ∧ z ≤ 1 := by
        rcases hz with hz | hz
        · exact ⟨by linarith [hz.1, upper_pos hε], hz.2⟩
        · exact ⟨hz.1, by linarith [hz.2, lower_pos hε]⟩
      refine ⟨?_, abs_le.mpr hz'⟩
      rw [abs_of_nonneg (by linarith [hz'.1])]
      rcases hz with hz | hz
      · exact Or.inr (by have := hz.1; dsimp [upper] at this; linarith)
      · exact Or.inl (by have := hz.2; dsimp [lower] at this; linarith)
  have hPm : MeasurableSet P := measurableSet_Icc
  have hNm : MeasurableSet N := measurableSet_Icc
  have hPm' : (∫ z in P, |z|⁻¹) = -Real.log (upper ε) := by
    rw [← integral_inv_Icc (upper_pos hε) hu]
    exact setIntegral_congr_fun hPm fun z hz ↦ by rw [abs_of_nonneg ((upper_pos hε).le.trans hz.1)]
  have hNm' : (∫ z in N, |z|⁻¹) = -Real.log (lower ε) := by
    rw [← integral_inv_Icc (lower_pos hε) hl, show N = Icc (-1) (-lower ε) from rfl,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_comp_neg,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hl] at hz
    change |(-z)|⁻¹ = z⁻¹
    rw [abs_neg, abs_of_nonneg ((lower_pos hε).le.trans hz.1)]
  have hm : MeasurableSet {z : ℝ | |z| ≤ 1} := measurableSet_le continuous_abs.measurable measurable_const
  rw [show (fun z : ℝ ↦ if |z| ≤ 1 then |z|⁻¹ else 0) =
    ({z : ℝ | |z| ≤ 1}).indicator (fun z ↦ |z|⁻¹) from rfl,
    setIntegral_indicator hm, hset, setIntegral_union hd hNm hP hN, hPm', hNm']
  ring

private theorem tendsto_log_ratios :
    Tendsto (fun ε : ℝ ↦ Real.log (upper ε / ε) + Real.log (lower ε / ε))
      (𝓝[Ioi 0] 0) (𝓝 0) := by
  have hp : Tendsto (fun ε : ℝ ↦ upper ε / ε) (𝓝[Ioi 0] 0) (𝓝 1) := by
    simpa [upper, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  have hder : HasDerivAt (fun ε : ℝ ↦ -(Real.exp (-ε))) 1 0 := by
    have h := ((Real.hasDerivAt_exp (-(0 : ℝ))).comp 0 (hasDerivAt_neg 0)).neg
    change HasDerivAt (fun ε : ℝ ↦ -Real.exp (-ε)) (-(Real.exp (-0) * -1)) 0 at h
    simpa using h
  have hn : Tendsto (fun ε : ℝ ↦ lower ε / ε) (𝓝[Ioi 0] 0) (𝓝 1) := by
    simpa [lower, smul_eq_mul, div_eq_mul_inv, mul_comm, sub_neg_eq_add, sub_eq_add_neg, add_comm] using
      hder.tendsto_slope_zero_right
  simpa using (((Real.continuousAt_log one_ne_zero).tendsto.comp hp).add
    ((Real.continuousAt_log one_ne_zero).tendsto.comp hn))

/-- The regular subtracted pairing has the same limit, and the two
logarithms of the moving positive-ray radii differ from `log ε` by `o(1)`. -/
public theorem tendsto_logAddSet_compensated {u : ℝ → ℂ} (hu : Integrable u)
    (hv : Integrable (RealLogFourier.unitSubtraction u)) :
    Tendsto (fun ε ↦ (1 / 2 : ℂ) * (∫ z in logAddSet ε, u z / ((|z| : ℝ) : ℂ)) +
        (Real.log ε : ℂ) * u 0) (𝓝[Ioi 0] 0)
      (𝓝 ((1 / 2 : ℂ) * ∫ z, RealLogFourier.unitSubtraction u z)) := by
  have hr := (tendsto_integral_logAddSet hv).const_mul (1 / 2 : ℂ)
  have hm : Tendsto (fun ε : ℝ ↦ u 0 / 2 *
      ((Real.log (upper ε / ε) + Real.log (lower ε / ε) : ℝ) : ℂ)) (𝓝[Ioi 0] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_log_ratios).const_mul (u 0 / 2)
  have hd := hr.sub hm
  rw [sub_zero] at hd
  refine hd.congr' ?_
  have hsmall : ∀ᶠ ε in 𝓝[Ioi 0] (0 : ℝ), upper ε ≤ 1 := by
    have ht : Tendsto upper (𝓝 (0 : ℝ)) (𝓝 0) := by
      have h : Continuous upper := Real.continuous_exp.sub continuous_const
      simpa [upper] using (h.continuousAt (x := (0 : ℝ))).tendsto
    exact nhdsWithin_le_nhds ((ht.eventually (eventually_lt_nhds zero_lt_one)).mono fun _ h ↦ h.le)
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with ε hε hε'
  have hε₀ : 0 < ε := hε
  have hdiff : (∫ z in logAddSet ε, u z / ((|z| : ℝ) : ℂ)) -
      (∫ z in logAddSet ε, RealLogFourier.unitSubtraction u z) =
      u 0 * ((-Real.log (upper ε) - Real.log (lower ε) : ℝ) : ℂ) := by
    rw [← integral_sub (integrableOn_logAddSet hu hε₀) hv.integrableOn]
    have he (z : ℝ) : u z / ((|z| : ℝ) : ℂ) - RealLogFourier.unitSubtraction u z =
        u 0 * (((if |z| ≤ 1 then |z|⁻¹ else 0) : ℝ) : ℂ) := by
      by_cases hz : |z| ≤ 1 <;> simp [RealLogFourier.unitSubtraction, hz, div_eq_mul_inv, sub_mul]
    simp_rw [he]
    rw [integral_const_mul, integral_complex_ofReal, integral_model hε₀ hε']
  rw [Real.log_div (upper_pos hε₀).ne' hε₀.ne', Real.log_div (lower_pos hε₀).ne' hε₀.ne']
  push_cast at hdiff ⊢
  linear_combination -hdiff / 2

/-- The density in (B.4.4.2), before multiplying by half of full Haar. -/
@[expose] public noncomputable def _root_.Masullo.realLogProfileHaarKernel (F : ℝ → ℂ) (y : ℝˣ) : ℂ :=
  F (Real.log |(y : ℝ)|) * ((|(y : ℝ)| ^ (1 / 2 : ℝ) : ℝ) : ℂ) /
    ((|1 - (y : ℝ)| : ℝ) : ℂ)

/-- Transport the log cutoff by first using the real Haar density and
then translating the identity to zero. -/
public theorem haar_logCutoff_eq {F : ℝ → ℂ} (hu : Integrable (realLogProfileAdditive F))
    {ε : ℝ} (hε : 0 < ε) :
    let μ := (1 / 2 : ℝ≥0∞) • realMultiplicativeHaar
    let s := {y : ℝˣ | ε ≤ |Real.log (|(y : ℝ)|)|}
    IntegrableOn (realLogProfileHaarKernel F) s μ ∧
      (∫ y in s, realLogProfileHaarKernel F y ∂μ) =
        (1 / 2 : ℂ) * (∫ z in logAddSet ε, realLogProfileAdditive F z / ((|z| : ℝ) : ℂ)) := by
  obtain ⟨hd, he⟩ := RealLogProfileHaar.density_set F (measurableSet_logValueSet ε)
  obtain ⟨ht, ht'⟩ := RealLogProfileHaar.translate_set (realLogProfileAdditive F) (logValueSet ε)
  have hi := hd.mpr (ht.mp (integrableOn_logAddSet hu hε))
  dsimp only
  rw [← preimage_logValueSet ε]
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, Measure.restrict_smul]
    exact hi.smul_measure (by norm_num)
  · have he' : (∫ y in Units.val ⁻¹' logValueSet ε,
        realLogProfileHaarKernel F y ∂realMultiplicativeHaar) = _ := he
    rw [Measure.restrict_smul, integral_smul_measure, he', ← ht']
    norm_num [Complex.real_smul, logAddSet]

end Masullo.RealLogCutoff
