module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Sharp full-period averages for finite weighted atoms

Finite-atomic part of `f8abd499:.godel/bob/sharp-period-windows.md`, lines 5–17.
The coordinates are those in the arithmetic pair sum of
`f8abd499:.godel/bob/windowed-harmonic-witness.md`, (B): use `a = y - y^2/(2*t)`
on the tuples already restricted to `|y| ≤ 8`. Atom indices, rather than their
coordinates, carry the gates, the weights, and the retained pair relation.
Coincident coordinates are not identified, and there is no further cut on the
original log frequency. Only the location law is normalized, not the atom
weights. Arithmetic reconstruction and estimates for the deleted mass are
outside this finite-atomic calculation.
-/

open MeasureTheory Set Filter
open scoped ENNReal ComplexConjugate

namespace SharpPeriodWindowPair

noncomputable section

/-- The sharp window has length one full period. -/
@[expose] public def period : ℝ := 2 * Real.pi

private theorem period_pos : 0 < period := Real.two_pi_pos

/-- Normalized Lebesgue measure on the closed interval of locations. -/
@[expose] public def locations : Measure ℝ :=
  ENNReal.ofReal period⁻¹ • volume.restrict (Icc 0 period)

public instance : IsProbabilityMeasure locations where
  measure_univ := by
    rw [locations, smul_apply, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr period_pos.le),
      inv_mul_cancel₀ period_pos.ne', ENNReal.ofReal_one]

/-- The half-open window at location `u`. -/
@[expose] public def window (u : ℝ) : Set ℝ := Ico (u - period) u

/-- For a fixed atom `a`, these are precisely the locations whose windows contain it. -/
public theorem mem_window_iff (a u : ℝ) : a ∈ window u ↔ u ∈ Ioc a (a + period) := by
  simp only [window, mem_Ico, mem_Ioc, sub_le_iff_le_add, and_comm]

/-- Window membership as a real-valued function of location. -/
@[expose] public def windowIndicator (a : ℝ) : ℝ → ℝ := (Ioc a (a + period)).indicator (fun _ => 1)

open Classical in
public theorem windowIndicator_apply (a u : ℝ) :
    windowIndicator a u = if a ∈ window u then 1 else 0 := by
  classical
  simp only [windowIndicator, indicator, mem_window_iff]

/-- The exact one-atom taper, on all of `ℝ`. -/
@[expose] public def triangle (a : ℝ) : ℝ := max 0 (1 - |a| / period)

private theorem integrable_windowIndicator (a : ℝ) :
    Integrable (windowIndicator a) locations :=
  (integrable_const (1 : ℝ)).indicator measurableSet_Ioc

/-- The included or excluded endpoints do not carry location mass. -/
public theorem integral_windowIndicator (a : ℝ) :
    ∫ u, windowIndicator a u ∂locations = triangle a := by
  have hclip : min (a + period) period - max a 0 = period - |a| := by
    by_cases ha : 0 ≤ a
    · rw [min_eq_right (by linarith), max_eq_left ha, abs_of_nonneg ha]
    · rw [min_eq_left (by linarith), max_eq_right (le_of_not_ge ha), abs_of_neg (lt_of_not_ge ha)]
      ring
  unfold locations windowIndicator triangle
  rw [← restrict_Ioc_eq_restrict_Icc, integral_smul_measure,
    integral_indicator measurableSet_Ioc, integral_const, measureReal_def,
    Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc, Real.volume_Ioc, hclip, ENNReal.toReal_ofReal (inv_nonneg.mpr period_pos.le),
    ENNReal.toReal_ofReal']
  simp only [smul_eq_mul, mul_one]
  by_cases ha : |a| ≤ period
  · rw [max_eq_left (sub_nonneg.mpr ha), max_eq_right]
    · field_simp [period_pos.ne']
    · exact sub_nonneg.mpr ((div_le_iff₀ period_pos).2 (by simpa using ha))
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge ha)), mul_zero, max_eq_left]
    exact sub_nonpos.mpr ((le_div_iff₀ period_pos).2 (by simpa using le_of_not_ge ha))

/-- The central atom has full taper; both endpoint atoms have zero taper. -/
public theorem triangle_endpoints : triangle 0 = 1 ∧ triangle period = 0 ∧ triangle (-period) = 0 := by
  simp [triangle, abs_of_pos period_pos, period_pos.ne']

variable {ι : Type*}

/-- The retained cosine box count on the ordered index pairs in `retained`. -/
@[expose] public def boxSum (a weight : ι → ℝ) (retained : Finset (ι × ι)) (u w : ℝ) : ℝ :=
  ∑ p ∈ retained, (weight p.1 * weight p.2 * Real.cos (a p.1 - a p.2)) *
    (windowIndicator (a p.1) u * windowIndicator (a p.2) w)

/-- The finite-atomic arithmetic pair sum in (B), with its original triangles. -/
@[expose] public def triangleSum (a weight : ι → ℝ) (retained : Finset (ι × ι)) : ℝ :=
  ∑ p ∈ retained, (weight p.1 * weight p.2 * Real.cos (a p.1 - a p.2)) *
    (triangle (a p.1) * triangle (a p.2))

/-- The box average for two independent uniform locations. -/
@[expose] public def independentAverage (a weight : ι → ℝ) (retained : Finset (ι × ι)) : ℝ :=
  ∫ z : ℝ × ℝ, boxSum a weight retained z.1 z.2 ∂(locations.prod locations)

/-- The box average when both copies use the same uniform location. -/
@[expose] public def commonAverage (a weight : ι → ℝ) (retained : Finset (ι × ι)) : ℝ :=
  ∫ u, boxSum a weight retained u u ∂locations

private theorem integrable_boxTerm_prod (a weight : ι → ℝ) (p : ι × ι) : Integrable
    (fun z : ℝ × ℝ => (weight p.1 * weight p.2 * Real.cos (a p.1 - a p.2)) *
      (windowIndicator (a p.1) z.1 * windowIndicator (a p.2) z.2))
    (locations.prod locations) :=
  ((integrable_windowIndicator (a p.1)).mul_prod (integrable_windowIndicator (a p.2))).const_mul _

private theorem integrable_boxSum_prod (a weight : ι → ℝ) (retained : Finset (ι × ι)) :
    Integrable (fun z : ℝ × ℝ => boxSum a weight retained z.1 z.2) (locations.prod locations) :=
  integrable_finsetSum _ (fun p _ => integrable_boxTerm_prod a weight p)

/-- Independent averaging recovers precisely the retained arithmetic test in (B).
No factorization of the retained relation itself is used. -/
public theorem independentAverage_eq_triangleSum (a weight : ι → ℝ) (retained : Finset (ι × ι)) :
    independentAverage a weight retained = triangleSum a weight retained := by
  unfold independentAverage boxSum triangleSum
  rw [integral_finsetSum _ (fun p _ => integrable_boxTerm_prod a weight p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul, integral_prod_mul, integral_windowIndicator, integral_windowIndicator]

private theorem norm_windowIndicator_le_one (a u : ℝ) : ‖windowIndicator a u‖ ≤ 1 := by
  rw [windowIndicator_apply]
  split <;> simp

private theorem integrable_boxSum_diag (a weight : ι → ℝ) (retained : Finset (ι × ι)) :
    Integrable (fun u => boxSum a weight retained u u) locations := by
  apply integrable_finsetSum
  intro p _
  exact ((integrable_windowIndicator (a p.2)).bdd_mul
    (integrable_windowIndicator (a p.1)).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_windowIndicator_le_one (a p.1)))).const_mul _

section Arcs

/-- Distance to zero after reducing modulo `2π`. -/
@[expose] public def circleDistance (x : ℝ) : ℝ := ‖(x : AddCircle period)‖

private theorem circleDistance_eq (x : ℝ) : circleDistance x = |(x : Real.Angle).toReal| := by
  let θ : Real.Angle := x
  have hcoe : (↑θ.toReal : AddCircle period) = (x : AddCircle period) := Real.Angle.coe_toReal θ
  unfold circleDistance
  rw [← hcoe, (AddCircle.norm_coe_eq_abs_iff period period_pos.ne').2]
  rw [abs_of_pos period_pos, show period / 2 = Real.pi by unfold period; ring]
  exact θ.abs_toReal_le_pi

private theorem cos_circleDistance (x : ℝ) : Real.cos (circleDistance x) = Real.cos x := by
  rw [circleDistance_eq, Real.cos_abs, Real.Angle.cos_toReal, Real.Angle.cos_coe]

private theorem circleDistance_le_pi (x : ℝ) : circleDistance x ≤ Real.pi := by
  rw [circleDistance_eq]
  exact Real.Angle.abs_toReal_le_pi _

private theorem circleDistance_sub_pi (x : ℝ) :
    circleDistance (x - Real.pi) = Real.pi - circleDistance x := by
  apply Real.injOn_cos
  · exact ⟨norm_nonneg _, circleDistance_le_pi _⟩
  · exact ⟨sub_nonneg.mpr (circleDistance_le_pi _), sub_le_self _ (norm_nonneg _)⟩
  · rw [cos_circleDistance, Real.cos_sub_pi, Real.cos_pi_sub, cos_circleDistance]

/-- The closed arc about zero minus the equal-width closed arc about π,
as a function of phase difference `x` and width `v`. -/
@[expose] public def arcDifference (x v : ℝ) : ℝ :=
  (Ici (circleDistance x)).indicator (fun _ => 1) v -
    (Ici (circleDistance (x - Real.pi))).indicator (fun _ => 1) v

private theorem half_pi_pos : 0 < Real.pi / 2 := half_pos Real.pi_pos

private theorem sin_mul_indicator (d v : ℝ) :
    Real.sin v * (Ici d).indicator (fun _ => (1 : ℝ)) v = (Ici d).indicator Real.sin v := by
  by_cases hv : v ∈ Ici d <;> simp [hv]

private theorem intervalIntegrable_sin_indicator (d : ℝ) :
    IntervalIntegrable ((Ici d).indicator Real.sin) volume 0 (Real.pi / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le half_pi_pos.le]
  exact ((Real.continuous_sin.intervalIntegrable 0 (Real.pi / 2)).1).indicator measurableSet_Ici

private theorem integral_sin_indicator {d : ℝ} (hd : 0 ≤ d) :
    (∫ v in (0 : ℝ)..(Real.pi / 2), (Ici d).indicator Real.sin v) = Real.cos (min d (Real.pi / 2)) := by
  have hclip : Ioi d ∩ Ioc 0 (Real.pi / 2) = Ioc d (Real.pi / 2) := by
    ext v
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hd.trans_lt h.1, h.2⟩⟩
  rw [intervalIntegral.integral_of_le half_pi_pos.le, integral_indicator measurableSet_Ici,
    ← restrict_Ioi_eq_restrict_Ici, Measure.restrict_restrict measurableSet_Ioi, hclip]
  by_cases h : d ≤ Real.pi / 2
  · rw [← intervalIntegral.integral_of_le h, integral_sin, Real.cos_pi_div_two, sub_zero,
      min_eq_left h]
  · rw [Ioc_eq_empty_of_le (le_of_not_ge h), Measure.restrict_empty, integral_zero_measure,
      min_eq_right (le_of_not_ge h), Real.cos_pi_div_two]

private theorem intervalIntegrable_sin_arcDifference (x : ℝ) :
    IntervalIntegrable (fun v => Real.sin v * arcDifference x v) volume 0 (Real.pi / 2) := by
  simp_rw [arcDifference, mul_sub, sin_mul_indicator]
  exact (intervalIntegrable_sin_indicator _).sub (intervalIntegrable_sin_indicator _)

/-- The single-pair arc identity used in the arithmetic harmonic witness (B). -/
public theorem integral_sin_arcDifference (x : ℝ) :
    (∫ v in (0 : ℝ)..(Real.pi / 2), Real.sin v * arcDifference x v) = Real.cos x := by
  simp_rw [arcDifference, mul_sub, sin_mul_indicator]
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_sin_indicator (circleDistance x))
    (intervalIntegrable_sin_indicator (circleDistance (x - Real.pi))),
    integral_sin_indicator (d := circleDistance x) (norm_nonneg _),
    integral_sin_indicator (d := circleDistance (x - Real.pi)) (norm_nonneg _),
    circleDistance_sub_pi, ← cos_circleDistance x]
  by_cases h : circleDistance x ≤ Real.pi / 2
  · rw [min_eq_left h, min_eq_right (by linarith), Real.cos_pi_div_two, sub_zero]
  · rw [min_eq_right (le_of_not_ge h), min_eq_left (by linarith), Real.cos_pi_div_two,
      Real.cos_pi_sub, zero_sub, neg_neg]

private theorem integral_sin_sum_arcDifference {ι : Type*} (phase coef : ι → ℝ) (s : Finset ι) :
    (∫ v in (0 : ℝ)..(Real.pi / 2), Real.sin v * ∑ p ∈ s, coef p * arcDifference (phase p) v) =
      ∑ p ∈ s, coef p * Real.cos (phase p) := by
  simp_rw [Finset.mul_sum, mul_left_comm (Real.sin _) (coef _)]
  rw [intervalIntegral.integral_finsetSum (fun p _ =>
    (intervalIntegrable_sin_arcDifference (phase p)).const_mul (coef p))]
  simp_rw [intervalIntegral.integral_const_mul, integral_sin_arcDifference]

/-- The retained box count in the closed arc about zero minus the one in the
closed arc about `π`, with the same width and sharp windows. -/
@[expose] public def boxArcDifference (a weight : ι → ℝ) (retained : Finset (ι × ι)) (u w v : ℝ) : ℝ :=
  ∑ p ∈ retained, (weight p.1 * weight p.2 *
    (windowIndicator (a p.1) u * windowIndicator (a p.2) w)) * arcDifference (a p.1 - a p.2) v

/-- The triangle-weighted version of the same arc difference, as in (B). -/
@[expose] public def triangleArcDifference (a weight : ι → ℝ) (retained : Finset (ι × ι)) (v : ℝ) : ℝ :=
  ∑ p ∈ retained, (weight p.1 * weight p.2 *
    (triangle (a p.1) * triangle (a p.2))) * arcDifference (a p.1 - a p.2) v

/-- The cosine box count is the sine-weighted integral of the sharp arc difference. -/
public theorem boxSum_eq_integral_boxArcDifference (a weight : ι → ℝ) (retained : Finset (ι × ι))
    (u w : ℝ) : boxSum a weight retained u w =
      ∫ v in (0 : ℝ)..(Real.pi / 2), Real.sin v * boxArcDifference a weight retained u w v := by
  unfold boxArcDifference
  rw [integral_sin_sum_arcDifference (fun p : ι × ι => a p.1 - a p.2)]
  unfold boxSum
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Independent boxes give the finite-atomic sine-weighted arithmetic test (B). -/
public theorem independentAverage_eq_integral_triangleArcDifference (a weight : ι → ℝ)
    (retained : Finset (ι × ι)) : independentAverage a weight retained =
      ∫ v in (0 : ℝ)..(Real.pi / 2), Real.sin v * triangleArcDifference a weight retained v := by
  rw [independentAverage_eq_triangleSum]
  unfold triangleArcDifference
  rw [integral_sin_sum_arcDifference (fun p : ι × ι => a p.1 - a p.2)]
  unfold triangleSum
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end Arcs

variable [Fintype ι]

/-- The first harmonic of the atoms in a single sharp window. -/
@[expose] public def harmonic (a weight : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ i, ((weight i * windowIndicator (a i) u : ℝ) : ℂ) * Complex.exp ((a i : ℂ) * Complex.I)

private theorem integrable_harmonic (a weight : ι → ℝ) : Integrable (harmonic a weight) locations := by
  apply integrable_finsetSum
  intro i _
  have he : (fun u => ((weight i * windowIndicator (a i) u : ℝ) : ℂ) *
      Complex.exp ((a i : ℂ) * Complex.I)) = (Ioc (a i) (a i + period)).indicator
      (fun _ => (weight i : ℂ) * Complex.exp ((a i : ℂ) * Complex.I)) := by
    funext u
    by_cases hu : u ∈ Ioc (a i) (a i + period) <;> simp [windowIndicator, hu]
  rw [he]
  exact (integrable_const _).indicator measurableSet_Ioc

/-- Only for unrestricted ordered pairs, the box sum factors through the two harmonics. -/
public theorem boxSum_univ_eq_re (a weight : ι → ℝ) (u w : ℝ) :
    boxSum a weight Finset.univ u w = (harmonic a weight u * conj (harmonic a weight w)).re := by
  classical
  unfold boxSum harmonic
  rw [map_sum, Finset.sum_mul, ← Finset.univ_product_univ, Finset.sum_product]
  simp only [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_sub]
  ring

/-- The gain from using one common location instead of two independent locations
is exactly the variance of the complex first harmonic for unrestricted pairs. -/
public theorem common_sub_independent_univ_eq_variance (a weight : ι → ℝ) :
    commonAverage a weight Finset.univ - independentAverage a weight Finset.univ =
      ∫ u, ‖harmonic a weight u - ∫ w, harmonic a weight w ∂locations‖ ^ 2 ∂locations := by
  let H := harmonic a weight
  let m := ∫ u, H u ∂locations
  have hH : Integrable H locations := integrable_harmonic a weight
  have hC : Integrable (fun u => conj (H u)) locations :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hH
  have hind : independentAverage a weight Finset.univ = Complex.normSq m := by
    simp_rw [independentAverage, boxSum_univ_eq_re]
    change (∫ z : ℝ × ℝ, (H z.1 * conj (H z.2)).re ∂(locations.prod locations)) = _
    rw [show (∫ z : ℝ × ℝ, (H z.1 * conj (H z.2)).re ∂(locations.prod locations)) =
      (∫ z : ℝ × ℝ, H z.1 * conj (H z.2) ∂(locations.prod locations)).re from
        integral_re (hH.mul_prod hC),
      integral_prod_mul (μ := locations) (ν := locations) H (fun u => conj (H u)), integral_conj]
    change (m * conj m).re = _
    simp [Complex.mul_conj]
  have hdiag (u : ℝ) : boxSum a weight Finset.univ u u = Complex.normSq (H u) := by
    simp [boxSum_univ_eq_re, H, Complex.mul_conj]
  have hE : Integrable (fun u => Complex.normSq (H u)) locations := by
    simp_rw [← hdiag]
    exact integrable_boxSum_diag a weight Finset.univ
  have hcross : Integrable (fun u => (H u * conj m).re) locations := (hH.mul_const (conj m)).re
  have hcross_mean : (∫ u, (H u * conj m).re ∂locations) = Complex.normSq m := by
    rw [show (∫ u, (H u * conj m).re ∂locations) = (∫ u, H u * conj m ∂locations).re from
      integral_re (hH.mul_const (conj m)), integral_mul_const]
    change (m * conj m).re = _
    simp [Complex.mul_conj]
  rw [hind]
  unfold commonAverage
  change _ = ∫ u, ‖H u - m‖ ^ 2 ∂locations
  simp_rw [hdiag, Complex.sq_norm, Complex.normSq_sub]
  have hplus : Integrable (fun u => Complex.normSq (H u) + Complex.normSq m) locations :=
    hE.add (integrable_const _)
  rw [integral_sub hplus (hcross.const_mul 2),
    integral_add hE (integrable_const (Complex.normSq m)), integral_const_mul, hcross_mean,
    integral_const]
  simp only [probReal_univ, one_smul]
  ring

open Classical in
/-- Absolute mass of deleted ordered pairs in the single product enclosure
`[-period, period] × [-period, period]`. No location is charged separately. -/
@[expose] public def deletedMass (a weight : ι → ℝ) (retained : Finset (ι × ι)) : ℝ :=
  ∑ p ∈ Finset.univ \ retained,
    if |a p.1| ≤ period ∧ |a p.2| ≤ period then weight p.1 * weight p.2 else 0

private theorem abs_le_period_of_mem_window {a u : ℝ}
    (hu : u ∈ Icc 0 period) (ha : a ∈ window u) : |a| ≤ period := by
  refine abs_le.mpr ⟨?_, ha.2.le.trans hu.2⟩
  linarith only [hu.1, ha.1]

open Classical in
private theorem abs_deleted_boxSum_le (a weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (retained : Finset (ι × ι)) {u w : ℝ} (hu : u ∈ Icc 0 period) (hw' : w ∈ Icc 0 period) :
    |boxSum a weight (Finset.univ \ retained) u w| ≤ deletedMass a weight retained := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [windowIndicator_apply, windowIndicator_apply]
  by_cases h₁ : a p.1 ∈ window u <;> by_cases h₂ : a p.2 ∈ window w
  · have h := And.intro (abs_le_period_of_mem_window hu h₁) (abs_le_period_of_mem_window hw' h₂)
    simp only [h₁, h₂, h, ite_true, mul_one, abs_mul, abs_of_nonneg (hw p.1), abs_of_nonneg (hw p.2)]
    exact mul_le_of_le_one_right (mul_nonneg (hw _) (hw _))
      (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  all_goals
    simp only [h₁, h₂, ite_true, ite_false, mul_zero, zero_mul, abs_zero]
    split_ifs
    · exact mul_nonneg (hw _) (hw _)
    · exact le_rfl

private theorem ae_location : ∀ᵐ u ∂locations, u ∈ Icc 0 period :=
  Measure.ae_smul_measure_le _ (ae_restrict_mem measurableSet_Icc)

private theorem ae_locations_prod : ∀ᵐ z ∂(locations.prod locations), z ∈ Icc 0 period ×ˢ Icc 0 period := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)).2
  filter_upwards [ae_location] with u hu
  filter_upwards [ae_location] with w hw
  exact ⟨hu, hw⟩

private theorem abs_average_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {M : ℝ} (hf : Integrable f μ)
    (hM : ∀ᵐ z ∂μ, |f z| ≤ M) : |∫ z, f z ∂μ| ≤ M := by
  calc
    |∫ z, f z ∂μ| ≤ ∫ z, |f z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _z, M ∂μ := integral_mono_ae hf.abs (integrable_const M) hM
    _ = M := by simp

/-- Removing pairs changes the common-minus-independent comparison by at most
twice the enclosing deleted mass. This does not estimate that mass arithmetically. -/
public theorem abs_retained_comparison_error_le (a weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (retained : Finset (ι × ι)) :
    |(commonAverage a weight retained - independentAverage a weight retained) -
      (∫ u, ‖harmonic a weight u - ∫ w, harmonic a weight w ∂locations‖ ^ 2 ∂locations)| ≤
      2 * deletedMass a weight retained := by
  classical
  let deleted : Finset (ι × ι) := Finset.univ \ retained
  have hsplit (u w : ℝ) : boxSum a weight deleted u w + boxSum a weight retained u w =
      boxSum a weight Finset.univ u w := by
    unfold boxSum
    exact Finset.sum_sdiff (Finset.subset_univ retained)
  have hc : commonAverage a weight Finset.univ =
      commonAverage a weight deleted + commonAverage a weight retained := by
    unfold commonAverage
    simp_rw [← hsplit]
    exact integral_add (integrable_boxSum_diag a weight deleted)
      (integrable_boxSum_diag a weight retained)
  have hi : independentAverage a weight Finset.univ =
      independentAverage a weight deleted + independentAverage a weight retained := by
    unfold independentAverage
    simp_rw [← hsplit]
    exact integral_add (integrable_boxSum_prod a weight deleted)
      (integrable_boxSum_prod a weight retained)
  have hcb : |commonAverage a weight deleted| ≤ deletedMass a weight retained := by
    apply abs_average_le (integrable_boxSum_diag a weight deleted)
    filter_upwards [ae_location] with u hu
    exact abs_deleted_boxSum_le a weight hw retained hu hu
  have hib : |independentAverage a weight deleted| ≤ deletedMass a weight retained := by
    apply abs_average_le (integrable_boxSum_prod a weight deleted)
    filter_upwards [ae_locations_prod] with z hz
    exact abs_deleted_boxSum_le a weight hw retained hz.1 hz.2
  rw [← common_sub_independent_univ_eq_variance, hc, hi,
    show (commonAverage a weight retained - independentAverage a weight retained) -
      (commonAverage a weight deleted + commonAverage a weight retained -
        (independentAverage a weight deleted + independentAverage a weight retained)) =
      independentAverage a weight deleted - commonAverage a weight deleted by ring]
  have hab := abs_sub_le (independentAverage a weight deleted) 0 (commonAverage a weight deleted)
  rw [sub_zero, zero_sub, abs_neg] at hab
  exact hab.trans (by linarith only [hcb, hib])

end

end SharpPeriodWindowPair
