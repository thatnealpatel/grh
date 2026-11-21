module

public import Theorems.RationalThetaMellinEntire
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Zeta factorization in the rational unramified model

Masullo invokes the identity theorem after (3.2.2.11), p. 127. Here the
absolutely unfolded product continues into `0 < z.re`, with its value at
one computed from the residue of zeta and the derivative of the real factor.
This continues the identity, not the absolutely integrated Dirichlet series.
-/

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

namespace Masullo

private theorem rationalMellin_one_eq_fourier_zero (b : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, rationalMellinIntegrand b 1 x) = (𝓕 b) 0 := by
  have hneg : Integrable (fun x : ℝ ↦ b (-x)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable b.integrable
  calc
    _ = ∫ x : ℝ, Real.exp x • (b (Real.exp x) + b (-Real.exp x)) := by
      congr 1
      funext x
      rw [rationalMellinIntegrand, one_mul, ← Complex.ofReal_exp, Complex.real_smul, mul_comm]
    _ = ∫ y in Ioi (0 : ℝ), b y + b (-y) := integral_comp_exp (fun y ↦ b y + b (-y))
    _ = ∫ y : ℝ, b y := by
      rw [integral_add b.integrable.integrableOn hneg.integrableOn, integral_comp_neg_Ioi, neg_zero]
      simpa only [compl_Ioi] using integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi b.integrable
    _ = _ := by
      rw [congrFun (SchwartzMap.fourier_coe b) 0, Real.fourier_real_eq_integral_exp_smul]
      simp

private theorem rationalTheta_mellin_continuation (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) :
    (∀ z : ℂ, 0 < z.re → z ≠ 1 →
      (∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)) =
        riemannZeta z * (∫ x : ℝ, rationalMellinIntegrand b z x)) ∧
    (∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp x) =
      ∫ x : ℝ, (x : ℂ) * rationalMellinIntegrand b 1 x := by
  classical
  let U := {z : ℂ | 0 < z.re}
  let T (z : ℂ) := ∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)
  let M (z : ℂ) := ∫ x : ℝ, rationalMellinIntegrand b z x
  let d := ∫ x : ℝ, (x : ℂ) * rationalMellinIntegrand b 1 x
  let G := Function.update (fun z ↦ riemannZeta z * M z) 1 d
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ U := convex_halfSpace_gt Complex.reLm.isLinear 0
  have hM1 : M 1 = 0 := (rationalMellin_one_eq_fourier_zero b).trans hFourier
  have hderiv : HasDerivAt M d 1 := (hasDerivAt_rationalMellin b (by simp : 0 < (1 : ℂ).re)).2
  have hM : AnalyticOnNhd ℂ M U := (Complex.analyticOnNhd_iff_differentiableOn hU).2
    (fun z hz ↦ (hasDerivAt_rationalMellin b hz).2.differentiableAt.differentiableWithinAt)
  have hproduct {z : ℂ} (hz : z ∈ U) (hne : z ≠ 1) :
      AnalyticAt ℂ (fun w ↦ riemannZeta w * M w) z :=
    (analyticOn_riemannZeta z hne).mul (hM z hz)
  have hupdate {z : ℂ} (hne : z ≠ 1) : G =ᶠ[𝓝 z] fun w ↦ riemannZeta w * M w := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show z ∈ ({1} : Set ℂ)ᶜ from hne)] with w hw
    exact Function.update_of_ne hw ..
  -- Cancel the pole by multiplying the zeta residue limit by the Mellin difference quotient.
  have hGone : AnalyticAt ℂ G 1 := by
    have hnear : U ∈ 𝓝 (1 : ℂ) := hU.mem_nhds (by simp [U])
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with z hz hne
      exact ((analyticAt_congr (hupdate hne)).2 (hproduct hz hne)).differentiableAt
    · apply continuousAt_update_same.mpr
      have hslope : Tendsto (fun z : ℂ ↦ M z / (z - 1)) (𝓝[≠] 1) (𝓝 d) := by
        have hs : slope M 1 = fun z ↦ M z / (z - 1) :=
          funext fun z ↦ by rw [slope_def_field, hM1, sub_zero]
        simpa only [hs] using hderiv.tendsto_slope
      have hlim := riemannZeta_residue_one.mul hslope
      rw [one_mul] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      field_simp
  have hG : AnalyticOnNhd ℂ G U := by
    intro z hz
    by_cases hne : z = 1
    · simpa only [hne] using hGone
    · exact (analyticAt_congr (hupdate hne)).2 (hproduct hz hne)
  -- The absolutely unfolded equality supplies agreement in a neighborhood of 2.
  have hagree : T =ᶠ[𝓝 (2 : ℂ)] G := by
    have hnear : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnear] with z hz
    have hne : z ≠ 1 := by
      intro h
      simp [h] at hz
    simpa only [G, Function.update_of_ne hne] using (rationalTheta_mellin_eq_zeta_mul b hz).2
  have hEq : EqOn T G U := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun z _ ↦ (differentiable_rationalTheta_mellin b hb hFourier).analyticAt z)
    hG hconv.isPreconnected (by norm_num [U]) hagree
  refine ⟨fun z hz hne ↦ ?_, ?_⟩
  · simpa only [G, Function.update_of_ne hne] using hEq hz
  · simpa only [T, G, Function.update_self, one_mul] using hEq (show (1 : ℂ) ∈ U by simp [U])

/-- Off the pole, the rational two-moment theta transform factors into zeta and
its real two-ray factor throughout the open right half-plane. -/
public theorem rationalTheta_mellin_eq_zeta_mul_of_pos (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) {z : ℂ} (hz : 0 < z.re) (hne : z ≠ 1) :
    (∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)) =
      riemannZeta z * (∫ x : ℝ, rationalMellinIntegrand b z x) :=
  (rationalTheta_mellin_continuation b hb hFourier).1 z hz hne

/-- At one, the continued product has value `M_b'(1)`, since `M_b(1) = 0`
and the zeta residue is one. This is not evaluation of the totalized product. -/
public theorem rationalTheta_mellin_one (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) :
    (∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp x) =
      ∫ x : ℝ, (x : ℂ) * rationalMellinIntegrand b 1 x :=
  (rationalTheta_mellin_continuation b hb hFourier).2

/-- The Mellin transform of two-moment rational theta input vanishes at each
zeta zero in the open critical strip. -/
public theorem rationalTheta_mellin_eq_zero_of_zeta_zero (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) {z : ℂ} (hpos : 0 < z.re) (hlt : z.re < 1)
    (hzero : riemannZeta z = 0) :
    (∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)) = 0 := by
  have hne : z ≠ 1 := fun h ↦ by simp [h] at hlt
  rw [rationalTheta_mellin_eq_zeta_mul_of_pos b hb hFourier hpos hne, hzero, zero_mul]

end Masullo
