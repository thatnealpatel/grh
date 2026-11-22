module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Ring

/-! # Change of variables for the complex Gaussian zeta integral -/

open Complex MeasureTheory Set
open scoped ENNReal

namespace Masullo

/-- A nonnegative real base raised to a fixed complex power is Borel. -/
public theorem measurable_cpow_ofReal_nonneg {α : Type*} [MeasurableSpace α]
    {r : α → ℝ} (hr : Measurable r) (hr₀ : ∀ x, 0 ≤ r x) (s : ℂ) :
    Measurable fun x ↦ (r x : ℂ) ^ s := by
  classical
  have hlog : Measurable fun x ↦ exp ((Real.log (r x) : ℂ) * s) :=
    continuous_exp.measurable.comp ((Complex.measurable_ofReal.comp
      (Real.measurable_log.comp hr)).mul_const s)
  have hpiece : Measurable ((r ⁻¹' {0}).piecewise (fun _ ↦ (0 : ℂ) ^ s)
      (fun x ↦ exp ((Real.log (r x) : ℂ) * s))) :=
    Measurable.piecewise (hr (measurableSet_singleton 0)) measurable_const hlog
  convert hpiece using 1
  ext x
  by_cases hx : r x = 0
  · simp [hx]
  · simp only [piecewise, mem_preimage, mem_singleton_iff, ite_eq_right hx]
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ← ofReal_log (hr₀ x)]

/-- For a polar pullback independent of the angle, integrate out the angle
and transfer absolute integrability from the radial integral. -/
public theorem complex_polar_radial {f : ℂ → ℂ} {g : ℝ → ℂ} (hf : Measurable f)
    (hg : IntegrableOn g (Ioi 0))
    (h : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 • f (Complex.polarCoord.symm p) = g p.1) :
    Integrable f ∧ (∫ z, f z) = (2 * Real.pi : ℝ) • ∫ r in Ioi 0, g r := by
  have hang : IntegrableOn (fun _ : ℝ ↦ (1 : ℂ)) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hprod : IntegrableOn (fun p : ℝ × ℝ ↦ g p.1)
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
    change Integrable _ ((volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi))
    rw [← Measure.prod_restrict]
    simpa only [mul_one] using hg.mul_prod hang
  refine ⟨⟨hf.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_norm, ← Complex.lintegral_comp_polarCoord_symm]
    calc
      _ = ∫⁻ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, ENNReal.ofReal ‖g p.1‖ := by
        change (∫⁻ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, _) = _
        refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
        rw [← h p hp.1, norm_smul, Real.norm_of_nonneg hp.1.le, ENNReal.ofReal_mul hp.1.le]
        rfl
      _ < ∞ := (hasFiniteIntegral_iff_norm _).mp hprod.hasFiniteIntegral
  · calc
      _ = ∫ p in Complex.polarCoord.target, p.1 • f (Complex.polarCoord.symm p) :=
        (Complex.integral_comp_polarCoord_symm _).symm
      _ = ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, g p.1 * (1 : ℂ) := by
        rw [Complex.polarCoord_target]
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
        rw [h p hp.1, mul_one]
      _ = _ := by
        change (∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, g p.1 * (1 : ℂ)
          ∂ (volume.prod volume)) = _
        rw [setIntegral_prod_mul g (fun _ : ℝ ↦ (1 : ℂ)), setIntegral_const, Real.volume_real_Ioo,
          max_eq_left (by linarith [Real.pi_pos]), sub_neg_eq_add, ← two_mul]
        simp [Complex.real_smul, mul_comm]

/-- The absolutely integrable Gamma density at scale `B`. -/
public theorem integrableOn_scaledGammaDensity {B : ℝ} (hB : 0 < B) {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (a - 1) * exp (-(B * t : ℝ))) (Ioi 0) := by
  have hmeas := (measurable_cpow_ofReal_nonneg
    (r := fun t : ℝ ↦ max t 0) (by fun_prop) (fun _ ↦ le_max_right _ _) (a - 1)).mul
    (show Measurable fun t : ℝ ↦ exp (-(B * t : ℝ)) from by fun_prop)
  have hnorm : IntegrableOn (fun t : ℝ ↦ t ^ (a.re - 1) * Real.exp (-B * t ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hB
  rw [← integrableOn_congr_fun (g := fun t : ℝ ↦ (t : ℂ) ^ (a - 1) * exp (-(B * t : ℝ)))
    (f := fun t : ℝ ↦ ((max t 0 : ℝ) : ℂ) ^ (a - 1) * exp (-(B * t : ℝ)))
    (fun t ht ↦ by dsimp only; rw [max_eq_left (show 0 ≤ t from ht.le)]) measurableSet_Ioi]
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_eq_of_lt (setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_)
    ((hasFiniteIntegral_iff_norm _).mp hnorm.hasFiniteIntegral)
  have ht' : 0 < t := ht
  rw [max_eq_left ht'.le, norm_mul, norm_cpow_eq_rpow_re_of_pos ht', norm_exp,
    neg_re, ofReal_re, sub_re, one_re, Real.rpow_one, neg_mul,
    Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht'.le _) (Real.exp_pos _).le)]

/-- Substitute `t = r²` on the positive half-line, including the Jacobian. -/
public theorem square_radial_substitution {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun r : ℝ ↦ (2 * r) • g (r ^ 2)) (Ioi 0) ∧
      (∫ r in Ioi (0 : ℝ), (2 * r) • g (r ^ 2)) = ∫ t in Ioi (0 : ℝ), g t := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have h := And.intro ((integrableOn_Ioi_comp_rpow_iff g htwo).mpr hg)
    (integral_comp_rpow_Ioi g htwo)
  simpa only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, Real.rpow_two] using h

end Masullo
