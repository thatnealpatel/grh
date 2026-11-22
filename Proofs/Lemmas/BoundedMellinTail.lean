module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform

/-! # Mellin tails of bounded measurable functions -/

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace Masullo

/-- The Mellin tail above `1`, with parameter chosen so it converges for `0 < w.re`
when the coefficient function is bounded there. -/
@[expose] public noncomputable def boundedMellinTail (A : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), A x * (x : ℂ) ^ (-(w + 1))

private theorem boundedMellinTail_eq_mellin (A : ℝ → ℂ) (w : ℂ) :
    boundedMellinTail A w = mellin ((Ioi (1 : ℝ)).indicator A) (-w) := by
  have hexp : -w - 1 = -(w + 1) := by ring
  simp only [mellin, boundedMellinTail, smul_eq_mul, hexp]
  have hcut (x : ℝ) : (x : ℂ) ^ (-(w + 1)) * (Ioi (1 : ℝ)).indicator A x =
      (Ioi (1 : ℝ)).indicator (fun t ↦ (t : ℂ) ^ (-(w + 1)) * A t) x :=
    (indicator_mul_right (i := x) (Ioi (1 : ℝ)) (fun t ↦ (t : ℂ) ^ (-(w + 1))) A).symm
  simp_rw [hcut]
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  simp only [mul_comm]

/-- A bounded measurable coefficient gives a holomorphic Mellin tail on `0 < w.re`. -/
public theorem boundedMellinTail_differentiableOn {A : ℝ → ℂ} {M : ℝ}
    (hA : Measurable A) (hM : 0 ≤ M) (hAb : ∀ x ≥ 1, ‖A x‖ ≤ M) :
    DifferentiableOn ℂ (boundedMellinTail A) {w | 0 < w.re} := by
  let f := (Ioi (1 : ℝ)).indicator A
  have hf : Measurable f := hA.indicator measurableSet_Ioi
  have hfb (x : ℝ) : ‖f x‖ ≤ M := by
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [show f x = A x from indicator_of_mem hx A]
      exact hAb x (le_of_lt hx)
    · simpa only [f, indicator_of_notMem hx, norm_zero] using hM
  have hloc : LocallyIntegrableOn f (Ioi 0) := by
    apply LocallyIntegrable.locallyIntegrableOn
    exact (locallyIntegrable_const M).mono hf.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_of_nonneg hM] using hfb x)
  have htop : f =O[atTop] (fun x : ℝ ↦ x ^ (-(0 : ℝ))) :=
    IsBigO.of_bound M (Eventually.of_forall fun x ↦ by
      simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using hfb x)
  intro w hw
  change 0 < w.re at hw
  have hbot : f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ ↦ x ^ (-(-w.re - 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with x hx
    have hx' : x ∉ Ioi (1 : ℝ) := not_lt_of_ge hx.le
    simp only [f, indicator_of_notMem hx', norm_zero, zero_mul, le_refl]
  have hd : DifferentiableAt ℂ (mellin f) (-w) :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop
      (by simpa only [Complex.neg_re, neg_lt_zero] using hw) hbot
      (by rw [Complex.neg_re]; exact sub_lt_self _ zero_lt_one)
  have hn : DifferentiableAt ℂ (fun z : ℂ ↦ -z) w := differentiableAt_id.neg
  have hm : boundedMellinTail A = mellin f ∘ fun z : ℂ ↦ -z :=
    funext (boundedMellinTail_eq_mellin A)
  rw [hm]
  exact (hd.comp w hn).differentiableWithinAt

/-- The tail is uniformly bounded by the coefficient bound on the closed half-plane
`1 ≤ w.re`, since `x⁻²` is an integrable majorant with integral `1`. -/
public theorem norm_boundedMellinTail_le {A : ℝ → ℂ} {M : ℝ} {w : ℂ}
    (hA : Measurable A) (hM : 0 ≤ M) (hAb : ∀ x ≥ 1, ‖A x‖ ≤ M) (hw : 1 ≤ w.re) :
    ‖boundedMellinTail A w‖ ≤ M := by
  have hm : IntegrableOn (fun x : ℝ ↦ M * x ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul M
  have hbound : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1),
      ‖A x * (x : ℂ) ^ (-(w + 1))‖ ≤ M * x ^ (-2 : ℝ) := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_
    have hx' : 1 < x := hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx'),
      Complex.neg_re, Complex.add_re, Complex.one_re]
    calc
      _ ≤ M * x ^ (-(w.re + 1)) :=
        mul_le_mul_of_nonneg_right (hAb x hx'.le) (Real.rpow_nonneg (zero_lt_one.trans hx').le _)
      _ ≤ M * x ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx'.le (by linarith)) hM
  have hkernel : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (-(w + 1))) (Ioi 1) :=
    continuousOn_of_forall_continuousAt fun x hx ↦
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans (show 1 < x from hx)).ne')
  have hint : IntegrableOn (fun x : ℝ ↦ A x * (x : ℂ) ^ (-(w + 1))) (Ioi 1) :=
    hm.mono' (hA.aestronglyMeasurable.mul (hkernel.aestronglyMeasurable measurableSet_Ioi)) hbound
  calc
    ‖boundedMellinTail A w‖ ≤ ∫ x : ℝ in Ioi 1, ‖A x * (x : ℂ) ^ (-(w + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi 1, M * x ^ (-2 : ℝ) := integral_mono_ae hint.norm hm hbound
    _ = M := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
      norm_num [Real.one_rpow]

end Masullo
