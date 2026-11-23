module

public import Lemmas.InteriorLogJet
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral

/-! # Moving a half-Mellin moment to the right in the symmetric strip norm -/

open Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace Masullo

private theorem halfMoment_translate (β : ℝ → ℂ) (m : ℂ) (L : ℝ) :
    (∫ x : ℝ, (Real.exp (x / 2) : ℂ) *
      (m * (Real.exp (-L / 2) : ℂ) * β (x - L))) =
    m * ∫ x : ℝ, (Real.exp (x / 2) : ℂ) * β x := by
  let f (x : ℝ) := (Real.exp (x / 2) : ℂ) *
    (m * (Real.exp (-L / 2) : ℂ) * β (x - L))
  calc
    ∫ x : ℝ, f x = ∫ x : ℝ, f (x + L) := (integral_add_right_eq_self f L).symm
    _ = m * ∫ x : ℝ, (Real.exp (x / 2) : ℂ) * β x := by
      rw [← integral_const_mul]
      congr 1
      funext x
      have he : (Real.exp ((x + L) / 2) : ℂ) * (Real.exp (-L / 2) : ℂ) =
          (Real.exp (x / 2) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        congr 2
        ring
      simp only [f, add_sub_cancel_right]
      calc
        _ = m * ((Real.exp ((x + L) / 2) : ℂ) * (Real.exp (-L / 2) : ℂ)) * β x := by ring
        _ = _ := by rw [he, mul_assoc]

private theorem halfMoment_weight_bound {α s L : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hL : 1 ≤ L) (x : ℝ) :
    Real.exp (-L / 2) * symmetricStripWeightRoot α s (x + L) ≤
      (4 : ℝ) ^ (s / 4) * (L ^ (s / 2) * Real.exp (-(1 / 2 - α) * L)) *
        symmetricStripWeightRoot α s x := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hpoly : 1 + (x + L) ^ 2 ≤ 4 * L ^ 2 * (1 + x ^ 2) := by
    calc
      _ ≤ 2 * (1 + L ^ 2) * (1 + x ^ 2) := by
        nlinarith [sq_nonneg (x - L), sq_nonneg (L * x)]
      _ ≤ _ := by
        gcongr (?_ * (1 + x ^ 2))
        nlinarith [mul_nonneg (sub_nonneg.mpr hL) (by positivity : 0 ≤ L + 1)]
  have hp : (1 + (x + L) ^ 2) ^ (s / 4) ≤
      (4 : ℝ) ^ (s / 4) * L ^ (s / 2) * (1 + x ^ 2) ^ (s / 4) := by
    refine (Real.rpow_le_rpow (by positivity) hpoly (by positivity : 0 ≤ s / 4)).trans_eq ?_
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul hL0]
    rw [show ((2 : ℕ) : ℝ) * (s / 4) = s / 2 by push_cast; ring]
  have he : Real.exp (α * |x + L|) ≤ Real.exp (α * (|x| + L)) := by
    rw [Real.exp_le_exp]
    gcongr
    simpa [abs_of_nonneg hL0] using abs_add_le x L
  simp only [symmetricStripWeightRoot_apply]
  calc
    _ ≤ Real.exp (-L / 2) * (Real.exp (α * (|x| + L)) *
        ((4 : ℝ) ^ (s / 4) * L ^ (s / 2) * (1 + x ^ 2) ^ (s / 4))) := by gcongr
    _ = _ := by
      rw [show α * (|x| + L) = α * |x| + α * L by ring, Real.exp_add,
        show -(1 / 2 - α) * L = -L / 2 + α * L by ring, Real.exp_add]
      ring

private theorem tendsto_weighted_halfMoment_translate {α s : ℝ} (hα : 0 ≤ α)
    (hα' : α < 1 / 2) (hs : 0 ≤ s) {f : ℝ → ℂ} (hf : Continuous f)
    (hcf : HasCompactSupport f) (m : ℂ) :
    Tendsto (fun L : ℝ ↦ eLpNorm (fun x : ℝ ↦ (symmetricStripWeightRoot α s x : ℂ) *
      (m * (Real.exp (-L / 2) : ℂ) * f (x - L))) 2 volume) atTop (𝓝 0) := by
  let g (x : ℝ) := (symmetricStripWeightRoot α s x : ℂ) * f x
  let u (L x : ℝ) := (symmetricStripWeightRoot α s x : ℂ) *
    (m * (Real.exp (-L / 2) : ℂ) * f (x - L))
  let C (L : ℝ) := ‖m‖ * (4 : ℝ) ^ (s / 4) *
    (L ^ (s / 2) * Real.exp (-(1 / 2 - α) * L))
  have hC (L : ℝ) (hL : 0 ≤ L) : 0 ≤ C L := by dsimp [C]; positivity
  have hg : Continuous g :=
    (Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot α s)).mul hf
  have hcg : HasCompactSupport g := hcf.mul_left
  have hu (L : ℝ) : Continuous (u L) :=
    (Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot α s)).mul
      (continuous_const.mul (hf.comp (continuous_id.sub continuous_const)))
  have hlimC : Tendsto C atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / 2) (1 / 2 - α)
        (sub_pos.mpr hα')).const_mul (‖m‖ * (4 : ℝ) ^ (s / 4))
  have hlim : Tendsto (fun L ↦ ENNReal.ofReal (C L) * eLpNorm g 2 volume) atTop (𝓝 0) := by
    have hfin : eLpNorm g 2 volume ≠ (∞ : ℝ≥0∞) :=
      (hg.memLp_of_hasCompactSupport hcg).eLpNorm_ne_top
    have hcast : Tendsto (fun L ↦ ENNReal.ofReal (C L)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlimC
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hcast (Or.inr hfin)
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), ENNReal.tendsto_nhds_zero.mp hlim ε hε] with L hL hεL
  have hCL := hC L (zero_le_one.trans hL)
  change eLpNorm (u L) 2 volume ≤ ε
  rw [← eLpNorm_comp_measurePreserving (hu L).aestronglyMeasurable
    (measurePreserving_add_right volume L)]
  refine le_trans ?_ hεL
  calc
    _ ≤ eLpNorm (fun x ↦ (C L : ℂ) • g x) 2 volume := by
      apply eLpNorm_mono_ae ((hu L).comp (continuous_id.add continuous_const)).aestronglyMeasurable
      filter_upwards with x
      simp only [Function.comp_apply, Pi.add_apply, id_eq, u, g, smul_eq_mul, add_sub_cancel_right,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (symmetricStripWeightRoot_pos ..).le,
        Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hCL]
      calc
        _ = ‖m‖ * (Real.exp (-L / 2) * symmetricStripWeightRoot α s (x + L)) * ‖f x‖ := by ring
        _ ≤ ‖m‖ * ((4 : ℝ) ^ (s / 4) * (L ^ (s / 2) * Real.exp (-(1 / 2 - α) * L)) *
            symmetricStripWeightRoot α s x) * ‖f x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (halfMoment_weight_bound hα hs hL x) (norm_nonneg _))
            (norm_nonneg _)
        _ = _ := by dsimp [C]; ring
    _ = _ := by
      rw [show (fun x ↦ (C L : ℂ) • g x) = (C L : ℂ) • g from rfl, eLpNorm_const_smul,
        ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hCL]

private theorem compactSupport_iteratedDeriv {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (j : ℕ) : HasCompactSupport (iteratedDeriv j f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- A normalized compact bump, translated by `L` and scaled by `m * exp(-L/2)`,
keeps half-Mellin moment `m` for every `L` and tends to zero in each weighted
log derivative norm as `L → +∞`, provided the strip has width `α < 1/2`. -/
public theorem compactLog_halfMoment_translate {α s : ℝ} (hα : 0 ≤ α) (hα' : α < 1 / 2)
    (hs : 0 ≤ s) {β : ℝ → ℂ} (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβm : (∫ x : ℝ, (Real.exp (x / 2) : ℂ) * β x) = 1) (m : ℂ) :
    (∀ L : ℝ, (∫ x : ℝ, (Real.exp (x / 2) : ℂ) *
      (m * (Real.exp (-L / 2) : ℂ) * β (x - L))) = m) ∧
    ∀ j : ℕ, Tendsto (fun L : ℝ ↦ eLpNorm (fun x : ℝ ↦
      (symmetricStripWeightRoot α s x : ℂ) *
        iteratedDeriv j (fun y : ℝ ↦ m * (Real.exp (-L / 2) : ℂ) * β (y - L)) x)
        2 volume) atTop (𝓝 0) := by
  refine ⟨fun L ↦ by rw [halfMoment_translate, hβm, mul_one], fun j ↦ ?_⟩
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const]
  exact tendsto_weighted_halfMoment_translate hα hα' hs
    (hβ.continuous_iteratedDeriv j (by simp)) (compactSupport_iteratedDeriv hcβ j) m

end Masullo
