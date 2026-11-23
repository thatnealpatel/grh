module

public import Lemmas.WeightedHalfMomentTranslate
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Moment-zero compact approximants for the rational theta density repair

In the rational log chart at twist `1/2`, (9.2.2.34), p. 417, gives the
symmetric strip weight. The theta inputs in (10.1.1.3), p. 434, have both
zero modes removed. The proposed replacement for totality in (10.2.2.4–6),
p. 446, uses compact log approximants to a Gaussian-damped zeta quotient.
This new approximation step makes their half-Mellin moment exactly zero.
It neither assumes continuity of this moment in the strip norm nor proves
that the Gaussian quotient has the required weighted derivatives.
-/

open Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace Masullo

private theorem exists_compactLog_halfMoment_eq_one :
    ∃ β : ℝ → ℂ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      (∫ x : ℝ, (Real.exp (x / 2) : ℂ) * β x) = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let β (x : ℝ) : ℂ := (Real.exp (-x / 2) : ℂ) * (b.normed volume x : ℂ)
  have hb : ContDiff ℝ ∞ (fun x : ℝ ↦ (b.normed volume x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have he : ContDiff ℝ ∞ (fun x : ℝ ↦ (Real.exp (-x / 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))
  refine ⟨β, he.mul hb, (b.hasCompactSupport_normed.comp_left Complex.ofReal_zero).mul_left, ?_⟩
  calc
    _ = ∫ x : ℝ, (b.normed volume x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      have hx : (Real.exp (x / 2) : ℂ) * (Real.exp (-x / 2) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add, show x / 2 + -x / 2 = 0 by ring,
          Real.exp_zero, Complex.ofReal_one]
      change (Real.exp (x / 2) : ℂ) *
        ((Real.exp (-x / 2) : ℂ) * (b.normed volume x : ℂ)) = _
      rw [← mul_assoc, hx, one_mul]
    _ = 1 := (integral_ofReal (f := b.normed volume)).trans
      ((congrArg Complex.ofReal b.integral_normed).trans Complex.ofReal_one)

/-- A smooth compact log profile can be approximated simultaneously through any
fixed derivative order by another smooth compact profile with zero half-Mellin
moment. The weighted derivative norms use the same root as the rational theta
closure, with the half moment strictly outside the strip. -/
public theorem exists_compactLog_halfMoment_eq_zero {α s : ℝ} (hα : 0 ≤ α)
    (hα' : α < 1 / 2) (hs : 0 ≤ s) {q : ℝ → ℂ} (hq : ContDiff ℝ ∞ q)
    (hcq : HasCompactSupport q) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ → ℂ, ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧
      (∫ x : ℝ, (Real.exp (x / 2) : ℂ) * p x) = 0 ∧
      ∀ j ≤ N, eLpNorm (fun x : ℝ ↦ (symmetricStripWeightRoot α s x : ℂ) *
        (iteratedDeriv j p x - iteratedDeriv j q x)) 2 volume < ENNReal.ofReal ε := by
  let m := ∫ x : ℝ, (Real.exp (x / 2) : ℂ) * q x
  obtain ⟨β, hβ, hcβ, hβm⟩ := exists_compactLog_halfMoment_eq_one
  let c (L x : ℝ) := m * (Real.exp (-L / 2) : ℂ) * β (x - L)
  obtain ⟨hm, hlim⟩ := compactLog_halfMoment_translate hα hα' hs hβ hcβ hβm m
  -- Pick one translation for the whole derivative norm, after fixing `q`.
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hev : ∀ᶠ L : ℝ in atTop, ∀ j ∈ Finset.range (N + 1),
      eLpNorm (fun x : ℝ ↦ (symmetricStripWeightRoot α s x : ℂ) *
        iteratedDeriv j (c L) x) 2 volume < ENNReal.ofReal ε :=
    (eventually_all_finset _).mpr fun j _ ↦ (hlim j).eventually_lt_const hε'
  obtain ⟨L, hL⟩ := hev.exists
  have hc : ContDiff ℝ ∞ (c L) := contDiff_const.mul (hβ.comp (by fun_prop))
  have hcc : HasCompactSupport (c L) := (hcβ.comp_homeomorph (Homeomorph.subRight L)).mul_left
  let p (x : ℝ) := q x - c L x
  refine ⟨p, hq.sub hc, hcq.sub hcc, ?_, fun j hj ↦ ?_⟩
  · -- The correction has exactly the moment removed from the compact candidate.
    let e (x : ℝ) : ℂ := Real.exp (x / 2)
    have he : Continuous e := Complex.continuous_ofReal.comp (by fun_prop)
    have hi {f : ℝ → ℂ} (hf : Continuous f) (hcf : HasCompactSupport f) :
        Integrable (fun x ↦ e x * f x) :=
      (he.mul hf).integrable_of_hasCompactSupport hcf.mul_left
    change (∫ x : ℝ, e x * (q x - c L x)) = 0
    simp_rw [mul_sub]
    rw [integral_sub (hi hq.continuous hcq) (hi hc.continuous hcc)]
    exact sub_eq_zero.mpr (hm L).symm
  · have hd (x : ℝ) : iteratedDeriv j p x - iteratedDeriv j q x = -iteratedDeriv j (c L) x := by
      rw [show iteratedDeriv j p x = iteratedDeriv j q x - iteratedDeriv j (c L) x from
        iteratedDeriv_sub (hq.of_le (by simp)).contDiffAt (hc.of_le (by simp)).contDiffAt]
      abel
    simp_rw [hd, mul_neg]
    rw [show (fun x : ℝ ↦ -((symmetricStripWeightRoot α s x : ℂ) *
      iteratedDeriv j (c L) x)) = -(fun x : ℝ ↦ (symmetricStripWeightRoot α s x : ℂ) *
        iteratedDeriv j (c L) x) from rfl, eLpNorm_neg]
    exact hL j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

end Masullo
