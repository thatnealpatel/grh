module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # The origin of the log-ramp integrand at a simple trivial zero

Write `ℓ = log X`. Unlike the odd-character case, `-exp (ℓ*s) * L'/L / s²`
then has a triple pole. Its residue is quadratic, not linear, in `ℓ`.
-/

open Filter Complex
open scoped Topology

namespace RampOrigin

private theorem split_slope (f : ℂ → ℂ) (z : ℂ) :
    f z = f 0 + z * dslope f 0 z := by
  have h := sub_smul_dslope f 0 z
  simp only [sub_zero, smul_eq_mul] at h
  linear_combination -h

private theorem exp_split (ℓ : ℂ) : ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
    ∀ z, exp (ℓ*z) = 1 + ℓ*z + ℓ^2/2*z^2 + z^3*R z := by
  let f := fun z : ℂ => exp (ℓ*z)
  let g := dslope f 0
  let h := dslope g 0
  have df (z : ℂ) : HasDerivAt f (exp (ℓ*z)*ℓ) z := by
    simpa [f] using ((hasDerivAt_id z).const_mul ℓ).cexp
  have af (z : ℂ) : AnalyticAt ℂ f z := by unfold f; fun_prop
  have ag (z : ℂ) : AnalyticAt ℂ g z := (af z).dslope 0
  have ah (z : ℂ) : AnalyticAt ℂ h z := (ag z).dslope 0
  have g0 : g 0 = ℓ := by simpa [g, dslope_same] using (df 0).deriv
  have eqf : f = fun z => f 0 + z*g z := funext (split_slope f)
  have eqd (z : ℂ) : f z * ℓ = g z + z * deriv g z := by
    have e := (((hasDerivAt_id z).mul (ag z).differentiableAt.hasDerivAt).const_add (f 0)).deriv
    change deriv (fun x => f 0 + x*g x) z = _ at e
    rw [← eqf] at e
    simpa [one_mul, id_eq, (df z).deriv] using e
  have h0 : h 0 = ℓ^2/2 := by
    have e := congrArg (fun F : ℂ → ℂ => deriv F 0) (funext eqd)
    have e1 := ((df 0).mul_const ℓ).deriv
    have e2 := ((ag 0).differentiableAt.hasDerivAt.add ((hasDerivAt_id (0:ℂ)).mul
      (ag 0).deriv.differentiableAt.hasDerivAt)).deriv
    change deriv (fun x => g x + x * deriv g x) 0 = _ at e2
    simp only [e1, e2, mul_zero, exp_zero, one_mul, id_eq, zero_mul, add_zero] at e
    rw [show h 0 = deriv g 0 from dslope_same ..]
    linear_combination -e/2
  refine ⟨dslope h 0, (ah 0).dslope 0, fun z => ?_⟩
  have hf := split_slope f z
  have hg := split_slope g z
  have hh := split_slope h z
  change f z = f 0 + z*g z at hf
  change g z = g 0 + z*h z at hg
  rw [g0] at hg
  rw [h0] at hh
  change f z = _
  rw [hf, hg, hh, show f 0 = 1 by simp [f]]
  ring

/-- The full principal part, with constants `a` and `b` independent of the cutoff.
The analytic remainder certifies that there are no other negative powers. -/
public theorem simple_zero_principal_part {L : ℂ → ℂ} (hL : AnalyticAt ℂ L 0)
    (hz : L 0 = 0) (hd : deriv L 0 ≠ 0) :
    ∃ a b : ℂ, ∀ ℓ : ℂ, ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        -exp (ℓ*z) * (deriv L z / L z) / z^2 =
          -1/z^3 - (ℓ+a)/z^2 - (ℓ^2/2 + a*ℓ + b)/z + R z := by
  let g := dslope L 0
  have hg : AnalyticAt ℂ g 0 := hL.dslope 0
  have hg0 : g 0 ≠ 0 := by rwa [show g 0 = deriv L 0 from dslope_same ..]
  let A := fun z => deriv g z / g z
  have hA : AnalyticAt ℂ A 0 := hg.deriv.div hg hg0
  let B := dslope A 0
  let T := dslope B 0
  have hT : AnalyticAt ℂ T 0 := (hA.dslope 0).dslope 0
  refine ⟨A 0, B 0, fun ℓ => ?_⟩
  obtain ⟨U, hU, eU⟩ := exp_split ℓ
  let R := fun z => -(U z + T z + ℓ * B 0 + ℓ*z*T z + ℓ^2/2*A z + z*U z*A z)
  have hR : AnalyticAt ℂ R 0 := by dsimp [R]; fun_prop
  refine ⟨R, hR, ?_⟩
  have eL : L = fun z => z*g z := funext fun z => by simpa [hz] using split_slope L z
  filter_upwards [self_mem_nhdsWithin, (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z hz' hn ha
  have hne : z ≠ 0 := hz'
  have dL : deriv L z = g z + z*deriv g z := by
    rw [eL]
    change deriv (id * g) z = _
    simpa using ((hasDerivAt_id z).mul ha.differentiableAt.hasDerivAt).deriv
  have ld : deriv L z / L z = 1/z + A z := by
    rw [dL, eL]; dsimp only [A]; field_simp
  rw [ld, eU]
  dsimp only [R]
  have eA : A z = A 0 + z*(B 0 + z*T z) := by
    calc A z = A 0 + z * B z := split_slope A z
         _ = _ := by rw [split_slope B z]
  rw [eA]
  field_simp
  ring

/-- At a real cutoff, the extra quadratic logarithm is still negligible on the
square scale. The constants may be complex. -/
public theorem residue_div_sqrt (a b : ℂ) :
    Tendsto (fun X : ℝ => -((Real.log X : ℂ)^2/2 + a*Real.log X + b) / Real.sqrt X)
      atTop (𝓝 0) := by
  have h₂ : Tendsto (fun X : ℝ => Real.log X ^ 2 / Real.sqrt X) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : 0 < (1/2 : ℝ))).tendsto_div_nhds_zero
  have h₁ : Tendsto (fun X : ℝ => Real.log X / Real.sqrt X) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : 0 < (1/2 : ℝ))).tendsto_div_nhds_zero
  have h₀ : Tendsto (fun X : ℝ => 1 / Real.sqrt X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have lift {f : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
      Tendsto (fun X => (f X : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hf
  have h := ((((lift h₂).div_const 2).add ((lift h₁).const_mul a)).add ((lift h₀).const_mul b)).neg
  convert h using 1
  · ext X
    push_cast
    ring
  · simp

end RampOrigin
