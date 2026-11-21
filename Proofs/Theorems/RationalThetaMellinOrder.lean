module

public import Theorems.RationalThetaMellinContinuation
public import Mathlib.Analysis.Analytic.Order

/-!
# Vanishing orders of rational theta Mellin transforms

In the rational unramified model, the continued Mellin factorization gives
vanishing through the zeta order. This is the unshifted analytic input for
the interior jets in (10.2.2.4) and (10.2.2.6), p. 446. It does not identify
these derivatives with the weighted pairings or prove totality on a quotient.
-/

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology

namespace Masullo

/-- The two-moment rational theta transform vanishes to at least the zeta
order in the open critical strip. The local factor may contribute extra
vanishing, including infinite order. -/
public theorem analyticOrderAt_rationalTheta_mellin_ge_zeta (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) {ρ : ℂ} (hpos : 0 < ρ.re) (hlt : ρ.re < 1) :
    analyticOrderAt riemannZeta ρ ≤ analyticOrderAt
      (fun z : ℂ ↦ ∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)) ρ := by
  let T (z : ℂ) := ∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)
  let M (z : ℂ) := ∫ x : ℝ, rationalMellinIntegrand b z x
  have hposNear : ∀ᶠ z : ℂ in 𝓝 ρ, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos
  have hltNear : ∀ᶠ z : ℂ in 𝓝 ρ, z.re < 1 :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hlt
  have hpole {z : ℂ} (hz : z.re < 1) : z ≠ 1 := fun h ↦ by simp [h] at hz
  have hfactor : T =ᶠ[𝓝 ρ] riemannZeta * M := by
    filter_upwards [hposNear, hltNear] with z hzpos hzlt
    exact rationalTheta_mellin_eq_zeta_mul_of_pos b hb hFourier hzpos (hpole hzlt)
  have hM : AnalyticAt ℂ M ρ :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr <| by
      filter_upwards [hposNear] with z hz
      exact (hasDerivAt_rationalMellin b hz).2.differentiableAt
  change analyticOrderAt riemannZeta ρ ≤ analyticOrderAt T ρ
  rw [analyticOrderAt_congr hfactor, analyticOrderAt_mul (analyticOn_riemannZeta ρ (hpole hlt)) hM]
  exact le_self_add

/-- Every derivative of the theta Mellin transform strictly below the zeta
order vanishes. At a nonzero value of zeta the order condition is vacuous. -/
public theorem iteratedDeriv_rationalTheta_mellin_eq_zero (b : 𝓢(ℝ, ℂ))
    (hb : b 0 = 0) (hFourier : (𝓕 b) 0 = 0) {ρ : ℂ} (hpos : 0 < ρ.re) (hlt : ρ.re < 1)
    {m : ℕ} (hm : (m : ℕ∞) < analyticOrderAt riemannZeta ρ) :
    iteratedDeriv m
      (fun z : ℂ ↦ ∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * x)) ρ = 0 := by
  have hT := (differentiable_rationalTheta_mellin b hb hFourier).analyticAt ρ
  have hbound := hm.trans_le (analyticOrderAt_rationalTheta_mellin_ge_zeta b hb hFourier hpos hlt)
  have hsucc := (ENat.add_one_le_iff (ENat.natCast_ne_top m)).mpr hbound
  rw [← Nat.cast_succ] at hsucc
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hT).mp hsucc m (Nat.lt_succ_self m)

end Masullo
