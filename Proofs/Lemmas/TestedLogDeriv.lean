module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Tactic.Ring

/-!
# Principal part of a tested logarithmic derivative

The step from the residue of `Φ * f` to `Φ(z) * Res f` in Masullo,
(B.3.2.3), p. 606, needs at most simple poles. For the logarithmic derivative
in (B.4.2.2), p. 614, this follows from the local order factorization. We record
both the residue coefficient and the analytic remainder for contour subtraction.
-/

open Filter
open scoped Topology

namespace Masullo

/-- At a point of finite meromorphic order `n`, the logarithmic derivative
multiplied by an analytic test has at most a simple pole, with coefficient
`n * Φ z`. The statement is on the punctured germ, irrespective of how the
functions were totalized at the center. -/
public theorem logDeriv_weighted_principalPart {F Φ : ℂ → ℂ} {z : ℂ} {n : ℤ}
    (hF : MeromorphicAt F z) (hn : meromorphicOrderAt F z = n) (hΦ : AnalyticAt ℂ Φ z) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧
      (fun w ↦ Φ w * logDeriv F w) =ᶠ[𝓝[≠] z] fun w ↦ (n : ℂ) * Φ z / (w - z) + H w := by
  obtain ⟨g, hg, hgz, heq⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hn
  have heq' : F =ᶠ[𝓝[≠] z] fun w ↦ (w - z) ^ n * g w := by
    change ∀ᶠ w in 𝓝[≠] z, F w = (w - z) ^ n * g w
    simpa only [smul_eq_mul] using heq
  have hld := logDeriv_congr_nhdsNE heq'
  have hag : AnalyticAt ℂ (logDeriv g) z := hg.deriv.div hg hgz
  refine ⟨fun w ↦ (n : ℂ) * dslope Φ z w + Φ w * logDeriv g w,
    (analyticAt_const.mul (hΦ.dslope z)).add (hΦ.mul hag), ?_⟩
  filter_upwards [hld, (hg.eventually_analyticAt).filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hgz).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw hgw hgwn hwz
  have hsub : w - z ≠ 0 := sub_ne_zero.mpr hwz
  have hlin : DifferentiableAt ℂ (fun u : ℂ ↦ u - z) w := differentiableAt_id.sub_const z
  have hlin_deriv : deriv (fun u : ℂ ↦ u - z) w = 1 := (hasDerivAt_id w).sub_const z |>.deriv
  have hzpow : DifferentiableAt ℂ (fun u : ℂ ↦ (u - z) ^ n) w :=
    hlin.zpow (.inl hsub)
  have hslope : dslope Φ z w = (Φ w - Φ z) / (w - z) :=
    (eq_div_iff hsub).mpr (by simpa only [mul_comm, smul_eq_mul] using sub_smul_dslope Φ z w)
  change Φ w * logDeriv F w = (n : ℂ) * Φ z / (w - z) +
    ((n : ℂ) * dslope Φ z w + Φ w * logDeriv g w)
  rw [hw, logDeriv_fun_mul (f := fun u ↦ (u - z) ^ n) (g := g)
    w (zpow_ne_zero n hsub) hgwn hzpow hgw.differentiableAt,
    logDeriv_fun_zpow hlin, logDeriv_apply (fun u : ℂ ↦ u - z), hlin_deriv, hslope]
  ring

end Masullo
