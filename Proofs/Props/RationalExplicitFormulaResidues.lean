module

public import Lemmas.CompletedZetaOrders
public import Lemmas.TestedLogDeriv

/-!
# The local terms in the rational explicit formula

Masullo (B.4.2.2), p. 614, takes the logarithmic derivative of the completed
function. The coefficients of the tested principal parts are the actual zeta
orders at the distinct critical-strip zeros, and minus the test value at each
of 0 and 1. In particular, the two terms in the contour calculation are not
residues of the uncompleted zeta function. The rational reflection identity
records the chain-rule minus sign needed between (B.4.2.2) and (B.4.2.4).
-/

open Filter Set
open scoped Topology

namespace Masullo

/-- The zero in (B.4.2.2) contributes its full order times the analytic test
value. The remainder is analytic even when the test vanishes at the zero. -/
public theorem completedZeta_tested_zero_principalPart (ρ : criticalStripZetaZeros)
    {Φ : ℂ → ℂ} (hΦ : AnalyticAt ℂ Φ (ρ : ℂ)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H (ρ : ℂ) ∧
      (fun w ↦ Φ w * logDeriv completedRiemannZeta w) =ᶠ[𝓝[≠] (ρ : ℂ)]
        fun w ↦ (zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ) / (w - (ρ : ℂ)) + H w := by
  obtain ⟨_, hp, hl⟩ := mem_criticalStripZetaZeros.mp ρ.property
  have h0 : (ρ : ℂ) ≠ 0 := by intro h; simp [h] at hp
  have h1 : (ρ : ℂ) ≠ 1 := by intro h; simp [h] at hl
  have horder : meromorphicOrderAt completedRiemannZeta (ρ : ℂ) =
      ((zetaZeroOrder ρ : ℤ) : WithTop ℤ) := by
    have ha := entireZeta_analyticOnNhd (ρ : ℂ) (mem_univ _)
    have hn : (zetaZeroOrder ρ : ℕ∞) = analyticOrderAt entireZeta (ρ : ℂ) := by
      rw [analyticOrderAt_entireZeta_eq hp hl, zetaZeroOrder_cast_eq]
    rw [order_completedZeta_away h0 h1, ha.meromorphicOrderAt_eq, ← hn, ENat.map_natCast]
  simpa only [Int.cast_natCast] using
    logDeriv_weighted_principalPart (meromorphicAt_completedZeta _) horder hΦ

/-- The two poles of the completed function give negative test values in
(B.4.2.2), before shifting the test argument by one half. -/
public theorem completedZeta_tested_pole_principalPart {z : ℂ} (hz : z = 0 ∨ z = 1)
    {Φ : ℂ → ℂ} (hΦ : AnalyticAt ℂ Φ z) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧
      (fun w ↦ Φ w * logDeriv completedRiemannZeta w) =ᶠ[𝓝[≠] z]
        fun w ↦ -Φ z / (w - z) + H w := by
  simpa only [Int.cast_neg, Int.cast_one, neg_one_mul] using
    logDeriv_weighted_principalPart (meromorphicAt_completedZeta z) (order_completedZeta_atPole hz) hΦ

/-- In the rational completed case, differentiating reflection gives a minus
sign. This is the sign used by the reflected vertical integral in (B.4.2.4). -/
public theorem completedZeta_logDeriv_reflection {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    logDeriv completedRiemannZeta z = -logDeriv completedRiemannZeta (1 - z) := by
  have h : (fun w ↦ completedRiemannZeta (1 - w)) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  have hd : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z := (hasDerivAt_id z).const_sub 1
  have hdiff := differentiableAt_completedZeta (s := 1 - z)
    (sub_ne_zero.mpr h1.symm) (by simpa using h0)
  simpa only [h, hd.deriv, mul_neg_one] using logDeriv_fun_comp hdiff hd.differentiableAt

end Masullo
