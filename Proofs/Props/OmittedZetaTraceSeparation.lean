module

public import Props.FilteredLogTraceSeparation
public import Props.OmittedZetaTailBudget
import Lemmas.FiniteMellinRootPolynomial
import Lemmas.MellinFrequencyPadding
import Lemmas.RationalCompletedZetaZeros
import Mathlib.Tactic.Linarith

/-!
# A short trace-density test killing the omitted rational zeta divisor

Theorem 12.5.1.1, pp. 519–520, (12.5.1.3–4), supplies the two polar
samples and the sum over the interior of the strip. In contrast the
completed explicit formula at (B.4.2.2), p. 614, uses the full zero sum.
With `t = -log |g|`, the positive-log Mellin convention of (B.2.1.29),
p. 599, gives the class samples at the *negative* of the shifted zeros.
The integration-by-parts sign in (B.2.1.31) then evaluates the derivative
polynomial at the shifted zeros themselves. These locators are from a
provisional Markdown and PDF text-layout reading.

Neither sum constructs a short test that kills all omitted samples while
separating the two rational model densities. This original construction
uses `exists_omittedZetaTail_reciprocal_budget` to split off a small-cost
actual tail and `exists_compactLogMellin_filter_trace_separation` to retain
both pairings and all vanishings in the same test. It neither proves the
count hypothesis nor identifies any manuscript trace with a model pairing.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

local notation "J" => (fun t : ℝ ↦ Real.exp ((-1 / 2) * t) / (1 - Real.exp (-2 * t)))
local notation "U[" β "]" =>
  (fun t : ℝ ↦ Real.exp ((β - 5 / 2) * t) / (1 - Real.exp (-2 * t)))

/-- A fixed-width dyadic count gives a smooth witness in any below-one log
window. It kills the polar samples and every distinct zeta sample omitted
from the open strip, including samples on the strip edges. -/
public theorem exists_compactLogMellin_omittedZeta_trace_separation {α C q : ℝ}
    (hq₀ : 0 ≤ q) (hq₂ : q < 2)
    (hcount : ∀ (j : ℕ) (A : Finset criticalStripZetaZeros),
      (∀ ρ ∈ A, 1 / 2 + α ≤ (ρ : ℂ).re ∧ 0 < (ρ : ℂ).im ∧
        (ρ : ℂ).im < (2 : ℝ) ^ (j + 1)) → (A.card : ℝ) ≤ C * q ^ j)
    {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    {L U : ℝ} (hL : 0 ≤ L) (hLU : L < U) (_hU : U ≤ Real.log 2) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ tsupport f ⊆ Ioo L U ∧
      (Integrable (fun t ↦ J t * f t) ∧ (∫ t, J t * f t) = 0) ∧
      (Integrable (fun t ↦ U[β] t * f t) ∧ (∫ t, U[β] t * f t) ≠ 0) ∧
      compactLogMellin (fun t ↦ (f t : ℂ)) (1 / 2) = 0 ∧
      compactLogMellin (fun t ↦ (f t : ℂ)) (-1 / 2) = 0 ∧
      ∀ ρ : criticalStripZetaZeros, α ≤ |(shiftedZetaZero ρ).re| →
        compactLogMellin (fun t ↦ (f t : ℂ)) (-(shiftedZetaZero ρ)) = 0 := by
  classical
  let a := L + (U - L) / 4
  let b := L + (U - L) / 2
  let ε := (U - b) / 2
  have hLa : L < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hε : 0 < ε := by dsimp [ε, b]; linarith
  obtain ⟨T, hT, htail, hsmall⟩ := exists_omittedZetaTail_reciprocal_budget hq₀ hq₂ hcount hε
  -- Use the reflected Mellin argument as the frequency in the high tail.
  let z (ρ : omittedZetaTail α T) := -(shiftedZetaZero ρ.val)
  have hzabs (ρ : omittedZetaTail α T) : |(z ρ).im| = |(ρ.val : ℂ).im| := by
    simp [z, shiftedZetaZero]
  have hzne (ρ : omittedZetaTail α T) : (z ρ).im ≠ 0 := by
    have hp : 0 < |(z ρ).im| := by
      rw [hzabs]
      exact zero_lt_one.trans (hT.trans_lt ρ.property.2)
    exact abs_pos.mp hp
  have hzs : Summable (fun ρ ↦ Real.pi / |(z ρ).im|) := htail.congr fun ρ ↦ by rw [hzabs]
  obtain ⟨w, hwim, hws, hwcost, hwcover⟩ := exists_mellinFrequency_sequence z hzne hzs hε
  simp only [hzabs] at hwcost
  have hbudget : b + (∑' n, Real.pi / |(w n).im|) < U := by
    dsimp [ε] at hsmall hwcost
    linarith
  -- All low omitted locations form a finite set, even if a low height is zero.
  let S : Set criticalStripZetaZeros :=
    {ρ | α ≤ |(shiftedZetaZero ρ).re| ∧ |(ρ : ℂ).im| ≤ T}
  have hS : S.Finite := (criticalStripZetaZeros_boundedIm_finite (-T - 1) (T + 1)).subset <| by
    intro ρ hρ
    obtain ⟨hl, hu⟩ := abs_le.mp hρ.2
    exact ⟨by linarith, by linarith⟩
  -- The real derivative polynomial kills the two poles and the low family,
  -- but stays positive at the nonvanishing projected-density sample.
  obtain ⟨P, hpolar, hproj, hplus, hminus, hlow⟩ :=
    exists_real_polynomial_polar_and_finite_roots hS.toFinset shiftedZetaZero
      (x := 5 / 2 - β) (by linarith) (by
        intro ρ _
        exact (lt_of_le_of_lt (le_abs_self _) (abs_re_shiftedZetaZero_lt ρ)).trans (by linarith))
  obtain ⟨f, hf, hsupp, hJ, hUβ, hmellin⟩ :=
    exists_compactLogMellin_filter_trace_separation w hwim hws (hL.trans_lt hLa) hab
      hpolar hβ₀ hproj.ne'
  refine ⟨f, hf, hsupp.trans (fun _ ht ↦ ⟨hLa.trans_le ht.1, ht.2.trans_lt hbudget⟩),
    hJ, hUβ, hmellin _ (.inl ?_), hmellin _ (.inl ?_), ?_⟩
  · simpa only [neg_div] using hminus
  · simpa only [neg_div, neg_neg] using hplus
  · intro ρ hρ
    apply hmellin
    by_cases ht : T < |(ρ : ℂ).im|
    · exact Or.inr (hwcover ⟨⟨ρ, hρ, ht⟩, rfl⟩)
    · exact Or.inl (by simpa only [neg_neg] using hlow ρ (hS.mem_toFinset.mpr ⟨hρ, le_of_not_gt ht⟩))

end Masullo
