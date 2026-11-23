module

public import Theorems.CompletedHeckeOneRectangle
public import Props.TestedRectangleBoundaryLimit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Good-height contour exhaustion for the completed trivial Hecke product

This is the limit along good rectangles in (B.4.2.2), p. 614. Use the
signed finite residue theorem and the repair of (B.3.2.4)–(5), p. 606, in
`tendsto_rectangleIntegral_compactLogMellin_logDeriv`. The finite zero sums
retain full orders and both pole terms. This does not yet identify their
limit with an unrestricted absolutely convergent sum.
Source reading provisional (pinned Markdown and numbered PDF layout).
-/

open Complex Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [BorelSpace (ideleNormOne (K := K))]

/-- For the same continuation and numerator as the finite rectangle theorem,
one choice of heights and zero sets works for every compact-log test. -/
public theorem completedHecke_one_tendsto_zeroSum_at_good_heights
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {L H : ℂ → ℂ}
    (hL : Meromorphic L) (hdiffL : ∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s)
    (hEuler : ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s)
    {B : ℝ} (hgood : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, (n : ℝ) < T ∧ T < (n : ℝ) + 1 ∧
      ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
        L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ B * (1 + |z.im|)^2) :
    ∃ (T : ℕ → ℝ) (Z : ℕ → Finset ℂ),
      (∀ n : ℕ, (n : ℝ) + 1 < T n ∧ T n < (n : ℝ) + 2 ∧
        ∀ z, z ∈ Z n ↔ z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (-T n) (T n) ∧ H z = 0) ∧
      ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
        let Φ := compactLogMellin g
        let V := fun (σ t : ℝ) ↦ Φ ((σ : ℂ) + (t : ℂ) * I) *
          logDeriv L ((σ : ℂ) + (t : ℂ) * I)
        Integrable (V 2) ∧ Integrable (V (-1)) ∧
          Tendsto (fun n ↦ ∑ z ∈ Z n, (analyticOrderNatAt H z : ℂ) * Φ z) atTop
            (𝓝 (Φ 0 + Φ 1 + ((∫ t, V 2 t) - (∫ t, V (-1) t)) / (2 * (Real.pi : ℂ)))) := by
  obtain ⟨C, _, hV, hrect⟩ :=
    completedHecke_one_rectangle_at_good_heights v r hr hL hdiffL hEuler hH hclear hgood
  -- Choose the rectangles before the test, keeping their residue identities.
  have hex (n : ℕ) := hrect (n + 1) (by omega)
  choose T hnT hTn hHorz Z hZ hResidue using hex
  have hT₀ (n : ℕ) : 0 ≤ T n := (Nat.cast_nonneg (n + 1)).trans (hnT n).le
  have hT : Tendsto T atTop atTop := tendsto_atTop_mono (fun n ↦ by
    simpa using (show (n : ℝ) ≤ T n by push_cast at hnT; linarith [hnT n]))
    tendsto_natCast_atTop_atTop
  refine ⟨T, Z, fun n ↦ ⟨by simpa using hnT n, ?_, hZ n⟩, ?_⟩
  · push_cast at hTn
    linarith [hTn n]
  intro g hg hc
  obtain ⟨hr', hl', hBoundary⟩ := tendsto_rectangleIntegral_compactLogMellin_logDeriv
    hdiffL hV hT₀ hT (fun n z h₁ h₂ hz ↦ (hHorz n z h₁ h₂ hz).2) hg hc
  refine ⟨hr', hl', ?_⟩
  -- Divide by 2πi (the vertical ds = i dt cancels i) and restore both poles.
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hπ) I_ne_zero
  have hconst : Tendsto (fun _ : ℕ ↦ compactLogMellin g 0 + compactLogMellin g 1)
      atTop (𝓝 (compactLogMellin g 0 + compactLogMellin g 1)) := tendsto_const_nhds
  have hlim := hconst.add (hBoundary.div_const (2 * (Real.pi : ℂ) * I))
  have hterm (n : ℕ) : compactLogMellin g 0 + compactLogMellin g 1 +
      rectangleIntegral (-1) 2 (-T n) (T n) (fun s ↦ compactLogMellin g s * logDeriv L s) /
        (2 * (Real.pi : ℂ) * I) =
      ∑ z ∈ Z n, (analyticOrderNatAt H z : ℂ) * compactLogMellin g z := by
    rw [hResidue n g hg hc, mul_div_cancel_left₀ _ hd]
    ring
  simpa only [← mul_sub, mul_comm I (2 * (Real.pi : ℂ)), mul_comm I (_ - _),
    mul_div_mul_right _ _ I_ne_zero] using hlim.congr hterm

end Masullo
