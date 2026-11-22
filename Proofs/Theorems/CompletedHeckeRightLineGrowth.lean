module

public import Theorems.CompletedHeckeEulerProduct
import Lemmas.ArchimedeanGammaDomination

/-! # Right vertical control for a completed Hecke continuation

Section B.4.2.1, p. 614, invokes slow growth to justify (B.4.2.2).
Masullo supplies the local decomposition (B.4.2.5)–(7), p. 615, and the
archimedean digamma terms (B.4.2.12), pp. 615–616. Use the checked
local sum identity, the summable finite-place majorant, and an
integrable archimedean envelope to bound the logarithmic derivative
on the actual right line. Euler agreement as germs transfers the
bound to the same function used on the rest of the contour. This
supplies no left-line or exhaustion estimate. The source reading is
provisional (pinned Markdown and numbered PDF layout).
-/

open Complex Filter NumberField
open scoped Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

/-- Any function agreeing with the completed Euler product on the open
half-plane inherits nonvanishing and linear logarithmic-derivative growth
on each fixed right vertical line. In particular no exchange of the
continuation witness is needed to combine this with horizontal control. -/
public theorem completedHecke_rightLine_nonzero_logDeriv_bound
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ c, ‖χ c‖ = 1)
    {L : ℂ → ℂ} (hEuler : ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ hχ s)
    {a : ℝ} (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, let s : ℂ := (a : ℂ) + (t : ℂ) * I
      L s ≠ 0 ∧ ‖logDeriv L s‖ ≤ C * (1 + |t|) := by
  classical
  let s (t : ℝ) : ℂ := (a : ℂ) + (t : ℂ) * I
  have hs (t : ℝ) : 1 < (s t).re := by simpa [s, mul_re] using ha
  -- Each infinite place has a fixed real or complex Gamma factor.
  have hlocal (v : InfinitePlace K) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv (localHeckeGammaFactor χ hχ v) (s t)‖ ≤ C * (1 + |t|) := by
    rcases v.isReal_or_isComplex with hv | hv
    · obtain ⟨b, τ, _, _, hΓ⟩ := localHeckeGammaFactor_real χ hχ hv
      rw [hΓ]
      exact archimedeanGammaFactor_rightLine_logDeriv_bound (zero_lt_one.trans ha)
        (by norm_num) (Nat.cast_nonneg b) Real.pi τ
    · obtain ⟨n, τ, _, hΓ⟩ := localHeckeGammaFactor_complex χ hχ hv
      rw [hΓ]
      exact archimedeanGammaFactor_rightLine_logDeriv_bound (zero_lt_one.trans ha)
        (by norm_num) (by positivity) (2 * Real.pi) τ
  choose c hc hcBound using hlocal
  let M := ∑' p, finiteHeckeMajorant (K := K) a p
  have hM : 0 ≤ M := by
    apply tsum_nonneg
    intro p
    exact div_nonneg (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans (two_le_finitePlaceNorm p.1)))
      (Real.rpow_nonneg (zero_le_two.trans (two_le_finitePlaceNorm p.1)) _)
  have hsum : 0 ≤ ∑ v, c v := Finset.sum_nonneg fun v _ ↦ (hc v).le
  refine ⟨(∑ v, c v) + M + 1, by positivity, fun t ↦ ?_⟩
  let P := completedHeckeEulerProduct χ hχ
  have hL : L =ᶠ[𝓝 (s t)] P := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (hs t)] with z hz
    exact hEuler z hz
  obtain ⟨hnz, _, hseries⟩ := completedHeckeEulerProduct_logDeriv χ hχ (hs t)
  change L (s t) ≠ 0 ∧ _
  refine ⟨(hL.eq_of_nhds).trans_ne hnz, ?_⟩
  have hlog := (logDeriv_congr_nhds hL).eq_of_nhds
  -- The finite part is uniformly bounded in the ordinate by the same majorant.
  obtain ⟨hMsum, hmajor⟩ := finiteHecke_right_line_majorant (K := K) ha
  have hpoint := hmajor (finiteHeckeCoefficient χ) (norm_finiteHeckeCoefficient_le_one χ hχ)
    (s t) (by simp [s, mul_re])
  have hfin : ‖(∑ v, logDeriv (localHeckeGammaFactor χ hχ v) (s t)) - logDeriv P (s t)‖ ≤ M := by
    rw [← hseries.tsum_eq]
    have hnorm := (hMsum.of_norm_bounded hpoint).norm
    exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hpoint hMsum)
  let G := ∑ v, logDeriv (localHeckeGammaFactor χ hχ v) (s t)
  have hG : ‖G‖ ≤ (∑ v, c v) * (1 + |t|) := by
    dsimp only [G]
    rw [Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ hcBound v t)
  change ‖logDeriv L (s t)‖ ≤ _
  rw [hlog, show logDeriv P (s t) = G - (G - logDeriv P (s t)) by abel]
  exact (norm_sub_le _ _).trans ((add_le_add hG hfin).trans (by
    nlinarith [abs_nonneg t, mul_nonneg hM (abs_nonneg t)]))

end Masullo
