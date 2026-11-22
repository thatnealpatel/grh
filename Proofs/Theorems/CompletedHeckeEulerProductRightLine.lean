module

public import Lemmas.TrivialHeckeGammaFactor
public import Lemmas.GammaRightLineLowerBound
public import Theorems.FiniteHeckeEulerProductLowerBound

/-! # Bound the completed trivial Hecke product on the right line

The center cost for the Euler-domain product is affine in absolute height.
It is a logarithmic loss, not a polynomial estimate for the reciprocal norm.
-/

open Complex NumberField InfinitePlace

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]
local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)

/-- The constant part of the logarithmic loss: the finite-place sum plus the
normalizing powers of `π` and `2π`, counted once per infinite place. -/
@[expose] public noncomputable def trivialHeckeRightLineLoss : ℝ :=
  finiteHeckeRightLineLoss K + nrRealPlaces K * Real.log Real.pi +
    nrComplexPlaces K * (2 * Real.log (2 * Real.pi))

/-- An exponential lower bound with degree-dependent slope, for all heights
(including zero). The argument of the product always has real part two. -/
public theorem completedHeckeEulerProduct_one_rightLine_lower_bound (t : ℝ) :
    Real.exp (-trivialHeckeRightLineLoss K - Module.finrank ℚ K * Real.pi * |t| / 4) ≤
      ‖completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) (2 + (t : ℂ) * I)‖ := by
  classical
  let s : ℂ := 2 + (t : ℂ) * I
  let a := -Real.log Real.pi - Real.pi * |t| / 4
  let b := -(2 * Real.log (2 * Real.pi)) - Real.pi * |t| / 2
  let L (v : InfinitePlace K) := if v.IsReal then Real.exp a else Real.exp b
  have hL (v : InfinitePlace K) : L v ≤ ‖localHeckeGammaFactor χ₀ (fun _ ↦ norm_one) v s‖ := by
    rcases v.isReal_or_isComplex with hr | hc
    · rw [localHeckeGammaFactor_one_real hr]
      simpa [L, hr, a, s] using norm_archimedeanGammaFactor_real_rightLine_lower_bound t
    · rw [localHeckeGammaFactor_one_complex hc]
      simpa [L, not_isReal_iff_isComplex.mpr hc, b, s] using
        norm_archimedeanGammaFactor_complex_rightLine_lower_bound t
  have hprod : (∏ v, L v) = Real.exp (nrRealPlaces K * a + nrComplexPlaces K * b) := by
    dsimp only [L]
    rw [Finset.prod_ite, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
    simp only [Finset.prod_const, ← Fintype.card_subtype, not_isReal_iff_isComplex]
  have hdeg : (Module.finrank ℚ K : ℝ) = nrRealPlaces K + 2 * (nrComplexPlaces K : ℝ) := by
    exact_mod_cast (card_add_two_mul_card_eq_rank K).symm
  have hfinite := exp_le_norm_finiteHeckeCharacterEulerProduct χ₀ (fun _ ↦ norm_one)
    (s := s) (by simp [s])
  change _ ≤ ‖(∏ v, localHeckeGammaFactor χ₀ (fun _ ↦ norm_one) v s) *
    finiteHeckeCharacterEulerProduct χ₀ s‖
  rw [norm_mul, norm_prod]
  calc
    _ = (∏ v, L v) * Real.exp (-finiteHeckeRightLineLoss K) := by
      rw [hprod, ← Real.exp_add, hdeg]
      congr 1
      dsimp [trivialHeckeRightLineLoss, a, b]
      ring
    _ ≤ _ := mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ by dsimp [L]; split <;> positivity)
      (fun v _ ↦ hL v)) hfinite (Real.exp_nonneg _) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)

/-- The center term entering the Jensen and zero-free-disk estimates is at
most affine in height. No continuation or bound on a surrounding disk is used. -/
public theorem neg_log_norm_completedHeckeEulerProduct_one_rightLine (t : ℝ) :
    -Real.log ‖completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) (2 + (t : ℂ) * I)‖ ≤
      trivialHeckeRightLineLoss K + Module.finrank ℚ K * Real.pi * |t| / 4 := by
  have h := Real.log_le_log (Real.exp_pos _) (completedHeckeEulerProduct_one_rightLine_lower_bound K t)
  rw [Real.log_exp] at h
  linarith

/-- Center contribution for a prospective pole-cleared continuation. This only
uses `s(s-1)` on the right line; it does not supply the sphere bound `M` or
identify a continuation on the Jensen disk. -/
public theorem log_div_norm_poleCleared_completedHeckeEulerProduct_one_rightLine
    (t : ℝ) {M : ℝ} (hM : 0 < M) :
    let s : ℂ := 2 + (t : ℂ) * I
    Real.log (M / ‖s * (s - 1) * completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s‖) ≤
      Real.log M + trivialHeckeRightLineLoss K + Module.finrank ℚ K * Real.pi * |t| / 4 := by
  intro s
  have hs : s.re = 2 := by simp [s]
  have hp : 1 ≤ ‖s * (s - 1)‖ := by
    rw [norm_mul]
    apply one_le_mul_of_one_le_of_one_le
    · linarith [re_le_norm s]
    · have h := re_le_norm (s - 1)
      rw [sub_re, one_re, hs] at h
      linarith
  have h := completedHeckeEulerProduct_one_rightLine_lower_bound K t
  change _ ≤ ‖completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s‖ at h
  have h' := h.trans (le_mul_of_one_le_left (norm_nonneg _) hp)
  rw [norm_mul, Real.log_div hM.ne' ((Real.exp_pos _).trans_le h').ne']
  have hlog := Real.log_le_log (Real.exp_pos _) h'
  rw [Real.log_exp] at hlog
  linarith

end Masullo
