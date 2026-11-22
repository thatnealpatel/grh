module

public import Props.CompactLogMellin
public import Theorems.PadicRamifiedThreeFourier
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Props.GammaRealLogDerivative
import Lemmas.ArchimedeanGammaDomination
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Horizontal edges for the character of conductor three

A conditional horizontal-exhaustion estimate for Mathlib's completed L-function.
The completion here does not include a conductor power. The result does not
identify an idelic completion or pass to the limit in a residue sum.
-/

open Complex Filter MeasureTheory Set
open scoped ContDiff Topology

namespace Masullo

local notation "χ₃" => padicRamifiedThreeCharacter
local notation "bare₃" => DirichletCharacter.LFunction padicRamifiedThreeCharacter
local notation "completed₃" => DirichletCharacter.completedLFunction padicRamifiedThreeCharacter

private theorem gammaReal_differentiableAt {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Gammaℝ w := by
  rw [← show archimedeanGammaFactor Real.pi 2 0 0 = Gammaℝ by
    simpa using archimedeanGammaFactor_real 0 0]
  exact (analyticOnNhd_archimedeanGammaFactor two_pos le_rfl w hw).differentiableAt

private theorem three_completion_eq {s : ℂ} (hs : 0 < (s + 1).re) :
    completed₃ s = bare₃ s * Gammaℝ (s + 1) := by
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ₃ s
    (Or.inr (by decide : 3 ^ 1 ≠ (1 : ℕ)))
  rw [padicRamifiedThreeCharacter_odd.gammaFactor_def] at h
  exact ((eq_div_iff (Gammaℝ_ne_zero_of_re_pos hs)).mp h).symm

private theorem three_completion_logDeriv {s : ℂ} (hs : 0 < (s + 1).re)
    (hL : bare₃ s ≠ 0) :
    logDeriv completed₃ s = logDeriv bare₃ s + logDeriv Gammaℝ (s + 1) := by
  have hne : χ₃ ≠ 1 := by
    intro h
    apply DirichletCharacter.Odd.not_even χ₃ padicRamifiedThreeCharacter_odd
    rw [h]
    exact DirichletCharacter.even_one
  have hN : ∀ᶠ z : ℂ in 𝓝 s, 0 < (z + 1).re :=
    IsOpen.mem_nhds
      (isOpen_lt continuous_const (continuous_re.comp (continuous_id.add continuous_const))) hs
  have hEq : completed₃ =ᶠ[𝓝 s] fun z ↦ bare₃ z * Gammaℝ (z + 1) :=
    hN.mono fun _ hz ↦ three_completion_eq hz
  have hg := gammaReal_differentiableAt hs
  have hshift : HasDerivAt (fun z : ℂ ↦ z + 1) 1 s := (hasDerivAt_id s).add_const 1
  have hgd : DifferentiableAt ℂ (fun z : ℂ ↦ Gammaℝ (z + 1)) s := by
    change DifferentiableAt ℂ (Gammaℝ ∘ fun z : ℂ ↦ z + 1) s
    exact hg.comp s hshift.differentiableAt
  rw [(logDeriv_congr_nhds hEq).eq_of_nhds,
    logDeriv_fun_mul (g := fun z ↦ Gammaℝ (z + 1)) s hL (Gammaℝ_ne_zero_of_re_pos hs)
      (DirichletCharacter.differentiable_LFunction hne s) hgd,
    logDeriv_fun_comp (f := Gammaℝ) (g := fun z : ℂ ↦ z + 1) (x := s) hg hshift.differentiableAt,
    hshift.deriv, mul_one]

private theorem norm_logDeriv_GammaReal_strip :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u ∈ Icc (1 / 2 : ℝ) (5 / 2), ∀ t : ℝ,
      ‖logDeriv Gammaℝ ((u : ℂ) + (t : ℂ) * I)‖ ≤ D * (1 + |t|) := by
  let E (x : ℝ) := (1 / 2 + x) * Real.exp (-(1 / 2) * x)
  let J := ∫ x in Ioi (0 : ℝ), E x
  let c : ℂ := -((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2
  have he : IntegrableOn (fun x : ℝ ↦ Real.exp (-(1 / 2) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hxe : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-(1 / 2) * x)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num)
      one_pos (by norm_num : (0 : ℝ) < 1 / 2))
  have hE : IntegrableOn E (Ioi 0) :=
    ((he.const_mul (1 / 2)).add hxe).congr
      (Eventually.of_forall fun x ↦ (add_mul (1 / 2) x _).symm)
  have hJ : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun x hx ↦
    mul_nonneg (by have : 0 < x := hx; linarith) (Real.exp_pos _).le
  refine ⟨‖c‖ + 2 * J, by positivity, fun u hu t ↦ ?_⟩
  let w : ℂ := (u : ℂ) + (t : ℂ) * I
  let K := archimedeanGammaKernel 2 w
  have hw : 0 < w.re := by simpa [w] using (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hu.1)
  obtain ⟨hK, hval⟩ := logDeriv_GammaReal_eq_integral hw
  have hK' : IntegrableOn K (Ioi 0) := by
    change IntegrableOn (fun x ↦ archimedeanGammaKernel 2 w x) (Ioi 0)
    simpa only [archimedeanGammaKernel, ofReal_ofNat, neg_mul] using hK
  have hval' : logDeriv Gammaℝ w = c + ∫ x in Ioi (0 : ℝ), K x := by
    simpa [c, K, archimedeanGammaKernel] using hval
  have hKbd (x : ℝ) (hx : 0 < x) : ‖K x‖ ≤ (2 + |t|) * E x := by
    have hu₂ : |2 - u| ≤ 2 := abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hmin : 1 / 2 ≤ min 2 u := le_min (by norm_num) hu.1
    refine (norm_archimedeanGammaKernel_le (u := u) (v := t) two_pos hx).trans ?_
    dsimp [E]
    gcongr
  have hI : ‖∫ x in Ioi (0 : ℝ), K x‖ ≤ (2 + |t|) * J := by
    rw [← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae hK'.norm
      (hE.const_mul (2 + |t|)) ?_)
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi] with x hx
    exact hKbd x hx
  show ‖logDeriv Gammaℝ w‖ ≤ _
  rw [hval']
  calc
    _ ≤ ‖c‖ + (2 + |t|) * J := (norm_add_le _ _).trans (add_le_add_right hI _)
    _ ≤ (‖c‖ + 2 * J) * (1 + |t|) := by
      nlinarith [mul_nonneg (norm_nonneg c) (abs_nonneg t), mul_nonneg hJ (abs_nonneg t)]

private theorem tendsto_three_horizontal {w : ℕ → ℝ}
    (hw : Tendsto (fun n ↦ |w n|) atTop atTop)
    {C : ℝ} (hC : 0 < C) {m : ℕ}
    (hL : ∀ n σ, σ ∈ Icc (-1 / 2 : ℝ) (3 / 2) →
      ‖logDeriv completed₃ ((σ : ℂ) + (w n : ℂ) * I)‖ ≤ C * (1 + |w n|) ^ m)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    Tendsto (fun n ↦ ∫ σ in (-1 / 2 : ℝ)..(3 / 2),
      let s := (σ : ℂ) + (w n : ℂ) * I
      compactLogMellin g s * logDeriv completed₃ s) atTop (𝓝 0) := by
  obtain ⟨B, _, hM⟩ := compactLogMellin_vertical_decay hg hcg (3 / 2) (m + 1)
  have hinv : Tendsto (fun n ↦ (1 + |w n|)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n ↦ by linarith) hw)
  refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using hinv.const_mul (2 * (B * C)))
  have hpos : 0 < 1 + |w n| := by positivity
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -1 / 2) (b := 3 / 2) (C := B * C / (1 + |w n|)) (f := fun σ : ℝ ↦
      let s := (σ : ℂ) + (w n : ℂ) * I
      compactLogMellin g s * logDeriv completed₃ s) (by
    intro σ hσ
    rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2)] at hσ
    have hm : σ ∈ Icc (-1 / 2 : ℝ) (3 / 2) := ⟨hσ.1.le, hσ.2⟩
    have habs : |σ| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hm.1], hm.2⟩
    dsimp only
    rw [norm_mul]
    calc
      _ ≤ (B / (1 + |w n|) ^ (m + 1)) * (C * (1 + |w n|) ^ m) :=
        mul_le_mul (hM σ _ habs) (hL n σ hm) (norm_nonneg _) (by positivity)
      _ = B * C / (1 + |w n|) := by rw [pow_succ]; field_simp)
  refine hbd.trans_eq ?_
  norm_num
  ring

/-- A simultaneous bare estimate on the two tails gives the same heights for
Mathlib's odd completed L-function, and for the vanishing horizontal pairings
with every smooth compact log profile. -/
public theorem padicRamifiedThree_completed_horizontal_of_bare
    (hbare : ∃ (C : ℝ) (m : ℕ), 0 < C ∧ ∀ H : ℝ, 1 ≤ H →
      ∃ T ∈ Ioo H (H + 1), ∀ σ ∈ Icc (-1 / 2 : ℝ) (3 / 2), ∀ t : ℝ, |t| = T →
        let s := (σ : ℂ) + (t : ℂ) * I
        bare₃ s ≠ 0 ∧ ‖logDeriv bare₃ s‖ ≤ C * (1 + T) ^ m) :
    ∃ (T : ℕ → ℝ) (C : ℝ) (m : ℕ), 0 < C ∧
      (∀ n : ℕ, T n ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2)) ∧
      (∀ n, ∀ σ ∈ Icc (-1 / 2 : ℝ) (3 / 2), ∀ t : ℝ, |t| = T n →
        let s := (σ : ℂ) + (t : ℂ) * I
        completed₃ s ≠ 0 ∧ ‖logDeriv completed₃ s‖ ≤ C * (1 + T n) ^ m) ∧
      (∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
        (Tendsto (fun n ↦ ∫ σ in (-1 / 2 : ℝ)..(3 / 2),
          let s := (σ : ℂ) + (T n : ℂ) * I
          compactLogMellin g s * logDeriv completed₃ s) atTop (𝓝 0)) ∧
        (Tendsto (fun n ↦ ∫ σ in (-1 / 2 : ℝ)..(3 / 2),
          let s := (σ : ℂ) - (T n : ℂ) * I
          compactLogMellin g s * logDeriv completed₃ s) atTop (𝓝 0))) := by
  obtain ⟨C, m, hC, h⟩ := hbare
  obtain ⟨D, hD, hΓ⟩ := norm_logDeriv_GammaReal_strip
  have hseq (n : ℕ) := h ((n : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))
  choose T hT hL using hseq
  have hse (n : ℕ) : T n ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    convert hT n using 2; ring
  have hTpos (n : ℕ) : 0 < T n := (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos).trans (hse n).1
  have hlim : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith [(hse n).1]) tendsto_natCast_atTop_atTop
  have hbound (n : ℕ) (σ : ℝ) (hσ : σ ∈ Icc (-1 / 2 : ℝ) (3 / 2)) (t : ℝ) (ht : |t| = T n) :
      let s := (σ : ℂ) + (t : ℂ) * I
      completed₃ s ≠ 0 ∧ ‖logDeriv completed₃ s‖ ≤ (C + D) * (1 + T n) ^ (m + 1) := by
    let s : ℂ := (σ : ℂ) + (t : ℂ) * I
    have hshift : s + 1 = ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      dsimp [s]
      push_cast
      ring
    have hs : 0 < (s + 1).re := by
      rw [hshift]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul, sub_zero,
        add_zero]
      linarith [hσ.1]
    obtain ⟨hne, hbd⟩ := hL n σ hσ t ht
    change completed₃ s ≠ 0 ∧ ‖logDeriv completed₃ s‖ ≤ _
    refine ⟨by rw [three_completion_eq hs]; exact mul_ne_zero hne (Gammaℝ_ne_zero_of_re_pos hs), ?_⟩
    have h₁ : 1 ≤ 1 + T n := by linarith [hTpos n]
    have hΓ' : ‖logDeriv Gammaℝ (s + 1)‖ ≤ D * (1 + T n) := by
      rw [hshift, ← ht]
      exact hΓ (σ + 1) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
    rw [three_completion_logDeriv hs hne]
    calc
      _ ≤ C * (1 + T n) ^ m + D * (1 + T n) :=
        (norm_add_le _ _).trans (add_le_add hbd hΓ')
      _ ≤ C * (1 + T n) ^ (m + 1) + D * (1 + T n) ^ (m + 1) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h₁ (Nat.le_succ m)) hC.le)
          (mul_le_mul_of_nonneg_left ?_ hD)
        simpa using pow_le_pow_right₀ h₁ (Nat.succ_le_succ (Nat.zero_le m))
      _ = _ := by ring
  have hCD : 0 < C + D := add_pos_of_pos_of_nonneg hC hD
  refine ⟨T, C + D, m + 1, hCD, hse, hbound, fun g hg hcg ↦ ⟨?_, ?_⟩⟩
  · refine tendsto_three_horizontal (w := T) ?_ hCD (m := m + 1) ?_ hg hcg
    · simpa only [abs_of_pos (hTpos _)] using hlim
    · intro n σ hσ
      rw [abs_of_pos (hTpos n)]
      exact (hbound n σ hσ (T n) (abs_of_pos (hTpos n))).2
  · have hw (n : ℕ) : |-T n| = T n := by rw [abs_neg, abs_of_pos (hTpos n)]
    have hn : Tendsto (fun n ↦ |-T n|) atTop atTop := by simpa only [hw] using hlim
    simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using
      (tendsto_three_horizontal (w := fun n ↦ -T n) hn hCD
        (m := m + 1) (fun n σ hσ ↦ by rw [hw]; exact (hbound n σ hσ _ (hw n)).2) hg hcg)

end Masullo
