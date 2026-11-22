module

public import Lemmas.DirichletRightAnchor
import Lemmas.AnalyticGoodHeightDisk
import Lemmas.LogLossGoodHeight
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Common good heights for the quadratic class denominator

For the repaired horizontal-edge argument in Masullo, p. 309, §6.3.2,
apply one disk argument to the product of the two L-functions. The
analytic premise left in this module is an upper growth bound on the
outer moving circles, not any reciprocal bound or zero spacing estimate.
-/

open Complex Metric Set

namespace Masullo

private noncomputable def lossConstant : ℝ :=
  8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ)) + 2 / Real.log (6 / 5 : ℝ)

private theorem lossConstant_nonneg : 0 ≤ lossConstant := by
  have h : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have h' : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  unfold lossConstant
  positivity

private theorem exists_one_goodHeight {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {H M : ℝ} {c : ℂ} (hc : c = 2 + ((H + 1 / 2 : ℝ) : ℂ) * I)
    (hn : f c ≠ 0) (hM : 1 ≤ M) (hbd : ∀ z ∈ sphere c 6, ‖f z‖ ≤ M) :
    ∃ T ∈ Ioo H (H + 1), ∀ σ ∈ Icc (-1 / 2 : ℝ) 2,
      let z := (σ : ℂ) + (T : ℂ) * I
      f z ≠ 0 ∧ Real.log ‖f c‖ - 8 - lossConstant * Real.log (M / ‖f c‖) ≤
        Real.log ‖f z‖ := by
  classical
  obtain ⟨A, n, g, hfac, hcount, hinner⟩ := exists_goodHeight_disk_factorization hf hn hM hbd
  obtain ⟨T, hT, hne, hsum⟩ := exists_goodHeight_sum_posLog A Complex.im n H
  refine ⟨T, hT, fun σ hσ ↦ ?_⟩
  let z := (σ : ℂ) + (T : ℂ) * I
  have hzre : (z - c).re = σ - 2 := by simp [z, hc]
  have hzim : (z - c).im = T - (H + 1 / 2) := by simp [z, hc]
  have hz : z ∈ closedBall c 3 := by
    rw [mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hzre, hzim]
    have hσ' := hσ.2
    have hs := hσ.1
    have ht := hT.1
    have ht' := hT.2
    rw [abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    have hre : -(σ - 2) ≤ 5 / 2 := by linarith
    have him : |T - (H + 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hdist (ρ : ℂ) (hρ : ρ ∈ A) : 0 < ‖z - ρ‖ := by
    have h := Complex.abs_im_le_norm (z - ρ)
    rw [sub_im] at h
    simp only [z, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
      mul_zero, zero_add, add_zero] at h
    exact (abs_pos.mpr (sub_ne_zero.mpr (hne ρ hρ))).trans_le h
  have hloss (ρ : ℂ) (hρ : ρ ∈ A) :
      -max 0 (-Real.log |T - ρ.im|) ≤ Real.log ‖z - ρ‖ := by
    have h := Complex.abs_im_le_norm (z - ρ)
    have hiz : (z - ρ).im = T - ρ.im := by simp [z]
    rw [hiz] at h
    have hl := Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr (hne ρ hρ))) h
    linarith [le_max_right (0 : ℝ) (-Real.log |T - ρ.im|)]
  obtain ⟨hg, hgl⟩ := hinner z hz
  have hp : ∏ ρ ∈ A, ‖z - ρ‖ ^ n ρ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦ pow_ne_zero _ (hdist ρ hρ).ne'
  have hlog : Real.log ‖f z‖ = (∑ ρ ∈ A, (n ρ : ℝ) * Real.log ‖z - ρ‖) + Real.log ‖g z‖ := by
    rw [hfac z, norm_mul, norm_prod]
    simp only [norm_pow]
    rw [Real.log_mul hp (norm_ne_zero_iff.mpr hg),
      Real.log_prod (fun ρ hρ ↦ pow_ne_zero (n ρ) (hdist ρ hρ).ne')]
    simp only [Real.log_pow]
  have hsum' : -(∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |T - ρ.im|)) ≤
      ∑ ρ ∈ A, (n ρ : ℝ) * Real.log ‖z - ρ‖ := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ρ hρ
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (hloss ρ hρ) (Nat.cast_nonneg _)
  have hK : 2 * (Real.log (M / ‖f c‖) / Real.log (6 / 5 : ℝ)) =
      (2 / Real.log (6 / 5 : ℝ)) * Real.log (M / ‖f c‖) := by ring
  change f z ≠ 0 ∧ _
  refine ⟨?_, ?_⟩
  · rw [hfac z]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ ↦
      pow_ne_zero _ (norm_pos_iff.mp (hdist ρ hρ))) hg
  · rw [hlog]
    unfold lossConstant
    have hcount' := mul_le_mul_of_nonneg_left hcount (by norm_num : (0 : ℝ) ≤ 2)
    rw [hK] at hcount'
    linarith

/-- Conditional common-height estimate for the explicit product. The sole
extra analytic premise is a polynomial **upper** bound on radius-six
circles about `2 + (H + 1/2)i`, for all sufficiently large real `H`.
Neither the conclusion nor the premise uses an identification with a
Hecke character. The same height works for the entire closed segment. -/
public theorem qSqrtNegFiveDirichletProduct_good_heights_of_circle_growth
    {C₀ H₀ : ℝ} {k : ℕ} (hC : 1 ≤ C₀) (hH₀ : 1 ≤ H₀)
    (hgrowth : ∀ H ≥ H₀, ∀ z ∈ sphere (2 + ((H + 1 / 2 : ℝ) : ℂ) * I) 6,
      ‖qSqrtNegFiveDirichletProduct z‖ ≤ C₀ * H ^ k) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ H ≥ H₀, ∃ T ∈ Ioo H (H + 1),
      ∀ σ ∈ Icc (-1 / 2 : ℝ) 2,
        let s := (σ : ℂ) + (T : ℂ) * I
        qSqrtNegFiveDirichletProduct s ≠ 0 ∧
          ‖(qSqrtNegFiveDirichletProduct s)⁻¹‖ ≤ C * T ^ A := by
  obtain ⟨b, hb, hanchor⟩ := exists_qSqrtNegFiveDirichletProduct_right_anchor
  let P := -Real.log b + 8 + lossConstant * Real.log (C₀ / b)
  let A := (lossConstant + 1) * ((k : ℝ) + 1)
  have hK := lossConstant_nonneg
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨Real.exp P, A, Real.exp_pos _, hA, fun H hH ↦ ?_⟩
  let c : ℂ := 2 + ((H + 1 / 2 : ℝ) : ℂ) * I
  let f := qSqrtNegFiveDirichletProduct
  let M := C₀ * H ^ k
  have hbc : b ≤ ‖f c‖ := hanchor (H + 1 / 2)
  have hfc : 0 < ‖f c‖ := hb.trans_le hbc
  have hf : AnalyticOnNhd ℂ f univ :=
    fun z _ ↦ differentiable_qSqrtNegFiveDirichletProduct.analyticAt z
  have hH₁ := hH₀.trans hH
  have hHp : 0 < H := by linarith
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hH₁)
  obtain ⟨T, hT, hgood⟩ := exists_one_goodHeight hf (c := c) rfl
    (norm_pos_iff.mp hfc) hM (hgrowth H hH)
  refine ⟨T, hT, fun σ hσ ↦ ?_⟩
  let z := (σ : ℂ) + (T : ℂ) * I
  obtain ⟨hn, hl⟩ := hgood σ hσ
  change f z ≠ 0 ∧ ‖(f z)⁻¹‖ ≤ _
  refine ⟨hn, ?_⟩
  have hMpos : 0 < M := by linarith
  have hCp : 0 < C₀ := by linarith
  have hTpos : 0 < T := hHp.trans hT.1
  have hlogc := Real.log_le_log hb hbc
  have hlogM := Real.log_le_log (div_pos hMpos hfc)
    (div_le_div_of_nonneg_left hMpos.le hb hbc)
  have hlogMT : Real.log (M / b) = Real.log (C₀ / b) + (k : ℝ) * Real.log H := by
    rw [show M / b = (C₀ / b) * H ^ k by dsimp [M]; ring,
      Real.log_mul (div_ne_zero hCp.ne' hb.ne') (pow_ne_zero _ hHp.ne'), Real.log_pow]
  have hlogH : Real.log H ≤ Real.log T := Real.log_le_log hHp hT.1.le
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (hH₁.trans hT.1.le)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hAk : lossConstant * (k : ℝ) ≤ A := by dsimp [A]; nlinarith
  have hL : -Real.log ‖f z‖ ≤ P + A * Real.log T := by
    change _ ≤ Real.log ‖f z‖ at hl
    calc
      _ ≤ -Real.log b + 8 + lossConstant * Real.log (M / b) := by
        linarith [mul_le_mul_of_nonneg_left hlogM hK]
      _ = P + (lossConstant * (k : ℝ)) * Real.log H := by rw [hlogMT]; dsimp [P]; ring
      _ ≤ P + (lossConstant * (k : ℝ)) * Real.log T := by gcongr
      _ ≤ P + A * Real.log T := by gcongr
  rw [norm_inv, ← Real.exp_log (norm_pos_iff.mpr hn), ← Real.exp_neg,
    Real.rpow_def_of_pos hTpos, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa only [mul_comm (Real.log T) A] using hL)

end Masullo
