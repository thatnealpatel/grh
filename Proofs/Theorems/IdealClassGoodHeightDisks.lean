module

public import Theorems.IdealClassGoodHeights
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville

/-!
# Disks around the common good-height segment

For the corrected omitted denominator in Masullo, pp. 308–309, §6.3.2,
a unit-radius Cauchy estimate controls the change from each segment point.
The radius-six growth estimate leaves room for the full disks, including
the disks centered at the endpoints of the segment.
-/

open Complex Metric Set

namespace Masullo

private theorem norm_product_sub_le_of_circle_bound {a : ℂ} {M : ℝ}
    (hcircle : ∀ z ∈ sphere a 6, ‖qSqrtNegFiveDirichletProduct z‖ ≤ M)
    {s : ℂ} (hs : s ∈ closedBall a 3) {z : ℂ} (hz : z ∈ closedBall s 1) :
    ‖qSqrtNegFiveDirichletProduct z - qSqrtNegFiveDirichletProduct s‖ ≤ M * ‖z - s‖ := by
  have hf := differentiable_qSqrtNegFiveDirichletProduct
  have hbd (u : ℂ) (hu : u ∈ closedBall a 6) : ‖qSqrtNegFiveDirichletProduct u‖ ≤ M := by
    rw [← closure_ball a (by norm_num : (6 : ℝ) ≠ 0)] at hu
    exact norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf.diffContOnCl
      (by simpa only [frontier_ball _ (by norm_num : (6 : ℝ) ≠ 0)] using hcircle) hu
  have hderiv (w : ℂ) (hw : w ∈ closedBall s 1) :
      ‖deriv qSqrtNegFiveDirichletProduct w‖ ≤ M := by
    have hunit (u : ℂ) (hu : u ∈ sphere w 1) : ‖qSqrtNegFiveDirichletProduct u‖ ≤ M := by
      apply hbd u
      rw [mem_closedBall] at hs hw ⊢
      rw [mem_sphere] at hu
      linarith [dist_triangle u w a, dist_triangle w s a]
    simpa only [div_one] using
      norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1)
        hf.diffContOnCl hunit
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun w _ ↦ hf w) hderiv
    (convex_closedBall s 1) (mem_closedBall_self (by norm_num)) hz

/-- One height in each unit interval works for the full closed disks of radius
`c * T ^ (-B)` centered along the good segment. No Hecke identification or
further growth hypothesis is required for this explicit product. -/
public theorem qSqrtNegFiveDirichletProduct_good_height_disks :
    ∃ c C A B : ℝ, 0 < c ∧ 0 < C ∧ 0 < A ∧ 0 < B ∧
      ∀ H ≥ (1 : ℝ), ∃ T ∈ Ioo H (H + 1), ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ z : ℂ,
        ‖z - ((σ : ℂ) + (T : ℂ) * I)‖ ≤ c * T ^ (-B) →
          qSqrtNegFiveDirichletProduct z ≠ 0 ∧
            ‖(qSqrtNegFiveDirichletProduct z)⁻¹‖ ≤ C * T ^ A := by
  obtain ⟨C, A, hC, hA, hgood⟩ := qSqrtNegFiveDirichletProduct_good_heights
  obtain ⟨C₀, hC₀, hgrowth⟩ := qSqrtNegFiveDirichletProduct_circle_growth
  have hC₀pos : 0 < C₀ := by linarith
  let c : ℝ := min 1 (2 * C * C₀)⁻¹
  let B := A + 12
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨c, 2 * C, A, B, hc, by positivity, hA, hB, fun H hH ↦ ?_⟩
  obtain ⟨T, hT, hseg⟩ := hgood H hH
  have hT₁ : 1 ≤ T := hH.trans hT.1.le
  have hTpos : 0 < T := by linarith
  let a : ℂ := 2 + ((H + 1 / 2 : ℝ) : ℂ) * I
  let K := C * T ^ A
  let M := C₀ * T ^ (12 : ℕ)
  let r := c * T ^ (-B)
  have hK : 0 < K := by dsimp [K]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hr : r ≤ 1 := calc
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hT₁ (neg_nonpos.mpr hB.le)) hc.le
    _ ≤ 1 := by rw [mul_one]; exact min_le_left _ _
  -- Multiplying by twice the segment reciprocal bound cancels the height powers.
  have hscale : 2 * K * (M * r) ≤ 1 := by
    have hpow : T ^ A * T ^ (12 : ℕ) = T ^ B := by
      simpa only [B, Nat.cast_ofNat] using (Real.rpow_add_natCast hTpos.ne' A 12).symm
    calc
      _ = (2 * C * C₀ * c) * ((T ^ A * T ^ (12 : ℕ)) * T ^ (-B)) := by
        dsimp [K, M, r]
        ring
      _ = 2 * C * C₀ * c := by
        rw [hpow, Real.rpow_neg hTpos.le, mul_inv_cancel₀ (by positivity), mul_one]
      _ ≤ (2 * C * C₀) * (2 * C * C₀)⁻¹ :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hcircle (u : ℂ) (hu : u ∈ sphere a 6) : ‖qSqrtNegFiveDirichletProduct u‖ ≤ M := by
    exact (hgrowth H hH u hu).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hT.1.le _) hC₀pos.le)
  refine ⟨T, hT, fun σ hσ z hz ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  have hs : s ∈ closedBall a 3 := by
    rw [mem_closedBall, dist_eq_norm]
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    simp [s, a]
    have hre : |σ - 2| ≤ 5 / 2 := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have him : |T - (H + 1 / 2)| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith [hT.1], by linarith [hT.2]⟩
    linarith
  have hz₁ : z ∈ closedBall s 1 := by
    rw [mem_closedBall, dist_eq_norm]
    exact hz.trans hr
  have hmove : ‖qSqrtNegFiveDirichletProduct z - qSqrtNegFiveDirichletProduct s‖ ≤ M * r :=
    (norm_product_sub_le_of_circle_bound hcircle hs hz₁).trans (mul_le_mul_of_nonneg_left hz hM)
  obtain ⟨hsne, hsr⟩ := hseg σ hσ
  have hsn : 0 < ‖qSqrtNegFiveDirichletProduct s‖ := norm_pos_iff.mpr hsne
  have hslow : 1 ≤ K * ‖qSqrtNegFiveDirichletProduct s‖ :=
    (mul_inv_le_iff₀ hsn).mp (by simpa only [one_mul, ← norm_inv] using hsr)
  have htri := norm_add_le (qSqrtNegFiveDirichletProduct z)
    (qSqrtNegFiveDirichletProduct s - qSqrtNegFiveDirichletProduct z)
  rw [add_sub_cancel, norm_sub_rev] at htri
  have hlow : 1 ≤ (2 * K) * ‖qSqrtNegFiveDirichletProduct z‖ := by
    nlinarith [mul_le_mul_of_nonneg_left (htri.trans (add_le_add_right hmove _)) hK.le]
  have hzn : 0 < ‖qSqrtNegFiveDirichletProduct z‖ := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * K by positivity) h
    linarith
  refine ⟨norm_pos_iff.mp hzn, ?_⟩
  rw [norm_inv, ← one_mul (‖qSqrtNegFiveDirichletProduct z‖⁻¹)]
  simpa only [K, mul_assoc] using (mul_inv_le_iff₀ hzn).mpr hlow

end Masullo
