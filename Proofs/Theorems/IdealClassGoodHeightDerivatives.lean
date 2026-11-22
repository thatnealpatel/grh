module

public import Theorems.IdealClassGoodHeightDisks
import Mathlib.Analysis.Complex.Liouville

/-!
# Reciprocal derivatives at common good heights

For the corrected forward denominator in Masullo, pp. 308–309, §6.3.2,
Cauchy's estimate on the closed good-height disks bounds every reciprocal
jet with the same height and constants.
-/

open Complex Metric Set

namespace Masullo

/-- The constants and height from the full-disk estimate work at every center
of the closed horizontal segment and for every derivative order. -/
public theorem qSqrtNegFiveDirichletProduct_good_height_inv_iteratedDeriv :
    ∃ c C A B : ℝ, 0 < c ∧ 0 < C ∧ 0 < A ∧ 0 < B ∧
      ∀ H ≥ (1 : ℝ), ∃ T ∈ Ioo H (H + 1), ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ m : ℕ,
        ‖iteratedDeriv m (fun z ↦ (qSqrtNegFiveDirichletProduct z)⁻¹)
          ((σ : ℂ) + (T : ℂ) * I)‖ ≤ (m.factorial : ℝ) * C * c ^ (-(m : ℤ)) *
            T ^ (A + B * (m : ℝ)) := by
  obtain ⟨c, C, A, B, hc, hC, hA, hB, hgood⟩ := qSqrtNegFiveDirichletProduct_good_height_disks
  refine ⟨c, C, A, B, hc, hC, hA, hB, fun H hH ↦ ?_⟩
  obtain ⟨T, hT, hdisks⟩ := hgood H hH
  refine ⟨T, hT, fun σ hσ m ↦ ?_⟩
  let s : ℂ := (σ : ℂ) + (T : ℂ) * I
  let r := c * T ^ (-B)
  have hTpos : 0 < T := zero_lt_one.trans (hH.trans_lt hT.1)
  have hr : 0 < r := mul_pos hc (Real.rpow_pos_of_pos hTpos _)
  have hf : DiffContOnCl ℂ (fun z ↦ (qSqrtNegFiveDirichletProduct z)⁻¹) (ball s r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hr.ne']
    exact differentiable_qSqrtNegFiveDirichletProduct.differentiableOn.inv
      (fun z hz ↦ (hdisks σ hσ z (by simpa only [mem_closedBall, dist_eq_norm] using hz)).1)
  have hsphere (z : ℂ) (hz : z ∈ sphere s r) :
      ‖(qSqrtNegFiveDirichletProduct z)⁻¹‖ ≤ C * T ^ A :=
    (hdisks σ hσ z (mem_sphere_iff_norm.mp hz).le).2
  calc
    _ ≤ m.factorial * (C * T ^ A) / r ^ m :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hr hf hsphere
    _ = _ := by
      have hpow : (T ^ B) ^ m = T ^ (B * (m : ℝ)) := by
        rw [Real.rpow_mul hTpos.le, Real.rpow_natCast]
      change _ / (c * T ^ (-B)) ^ m = _
      rw [Real.rpow_neg hTpos.le, mul_pow, inv_pow, div_eq_mul_inv, mul_inv_rev, inv_inv,
        hpow, zpow_neg, zpow_natCast, Real.rpow_add hTpos]
      ring

end Masullo
