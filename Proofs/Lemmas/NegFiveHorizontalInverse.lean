module

public import Theorems.IdealClassGoodHeights
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Horizontal inverse bound for the discriminant `-20` product

A common good height for the product gives the upper edge. The two characters
have real coefficients, so complex conjugation gives the matching lower edge.
-/

open Complex Set
open scoped ComplexConjugate Topology

namespace Masullo

private theorem dirichletLFunction_conj_of_real {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hreal : ∀ n : ℕ, conj (χ n) = χ n) (s : ℂ) :
    χ.LFunction (conj s) = conj (χ.LFunction s) := by
  let g : ℂ → ℂ := fun z ↦ conj (χ.LFunction (conj z))
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have hg : Differentiable ℂ g := fun z ↦
    differentiableAt_conj_conj_iff.mpr (hL (conj z))
  -- Check the symmetry on the convergent Dirichlet series, then continue it.
  have hright (z : ℂ) (hz : 1 < z.re) : g z = χ.LFunction z := by
    have hcz : 1 < (conj z).re := by simpa only [conj_re] using hz
    dsimp only [g]
    rw [χ.LFunction_eq_LSeries hcz, χ.LFunction_eq_LSeries hz, LSeries, LSeries, conj_tsum]
    apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hreal,
        ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
  have heq : g =ᶠ[𝓝 (2 : ℂ)] χ.LFunction :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))
      hright
  rw [← analyticOnNhd_univ_iff_differentiable] at hg hL
  simpa only [g, conj_conj] using
    congrArg (starRingEnd ℂ) (congrFun (hg.eq_of_eventuallyEq hL heq) s)

private theorem qSqrtNegFiveDirichletProduct_conj (s : ℂ) :
    qSqrtNegFiveDirichletProduct (conj s) = conj (qSqrtNegFiveDirichletProduct s) := by
  have h₄ := dirichletLFunction_conj_of_real dirichletNegFour dirichletNegFour_ne_one
    (fun n ↦ by simp [dirichletNegFour, MulChar.ringHomComp_apply]) s
  have h₅ := dirichletLFunction_conj_of_real dirichletFive dirichletFive_ne_one
    (fun n ↦ by simp [dirichletFive, MulChar.ringHomComp_apply]) s
  rw [qSqrtNegFiveDirichletProduct, qSqrtNegFiveDirichletProduct, h₄, h₅, map_mul]

/-- Arbitrarily high pairs of horizontal edges on which the explicit Dirichlet
product is nonzero and its reciprocal is bounded by a fixed polynomial. -/
public theorem qSqrtNegFiveDirichletProduct_horizontal_inverse :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ R : ℝ, 0 < R → ∃ T : ℝ, R < T ∧
      ∀ w : ℂ, -(1 / 2 : ℝ) ≤ w.re → w.re ≤ 2 → w.im = -T ∨ w.im = T →
        qSqrtNegFiveDirichletProduct w ≠ 0 ∧
          ‖(qSqrtNegFiveDirichletProduct w)⁻¹‖ ≤ C * (1 + ‖w‖) ^ k := by
  obtain ⟨C, A, hC, -, hgood⟩ := qSqrtNegFiveDirichletProduct_good_heights
  let k := ⌈A⌉₊
  have hk : A ≤ (k : ℝ) := Nat.le_ceil A
  refine ⟨C, hC.le, k, fun R _ ↦ ?_⟩
  obtain ⟨T, hT, hseg⟩ := hgood (max 1 R) (le_max_left _ _)
  have hT₁ : 1 ≤ T := (le_max_left _ _).trans hT.1.le
  have hT₀ : 0 ≤ T := zero_le_one.trans hT₁
  have hupper (z : ℂ) (hlo : -(1 / 2 : ℝ) ≤ z.re) (hhi : z.re ≤ 2) (hz : z.im = T) :
      qSqrtNegFiveDirichletProduct z ≠ 0 ∧
        ‖(qSqrtNegFiveDirichletProduct z)⁻¹‖ ≤ C * (1 + ‖z‖) ^ k := by
    have hz' : (z.re : ℂ) + (T : ℂ) * I = z := by rw [← hz, re_add_im]
    obtain ⟨hne, hinv⟩ := hseg z.re ⟨by simpa only [neg_div] using hlo, hhi⟩
    rw [hz'] at hne hinv
    have hTz : T ≤ ‖z‖ := by
      simpa only [hz, abs_of_nonneg hT₀] using abs_im_le_norm z
    refine ⟨hne, hinv.trans (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
    calc
      T ^ A ≤ T ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hT₁ hk
      _ = T ^ k := Real.rpow_natCast T k
      _ ≤ (1 + ‖z‖) ^ k :=
        pow_le_pow_left₀ hT₀ (hTz.trans (le_add_of_nonneg_left zero_le_one)) k
  refine ⟨T, (le_max_right _ _).trans_lt hT.1, fun w hlo hhi hw ↦ ?_⟩
  rcases hw with hw | hw
  · obtain ⟨hne, hinv⟩ := hupper (conj w) (by simpa only [conj_re] using hlo)
      (by simpa only [conj_re] using hhi) (by simp [hw])
    rw [qSqrtNegFiveDirichletProduct_conj] at hne hinv
    exact ⟨fun h ↦ hne (by rw [h, map_zero]),
      by simpa only [norm_inv, norm_conj] using hinv⟩
  · exact hupper w hlo hhi hw

end Masullo
