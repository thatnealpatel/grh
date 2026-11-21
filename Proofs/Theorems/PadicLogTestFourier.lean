module

public import Theorems.PadicLogBallFourier
public import Mathlib.Topology.LocallyConstant.Basic

import Lemmas.PadicTestDecomposition
import Lemmas.PadicLogPair

/-!
# The rational finite logarithmic Fourier pairing on tests avoiding zero

In (B.4.3.5), pp. 617–618, Masullo uses dilation covariance and uniqueness
of the invariant functional on multiplicative tests, calibrating on the
unit indicator. Instead, `padicTranslatedBall_log_fourier` computes
arbitrary off-zero ball pairings directly, and
`padicTest_eq_sum_closedBalls` reduces the test to these indicators.
This replaces the covariance and uniqueness argument for this restriction
only. The Fourier integral uses the conjugate character. Reversing the
Fourier sign reflects frequency and leaves the pairing unchanged, since
`J` is even and additive Haar is invariant under negation. The result
uses additive density; its identification with unit-normalized
multiplicative Haar in (A.3.2.3), p. 560, is separate. These locators
follow the pinned text extraction.
-/

open scoped Padic BigOperators
open Set Metric MeasureTheory

namespace Masullo

variable (p : ℕ) [Fact p.Prime]

/-- Rational additive-density form of (B.4.3.5). Both sides are absolutely
integrable. Local constancy makes `u 0 = 0` a neighborhood vanishing condition. -/
public theorem padicTest_log_fourier_off_zero (u : ℚ_[p] → ℂ) (hu : IsLocallyConstant u)
    (hc : HasCompactSupport u) (h₀ : u 0 = 0) :
    let F := fun ξ : ℚ_[p] ↦ (↑(Real.log ‖ξ‖ / Real.log (p : ℝ)) : ℂ) *
      (∫ x, u x * star (padicStdAddChar p (x * ξ)) ∂padicAddHaar p)
    let G := fun x : ℚ_[p] ↦ u x / (↑‖x‖ : ℂ)
    Integrable F (padicAddHaar p) ∧ Integrable G (padicAddHaar p) ∧
      (∫ ξ, F ξ ∂padicAddHaar p) = -((↑(1 - (p : ℝ)⁻¹) : ℂ)⁻¹) *
        ∫ x, G x ∂padicAddHaar p := by
  classical
  let μ := padicAddHaar p
  let J := fun ξ : ℚ_[p] ↦ (↑(Real.log ‖ξ‖ / Real.log (p : ℝ)) : ℂ)
  let K := fun ξ x : ℚ_[p] ↦ star (padicStdAddChar p (x * ξ))
  let d := -((↑(1 - (p : ℝ)⁻¹) : ℂ)⁻¹)
  obtain ⟨n, s, a, ha, hsum⟩ := padicTest_eq_sum_closedBalls p hu hc h₀
  let r := ((p : ℝ)⁻¹) ^ n
  let S (i : s) := closedBall (a i) r
  let c (i : s) := u (a i)
  let F (i : s) (ξ : ℚ_[p]) := c i * (J ξ * ∫ x in S i, K ξ x ∂μ)
  let G (i : s) := fun x ↦ c i * (S i).indicator (fun y ↦ (↑‖y‖ : ℂ)⁻¹) x
  have hF (i : s) : Integrable (F i) μ := (padicClosedBall_log_pair p n (a i) (ha i)).1.const_mul _
  have hG (i : s) : Integrable (G i) μ := (padicClosedBall_log_pair p n (a i) (ha i)).2.1.const_mul _
  have hpair (i : s) : (∫ ξ, F i ξ ∂μ) = d * ∫ x, G i x ∂μ := by
    simp only [F, G, integral_const_mul]
    rw [(padicClosedBall_log_pair p n (a i) (ha i)).2.2]
    exact mul_left_comm _ _ _
  -- Fourier transformation commutes with this finite spatial sum.
  have hf (ξ : ℚ_[p]) : J ξ * (∫ x, u x * K ξ x ∂μ) = ∑ i : s, F i ξ := by
    have he : (fun x ↦ u x * K ξ x) =
        fun x ↦ ∑ i : s, (S i).indicator (fun y ↦ c i * K ξ y) x := by
      funext x
      rw [show u x = ∑ i : s, (S i).indicator (fun _ ↦ c i) x from congrFun hsum x,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x ∈ S i <;> simp [Set.indicator, hi]
    have hint (i : s) : Integrable ((S i).indicator (fun x ↦ c i * K ξ x)) μ :=
      (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
        ((integrableOn_padicClosedBall_char p r (a i) ξ).const_mul _)
    rw [he, integral_finsetSum _ (fun i _ ↦ hint i), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator isClosed_closedBall.measurableSet, integral_const_mul]
    exact mul_left_comm _ _ _
  have hg (x : ℚ_[p]) : u x / (↑‖x‖ : ℂ) = ∑ i : s, G i x := by
    rw [show u x = ∑ i : s, (S i).indicator (fun _ ↦ c i) x from congrFun hsum x,
      div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x ∈ S i <;> simp [G, Set.indicator, hi]
  change Integrable (fun ξ ↦ J ξ * ∫ x, u x * K ξ x ∂μ) μ ∧
    Integrable (fun x ↦ u x / (↑‖x‖ : ℂ)) μ ∧
    (∫ ξ, J ξ * ∫ x, u x * K ξ x ∂μ ∂μ) = d * ∫ x, u x / (↑‖x‖ : ℂ) ∂μ
  simp_rw [hf, hg]
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hF i), integrable_finsetSum _ (fun i _ ↦ hG i), ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hF i), integral_finsetSum _ (fun i _ ↦ hG i), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ hpair i)

end Masullo
