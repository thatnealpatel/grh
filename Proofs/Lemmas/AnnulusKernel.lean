module

public import Lemmas.WindowKernel
/-! # Remove the auxiliary period and input window

The two support bounds here are for the original real-line test and cutoff.
Neither the level projection nor its image needs to be compactly supported. -/

open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace

namespace Masullo.OperatorTrace
noncomputable section

variable {L R : ℝ} [Fact (0 < L)] {μ : Measure ℝ}
local notation "H" => Lp ℂ 2 μ

/-- Identify the right-composed operator with real-line convolution, when the
window cancels the weight and the periodic test agrees on all differences. -/
public theorem annulus_kernel_ae (p φ : ℝ → ℂ) (hp : MemLp p 2 μ)
    (hpR : Function.support p ⊆ Icc (-R) R) (hφR : Function.support φ ⊆ Icc (-R) R)
    (q : H) (hq : ∀ F : ℝ → ℂ, (∫ y, F y * star (q y) ∂μ) = ∫ y in Icc (-(2*R)) (2*R), F y)
    (f : C(AddCircle L, ℂ)) (hf : Summable (fourierCoeff f))
    (hmatch : ∀ t : ℝ, |t| ≤ 3*R → f (t : AddCircle L) = φ t)
    (Q : H →L[ℂ] H) (z : H) :
    (windowKernel (hp.toLp p) q f (Q z) : ℝ → ℂ) =ᵐ[μ]
      fun x => p x * ∫ y, φ (x-y) * (Q z) y := by
  filter_upwards [windowKernel_ae (hp.toLp p) q f hf (Q z), hp.coeFn_toLp] with x hx hpx
  rw [hx, hpx]
  by_cases hx0 : p x = 0
  · simp [hx0]
  have hxR := hpR (show x ∈ Function.support p from hx0)
  change -R ≤ x ∧ x ≤ R at hxR
  congr 1
  simp_rw [RCLike.inner_apply, ← mul_assoc]
  refine (hq (fun y => f ((x : AddCircle L) - (y : AddCircle L)) * (Q z) y)).trans ?_
  calc
    _ = ∫ y in Icc (-(2*R)) (2*R), φ (x-y) * (Q z) y := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro y hy
      change f ((x : AddCircle L) - (y : AddCircle L)) * _ = _
      rw [← AddCircle.coe_sub, hmatch]
      exact abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      suffices φ (x-y) = 0 by simp [this]
      by_contra hne
      have ht := hφR (show x-y ∈ Function.support φ from hne)
      exact hy ⟨by linarith [ht.2], by linarith [ht.1]⟩

end
end Masullo.OperatorTrace
