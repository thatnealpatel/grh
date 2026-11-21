module

public import Lemmas.ZetaZeroOrders
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Meromorphic orders of completed zeta

Clearing the two poles via `entireZeta` transfers orders off 0 and 1
and reduces each pole to the vanishing of a linear factor.
-/

open Filter Set
open scoped Topology

namespace Masullo

private theorem completedZeta_eq_quotient {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedRiemannZeta s = entireZeta s / (s * (s - 1)) := by
  rw [completedRiemannZeta_eq, entireZeta]
  have hs1 := sub_ne_zero.mpr h1
  have h1s := sub_ne_zero.mpr h1.symm
  field_simp
  ring

public theorem meromorphicAt_completedZeta (z : ℂ) :
    MeromorphicAt completedRiemannZeta z := by
  rw [show completedRiemannZeta = (fun s ↦ completedRiemannZeta₀ s - 1 / s - 1 / (1 - s))
    from funext completedRiemannZeta_eq]
  exact (differentiable_completedZeta₀.analyticAt z).meromorphicAt.sub
    (by fun_prop) |>.sub (by fun_prop)

public theorem order_completedZeta_away {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    meromorphicOrderAt completedRiemannZeta z = meromorphicOrderAt entireZeta z := by
  let q : ℂ → ℂ := fun s ↦ s * (s - 1)
  have hq : AnalyticAt ℂ q z := by dsimp [q]; fun_prop
  have hq0 : q z ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
  have heq : entireZeta =ᶠ[𝓝[≠] z] q * completedRiemannZeta := by
    filter_upwards [(eventually_ne_nhds h0).filter_mono nhdsWithin_le_nhds,
      (eventually_ne_nhds h1).filter_mono nhdsWithin_le_nhds] with s hs0 hs1
    change entireZeta s = q s * completedRiemannZeta s
    rw [completedZeta_eq_quotient hs0 hs1, mul_comm]
    exact (div_mul_cancel₀ _ (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))).symm
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul_of_ne_zero hq hq0]

public theorem order_completedZeta_atPole {z : ℂ} (hz : z = 0 ∨ z = 1) :
    meromorphicOrderAt completedRiemannZeta z = ((-1 : ℤ) : WithTop ℤ) := by
  have hq : AnalyticAt ℂ (fun s : ℂ ↦ s * (s - 1)) z := by fun_prop
  have he : AnalyticAt ℂ entireZeta z := entireZeta_analyticOnNhd z (mem_univ z)
  have he0 : entireZeta z ≠ 0 := by rcases hz with rfl | rfl <;> simp [entireZeta]
  have hq_order : meromorphicOrderAt (fun s : ℂ ↦ s * (s - 1)) z = 1 := by
    rcases hz with rfl | rfl
    · have h : AnalyticAt ℂ (· - (1 : ℂ)) 0 := by fun_prop
      rw [show (fun s : ℂ ↦ s * (s - 1)) = (· - (1 : ℂ)) * id from
        funext fun s ↦ mul_comm s (s - 1)]
      rw [meromorphicOrderAt_mul_of_ne_zero h (by simp), meromorphicOrderAt_id]
    · have h : AnalyticAt ℂ (id : ℂ → ℂ) 1 := analyticAt_id
      change meromorphicOrderAt (id * (· - (1 : ℂ))) 1 = 1
      rw [meromorphicOrderAt_mul_of_ne_zero h (by simp), meromorphicOrderAt_id_sub_const]
  have heq : completedRiemannZeta =ᶠ[𝓝[≠] z] fun s ↦ entireZeta s / (s * (s - 1)) := by
    rcases hz with rfl | rfl
    · filter_upwards [self_mem_nhdsWithin, (eventually_ne_nhds (show (0 : ℂ) ≠ 1 by simp)).filter_mono
        nhdsWithin_le_nhds] with s hs0 hs1 using completedZeta_eq_quotient hs0 hs1
    · filter_upwards [(eventually_ne_nhds (show (1 : ℂ) ≠ 0 by simp)).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs0 hs1 using completedZeta_eq_quotient hs0 hs1
  have he_ord : meromorphicOrderAt entireZeta z = 0 := by
    rw [he.meromorphicOrderAt_eq, he.analyticOrderAt_eq_zero.mpr he0]
    rfl
  rw [meromorphicOrderAt_congr heq]
  change meromorphicOrderAt (entireZeta / (fun s : ℂ ↦ s * (s - 1))) z = _
  rw [meromorphicOrderAt_div he.meromorphicAt hq.meromorphicAt, he_ord, hq_order]
  simp

end Masullo
