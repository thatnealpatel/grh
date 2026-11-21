module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Pointwise finite sums of seminorms -/

namespace Masullo

variable {𝕜 V : Type*} [NormedField 𝕜] [AddCommGroup V] [Module 𝕜 V]

private theorem sum_until (p : ℕ → Seminorm 𝕜 V) (x : V) {m : ℕ}
    (h : ∀ n ≥ m, p n x = 0) :
    (∑' n, p n x) = ∑ n ∈ Finset.range m, p n x := by
  apply tsum_eq_sum
  exact fun n hn ↦ h n (Nat.le_of_not_lt (fun hn' ↦ hn (Finset.mem_range.mpr hn')))

/-- A sequence of seminorms that is eventually zero at each point has a
pointwise finite sum, again a seminorm. There need not be a common cutoff. -/
public noncomputable def eventualZeroSeminormSum (p : ℕ → Seminorm 𝕜 V)
    (h : ∀ x, ∃ m, ∀ n ≥ m, p n x = 0) : Seminorm 𝕜 V :=
  Seminorm.of (fun x ↦ ∑' n, p n x)
    (by
      intro x y
      obtain ⟨a, ha⟩ := h x
      obtain ⟨b, hb⟩ := h y
      have hxy (n : ℕ) (hn : max a b ≤ n) : p n (x + y) = 0 := by
        apply le_antisymm _ (apply_nonneg _ _)
        simpa only [ha n ((le_max_left a b).trans hn), hb n ((le_max_right a b).trans hn),
          add_zero] using map_add_le_add (p n) x y
      rw [sum_until p _ hxy, sum_until p x (fun n hn ↦ ha n ((le_max_left a b).trans hn)),
        sum_until p y (fun n hn ↦ hb n ((le_max_right a b).trans hn)), ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun n _ ↦ map_add_le_add (p n) x y)
    (by
      intro c x
      obtain ⟨a, ha⟩ := h x
      have hc (n : ℕ) (hn : a ≤ n) : p n (c • x) = 0 := by
        rw [map_smul_eq_mul, ha n hn, mul_zero]
      rw [sum_until p _ hc, sum_until p x ha, Finset.mul_sum]
      simp only [map_smul_eq_mul])

public theorem eventualZeroSeminormSum_apply (p : ℕ → Seminorm 𝕜 V)
    (h : ∀ x, ∃ m, ∀ n ≥ m, p n x = 0) (x : V) {m : ℕ} (hm : ∀ n ≥ m, p n x = 0) :
    eventualZeroSeminormSum p h x = ∑ n ∈ Finset.range m, p n x :=
  sum_until p x hm

public theorem le_eventualZeroSeminormSum_apply (p : ℕ → Seminorm 𝕜 V)
    (h : ∀ x, ∃ m, ∀ n ≥ m, p n x = 0) (n : ℕ) (x : V) :
    p n x ≤ eventualZeroSeminormSum p h x := by
  obtain ⟨m, hm⟩ := h x
  by_cases hn : n < m
  · rw [eventualZeroSeminormSum_apply p h x hm]
    exact Finset.single_le_sum (fun i _ ↦ apply_nonneg (p i) x) (Finset.mem_range.mpr hn)
  · rw [hm n (Nat.le_of_not_lt hn)]
    exact apply_nonneg _ _

end Masullo
