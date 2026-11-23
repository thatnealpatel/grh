module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# Local separation of distinct exponential rates

Apply `D - r` to an equality on an open set to remove a summand of rate `r`.
Repeating this operation leaves a nonzero multiple of the target exponential.
-/

open Filter Set
open scoped Topology

namespace Masullo

private theorem hasDerivAt_const_mul_exp_mul (c k t : ℝ) :
    HasDerivAt (fun x ↦ c * Real.exp (k * x)) ((c * k) * Real.exp (k * t)) t := by
  simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_comm k] using
    (((hasDerivAt_id t).const_mul k).exp.const_mul c)

/-- A nonzero exponential term cannot agree on a nonempty open set with a
finite sum of terms whose rates all differ from its own. -/
public theorem not_eqOn_exp_finset {ι : Type*} {I : Set ℝ} (hI : IsOpen I) (hne : I.Nonempty)
    (s : Finset ι) (r c : ι → ℝ) {k d : ℝ}
    (hk : ∀ i ∈ s, k ≠ r i) (hd : d ≠ 0) :
    ¬ EqOn (fun x ↦ d * Real.exp (k * x)) (fun x ↦ ∑ i ∈ s, c i * Real.exp (r i * x)) I := by
  classical
  induction s using Finset.induction_on generalizing c d with
  | empty =>
    intro h
    obtain ⟨t, ht⟩ := hne
    exact (mul_ne_zero hd (Real.exp_ne_zero (k * t))) (by simpa using h ht)
  | insert j s hj ih =>
    intro h
    have hjk := hk j (Finset.mem_insert_self j s)
    refine ih (fun i ↦ c i * (r i - r j))
      (fun i hi ↦ hk i (Finset.mem_insert_of_mem hi)) (mul_ne_zero hd (sub_ne_zero.mpr hjk)) ?_
    intro t ht
    have he : (fun x ↦ ∑ i ∈ insert j s, c i * Real.exp (r i * x)) =ᶠ[𝓝 t]
        (fun x ↦ d * Real.exp (k * x)) :=
      (hI.eventually_mem ht).mono fun _ hx ↦ (h hx).symm
    have hder : (d * k) * Real.exp (k * t) =
        ∑ i ∈ insert j s, (c i * r i) * Real.exp (r i * t) :=
      ((hasDerivAt_const_mul_exp_mul d k t).congr_of_eventuallyEq he).unique
        (HasDerivAt.fun_sum fun i _ ↦ hasDerivAt_const_mul_exp_mul (c i) (r i) t)
    have hdiff : (d * (k - r j)) * Real.exp (k * t) =
        ∑ i ∈ insert j s, (c i * (r i - r j)) * Real.exp (r i * t) := calc
      _ = (d * k) * Real.exp (k * t) - r j * (d * Real.exp (k * t)) := by ring
      _ = _ := by
        have ht' : d * Real.exp (k * t) = ∑ i ∈ insert j s, c i * Real.exp (r i * t) := h ht
        rw [hder, ht', Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
    simpa [Finset.sum_insert hj] using hdiff

end Masullo
