module

public import Lemmas.CompactSmoothMoments
public import Lemmas.LocalExponentialSum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Scalar separation on a short positive log interval

A real smooth interior test annihilates both polar moments and the scalar
multiplier moment without annihilating the weighted projection moment.
This is only a scalar result: It does not identify either moment with a
trace of a global operator.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- On every nonempty open test domain inside `(0, log 2)`, the two polar
weights and `J` can be annihilated without annihilating `Uβ` for `0 < β < 1`.
All four products are integrable for Lebesgue measure on the whole real line. -/
public theorem exists_smooth_test_trace_scalar_separation {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {I : Set ℝ} (hI : IsOpen I) (hne : I.Nonempty) (hpos : I ⊆ Ioo 0 (Real.log 2)) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ I ∧
      (Integrable (fun t ↦ f t * Real.exp (t / 2)) ∧ (∫ t, f t * Real.exp (t / 2)) = 0) ∧
      (Integrable (fun t ↦ f t * Real.exp (-t / 2)) ∧ (∫ t, f t * Real.exp (-t / 2)) = 0) ∧
      (Integrable (fun t ↦ f t * (Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))) ∧
        (∫ t, f t * (Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))) = 0) ∧
      (Integrable (fun t ↦ f t * (Real.exp ((β - 5 / 2) * t) / (1 - Real.exp (-2 * t)))) ∧
        (∫ t, f t * (Real.exp ((β - 5 / 2) * t) / (1 - Real.exp (-2 * t)))) ≠ 0) := by
  let D (t : ℝ) := 1 - Real.exp (-2 * t)
  let w : Fin 3 → ℝ → ℝ :=
    ![fun t ↦ Real.exp (t / 2), fun t ↦ Real.exp (-t / 2), fun t ↦ Real.exp (-t / 2) / D t]
  let u (t : ℝ) := Real.exp ((β - 5 / 2) * t) / D t
  have hd (t : ℝ) (ht : t ∈ I) : D t ≠ 0 := by
    have ht0 := (hpos ht).1
    exact ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hu : ContinuousOn u I := by
    exact (show Continuous (fun t : ℝ ↦ Real.exp ((β - 5 / 2) * t)) by fun_prop).continuousOn.div
      hD.continuousOn hd
  have hw (i : Fin 3) : ContinuousOn (w i) I := by
    fin_cases i
    · exact (show Continuous (fun t : ℝ ↦ Real.exp (t / 2)) by fun_prop).continuousOn
    · exact (show Continuous (fun t : ℝ ↦ Real.exp (-t / 2)) by fun_prop).continuousOn
    · exact (show Continuous (fun t : ℝ ↦ Real.exp (-t / 2)) by fun_prop).continuousOn.div
        hD.continuousOn hd
  suffices hex : ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ I ∧
      (∀ i, (∫ t, f t * w i t) = 0) ∧ (∫ t, f t * u t) ≠ 0 by
    obtain ⟨f, hf, hfc, hfs, hfw, hfu⟩ := hex
    have hint {g : ℝ → ℝ} (hg : ContinuousOn g I) :=
      integrable_mul_of_tsupport_subset hI hf.continuous hfc hfs hg
    exact ⟨f, hf, hfc, hfs, ⟨hint (hw 0), hfw 0⟩, ⟨hint (hw 1), hfw 1⟩,
      ⟨hint (hw 2), hfw 2⟩, ⟨hint hu, hfu⟩⟩
  by_contra! hnone
  -- The common kernel inclusion would give a linear combination on the test space.
  obtain ⟨c, hc⟩ := compactSmooth_moment_relation hI hw hu hnone
  let v (t : ℝ) := ∑ i, c i * w i t
  have hv : ContinuousOn v I :=
    continuousOn_finsetSum Finset.univ fun i _ ↦ (hw i).const_mul (c i)
  -- Testing all smooth bumps makes the linear combination an equality of densities on I.
  have heq : EqOn u v I := by
    apply eqOn_of_compactSmooth_moments_eq hI hu hv
    intro f hf hfc hfs
    rw [hc f hf hfc hfs]
    simp only [v, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ ↦ integrable_mul_of_tsupport_subset hI hf.continuous hfc hfs
      ((hw i).const_mul (c i)))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_left_comm (f _), integral_const_mul]
  -- Clearing the denominator leaves four constraint rates, all distinct from β − 5/2.
  let r : Fin 4 → ℝ := ![1 / 2, -1 / 2, -3 / 2, -5 / 2]
  let q : Fin 4 → ℝ := ![c 0, c 1 + c 2, -c 0, -c 1]
  have hr (i : Fin 4) : β - 5 / 2 ≠ r i := by
    fin_cases i <;> dsimp [r] <;> linarith
  apply not_eqOn_exp_finset hI hne Finset.univ r q (fun i _ ↦ hr i) (one_ne_zero (α := ℝ))
  intro t ht
  have hscale : Real.exp ((β - 5 / 2) * t) = ∑ i, c i * (w i t * D t) := calc
    _ = u t * D t := (div_mul_cancel₀ _ (hd t ht)).symm
    _ = v t * D t := congrArg (· * D t) (heq ht)
    _ = _ := by simp only [v, Finset.sum_mul, mul_assoc]
  have hp : Real.exp (t / 2) * D t = Real.exp ((1 / 2) * t) - Real.exp ((-3 / 2) * t) := by
    dsimp only [D]
    rw [mul_sub, mul_one, ← Real.exp_add, show t / 2 + -2 * t = (-3 / 2) * t by ring,
      show t / 2 = (1 / 2) * t by ring]
  have hm : Real.exp (-t / 2) * D t = Real.exp ((-1 / 2) * t) - Real.exp ((-5 / 2) * t) := by
    dsimp only [D]
    rw [mul_sub, mul_one, ← Real.exp_add, show -t / 2 + -2 * t = (-5 / 2) * t by ring,
      show -t / 2 = (-1 / 2) * t by ring]
  have hj : (Real.exp (-t / 2) / D t) * D t = Real.exp ((-1 / 2) * t) := by
    rw [div_mul_cancel₀ _ (hd t ht), show -t / 2 = (-1 / 2) * t by ring]
  rw [Fin.sum_univ_three] at hscale
  change Real.exp ((β - 5 / 2) * t) = c 0 * (Real.exp (t / 2) * D t) +
    c 1 * (Real.exp (-t / 2) * D t) + c 2 * ((Real.exp (-t / 2) / D t) * D t) at hscale
  rw [hp, hm, hj] at hscale
  simp only [one_mul, Fin.sum_univ_four]
  change Real.exp ((β - 5 / 2) * t) = c 0 * Real.exp ((1 / 2) * t) +
    (c 1 + c 2) * Real.exp ((-1 / 2) * t) + -c 0 * Real.exp ((-3 / 2) * t) +
    -c 1 * Real.exp ((-5 / 2) * t)
  rw [hscale]
  ring

end Masullo
