module

public import Props.HeckeContourReflection
public import Lemmas.CompletedDirichletRightLine

/-!
# The conductor term for primitive Dirichlet L-functions

This is a control for (B.4.2.3)–(4), pp. 614–615, with nontrivial
conductor. Mathlib's completion includes the real Gamma factor but
not the conductor power. Its primitive functional equation supplies
that power with exponent `s - 1/2` in Masullo's orientation after
applying it to `χ⁻¹`. The `N` is the conductor because `χ` is primitive.
This is not an identification with a completed idelic Hecke function.
-/

open Complex Filter MeasureTheory
open scoped ContDiff Topology

namespace Masullo

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The corrected (B.4.2.3) with the actual nontrivial Dirichlet conductor.
The inverse character is the dual in Mathlib's functional equation. -/
public theorem completedDirichlet_logDeriv_reflection (hχ : χ.IsPrimitive) (hN : 1 < N)
    {z : ℂ} (hz : χ.completedLFunction z ≠ 0) :
    logDeriv χ.completedLFunction z =
      -logDeriv (χ⁻¹).completedLFunction (1 - z) - (Real.log N : ℂ) := by
  have hn₀ : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hlog : Complex.log (N : ℂ) = (Real.log N : ℂ) := by
    simpa only [ofReal_natCast] using (ofReal_log (show 0 ≤ (N : ℝ) by positivity)).symm
  have hn : N ≠ 1 := ne_of_gt hN
  have hnontrivial : ∀ {ψ : DirichletCharacter ℂ N}, ψ.IsPrimitive → ψ ≠ 1 := by
    intro ψ hψ heq
    exact hn (by simpa [DirichletCharacter.IsPrimitive, heq, DirichletCharacter.conductor_one] using hψ.symm)
  refine completed_logDeriv_reflection (DirichletCharacter.rootNumber_ne_zero hχ.inv)
    ((DirichletCharacter.differentiable_completedLFunction (hnontrivial hχ)) z)
    ((DirichletCharacter.differentiable_completedLFunction (hnontrivial hχ.inv)) (1 - z)) hz ?_
  exact Eventually.of_forall fun s ↦ by
    change (χ⁻¹).completedLFunction (1 - s) =
      DirichletCharacter.rootNumber χ⁻¹ * exp ((Real.log N : ℂ) * (s - 1 / 2)) * χ.completedLFunction s
    rw [hχ.inv.completedLFunction_one_sub, inv_inv, cpow_def_of_ne_zero hn₀, hlog, mul_comm
      (exp (Real.log N * (s - 1 / 2))) (DirichletCharacter.rootNumber χ⁻¹)]

/-- Reflect the tested left line for a primitive Dirichlet character.
Both line integrability estimates follow from the test hypotheses. -/
public theorem completedDirichlet_reflect_left_integral (hχ : χ.IsPrimitive) (hN : 1 < N)
    {a : ℝ} (ha : 1 < a) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let L := fun t : ℝ ↦
      let z := ((1 - a : ℝ) : ℂ) + (t : ℂ) * I
      compactLogMellin g z * logDeriv χ.completedLFunction z
    let R := fun t : ℝ ↦
      let s := (a : ℂ) + (t : ℂ) * I
      compactLogMellin g (1 - s) * logDeriv (χ⁻¹).completedLFunction s
    Integrable L ∧ (∫ t, L t) / (2 * (Real.pi : ℂ)) =
      -((∫ t, R t) / (2 * (Real.pi : ℂ))) - (Real.log N : ℂ) * g 0 := by
  refine completed_reflect_left_integral a hg hc (fun t ↦ ?_)
    (integrable_compactLogMellin_completedDirichlet_reflected χ⁻¹ hg hc ha)
  let z := ((1 - a : ℝ) : ℂ) + (t : ℂ) * I
  have hz : 1 < (1 - z).re := by simp [z, sub_re, mul_re, ha]
  have hG := (χ⁻¹).completedLFunction_ne_zero_of_one_le_re
    (.inr (fun h ↦ by rw [h, one_re] at hz; exact (lt_irrefl 1) hz)) hz.le
  have hef := hχ.completedLFunction_one_sub (1 - z)
  rw [sub_sub_cancel] at hef
  apply completedDirichlet_logDeriv_reflection hχ hN
  rw [hef]
  exact mul_ne_zero
    (mul_ne_zero (cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr (NeZero.ne N))))
      (DirichletCharacter.rootNumber_ne_zero hχ)) hG

end Masullo
