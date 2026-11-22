module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace Masullo

open Classical in
/-- A character's conjugate averages to zero on a measurable subgroup unless
its restriction is trivial, in which case the integral is the subgroup's real measure. -/
public theorem addSubgroup_integral_star_char {G : Type*} [AddGroup G]
    [MeasurableSpace G] [MeasurableAdd G] (S : AddSubgroup G)
    (hS : MeasurableSet (S : Set G)) (μ : Measure G) [μ.IsAddLeftInvariant]
    (χ : G → ℂ) (hadd : ∀ a b, χ (a + b) = χ a * χ b) :
    (∫ y in (S : Set G), star (χ y) ∂μ) =
      if (∀ y ∈ S, χ y = 1) then (μ.real (S : Set G) : ℂ) else 0 := by
  classical
  split_ifs with h
  · calc
      _ = ∫ _ in (S : Set G), (1 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hS
        intro y hy
        simp [h y hy]
      _ = _ := by simp [Complex.real_smul]
  · push Not at h
    obtain ⟨a, ha, hne⟩ := h
    let f := (S : Set G).indicator (fun y => star (χ y))
    have translate (y : G) : f (a + y) = star (χ a) * f y := by
      by_cases hy : y ∈ S
      · simp [f, Set.indicator_of_mem, hy, S.add_mem ha hy, hadd]
      · have hnot : a + y ∉ S := fun hay => hy ((S.add_mem_cancel_left ha).mp hay)
        simp [f, Set.indicator_of_notMem, hy, hnot]
    rw [← integral_indicator hS]
    change (∫ y, f y ∂μ) = 0
    by_contra hI
    have heq := integral_add_left_eq_self (μ := μ) f a
    simp_rw [translate, integral_const_mul] at heq
    exact hne (by simpa using congrArg star ((mul_eq_right₀ hI).mp heq))

end Masullo
