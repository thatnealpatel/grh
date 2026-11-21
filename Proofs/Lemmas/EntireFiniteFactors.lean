module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions

/-! Removing finitely many ordinary zero factors from an entire function. -/

open Filter Set
open scoped Topology

namespace Masullo

/-- Removing the exact orders at finitely many distinct points gives an entire
quotient that is nonzero at all the removed points. The product identity holds
at the removed points as well. -/
public theorem entire_extract_finset_factors {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (A : Finset ℂ) (m : ℂ → ℕ)
    (hm : ∀ a ∈ A, analyticOrderAt f a = (m a : ℕ∞)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g univ ∧ (∀ a ∈ A, g a ≠ 0) ∧
      ∀ z, f z = (∏ a ∈ A, (z - a) ^ m a) * g z := by
  classical
  choose u hu hu₀ hlocal using fun (a : ℂ) (ha : a ∈ A) ↦
    ((hf a trivial).analyticOrderAt_eq_natCast.mp (hm a ha))
  let P (z : ℂ) := ∏ b ∈ A, (z - b) ^ m b
  let Q (a z : ℂ) := ∏ b ∈ A.erase a, (z - b) ^ m b
  have hP (a : ℂ) (ha : a ∈ A) (z : ℂ) :
      P z = (z - a) ^ m a * Q a z := by
    exact (Finset.mul_prod_erase A _ ha).symm
  have hP₀ (z : ℂ) (hz : z ∉ A) : P z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b hb ↦
      pow_ne_zero _ (sub_ne_zero.mpr (ne_of_mem_of_not_mem hb hz).symm)
  have hQ₀ (a : ℂ) : Q a a ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun b hb ↦
      pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm)
  let g (z : ℂ) := if hz : z ∈ A then u z hz z / Q z z else f z / P z
  have hg_eq (a : ℂ) (ha : a ∈ A) : g =ᶠ[𝓝 a] fun z ↦ u a ha z / Q a z := by
    have he : ∀ᶠ z in 𝓝 a, z ∉ (↑(A.erase a) : Set ℂ) :=
      (A.erase a).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [he, hlocal a ha] with z hz hfac
    by_cases h : z = a
    · subst z
      simp [g, ha]
    · have hz' : z ∉ A := fun hzA ↦ hz (Finset.mem_erase.mpr ⟨h, hzA⟩)
      have hn := pow_ne_zero (m a) (sub_ne_zero.mpr h)
      simp only [g, dite_eq_right hz', hP a ha, hfac, smul_eq_mul, mul_div_mul_left _ _ hn]
  refine ⟨g, ?_, fun a ha ↦ ?_, fun z ↦ ?_⟩
  · intro a _
    by_cases ha : a ∈ A
    · have hQ : AnalyticAt ℂ (Q a) a :=
        Finset.analyticAt_fun_prod _ fun b _ ↦ (analyticAt_id.sub analyticAt_const).pow (m b)
      exact ((hu a ha).div hQ (hQ₀ a)).congr (hg_eq a ha).symm
    · have hPa : AnalyticAt ℂ P a :=
        Finset.analyticAt_fun_prod _ fun b _ ↦ (analyticAt_id.sub analyticAt_const).pow (m b)
      apply ((hf a trivial).div hPa (hP₀ a ha)).congr
      filter_upwards [A.finite_toSet.isClosed.isOpen_compl.mem_nhds ha] with z hz
      simp [g, show z ∉ A from hz]
  · simpa [g, ha] using div_ne_zero (hu₀ a ha) (hQ₀ a)
  · change f z = P z * g z
    by_cases hz : z ∈ A
    · rw [hP z hz]
      simp only [g, dite_eq_left hz]
      rw [mul_assoc, mul_div_cancel₀ _ (hQ₀ z)]
      have h : f =ᶠ[𝓝 z] fun w ↦ (w - z) ^ m z • u z hz w := hlocal z hz
      exact h.eq_of_nhds.trans (smul_eq_mul _ _)
    · simp only [g, dite_eq_right hz, mul_div_cancel₀ _ (hP₀ z hz)]

end Masullo
