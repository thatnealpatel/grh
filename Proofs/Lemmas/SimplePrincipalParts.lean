module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Separation.Basic

/-! Analytic removal of finitely many simple principal parts. -/

open Filter Set
open scoped Topology

namespace Masullo

private theorem analyticAt_simpleParts {Z : Finset ℂ} {k : ℂ → ℂ} {z : ℂ} (hz : z ∉ Z) :
    AnalyticAt ℂ (fun w ↦ ∑ q ∈ Z, k q * (w - q)⁻¹) z := by
  apply Finset.analyticAt_fun_sum
  intro q hq
  exact analyticAt_const.mul <| (analyticAt_id.sub analyticAt_const).inv
    (sub_ne_zero.mpr (show z ≠ q from fun h ↦ hz (h.symm ▸ hq)))

/-- Off a finite set of simple poles, subtract the kernels. At a pole, use the
value of its regular term minus the kernels at the other poles. -/
public theorem exists_analyticAt_remainder_of_simpleParts {K : Set ℂ} {Z : Finset ℂ}
    {g k : ℂ → ℂ} (hreg : ∀ w ∈ K \ (Z : Set ℂ), AnalyticAt ℂ g w)
    (hpole : ∀ z ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧
      g =ᶠ[𝓝[≠] z] fun w ↦ k z * (w - z)⁻¹ + H w) :
    ∃ h : ℂ → ℂ, (∀ w ∈ K, AnalyticAt ℂ h w) ∧
      EqOn g (fun w ↦ h w + ∑ q ∈ Z, k q * (w - q)⁻¹) (K \ (Z : Set ℂ)) := by
  classical
  choose H hH using hpole
  let P (Z' : Finset ℂ) (w : ℂ) := ∑ q ∈ Z', k q * (w - q)⁻¹
  let h (w : ℂ) := if hw : w ∈ Z then H w hw w - P (Z.erase w) w else g w - P Z w
  refine ⟨h, ?_, fun w hw ↦ ?_⟩
  · intro z hz
    by_cases hZ : z ∈ Z
    · have hmiss : z ∉ Z.erase z := Finset.notMem_erase _ _
      refine ((hH z hZ).1.sub (analyticAt_simpleParts (k := k) hmiss)).congr ?_
      apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
      · have haway : ∀ᶠ w in 𝓝 z, w ∉ Z.erase z :=
          (Z.erase z).isClosed.isOpen_compl.mem_nhds hmiss
        filter_upwards [(hH z hZ).2, haway.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with w hw hw' hne
        have hwZ : w ∉ Z := by
          intro hmem
          exact hw' (Finset.mem_erase.mpr ⟨hne, hmem⟩)
        change g w = k z * (w - z)⁻¹ + H z hZ w at hw
        have hsum : P Z w = P (Z.erase z) w + k z * (w - z)⁻¹ :=
          (Finset.sum_erase_add Z (fun q ↦ k q * (w - q)⁻¹) hZ).symm
        change H z hZ w - P (Z.erase z) w = h w
        simp only [h, dite_eq_right hwZ, hw, hsum]
        abel
      · simp [h, hZ, P]
    · refine ((hreg z ⟨hz, hZ⟩).sub (analyticAt_simpleParts (k := k) hZ)).congr ?_
      filter_upwards [Z.isClosed.isOpen_compl.mem_nhds hZ] with w hw
      simp [h, P, show w ∉ Z from hw]
  · simp [h, P, show w ∉ Z from hw.2]

end Masullo
