module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries

/-! # Compact-uniform bounds for real Schwartz lattice translates -/

open Asymptotics TopologicalSpace
open scoped SchwartzMap

namespace Masullo

private noncomputable def translateSchwartzMap (b : 𝓢(ℝ, ℂ)) (n : ℤ) : C(ℝ, ℂ) :=
  (⟨b, b.continuous⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ))

private theorem translateSchwartzMap_apply (b : 𝓢(ℝ, ℂ)) (n : ℤ) (x : ℝ) :
    translateSchwartzMap b n x = b (x + n) := rfl

private theorem summable_norm_translateSchwartzMap (b : 𝓢(ℝ, ℂ)) (K : Compacts ℝ) :
    Summable (fun n : ℤ ↦ ‖(translateSchwartzMap b n).restrict K‖) := by
  apply summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
  exact (isBigO_norm_restrict_cocompact ⟨b, b.continuous⟩ (by norm_num : (0 : ℝ) < 2)
    (by simpa only [ContinuousMap.coe_mk, Real.norm_eq_abs] using
      b.isBigO_cocompact_rpow (-2)) K).comp_tendsto
    Int.tendsto_coe_cofinite

public theorem summable_norm_schwartz_add_int (b : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun n : ℤ ↦ ‖b (x + n)‖) := by
  let K : Compacts ℝ := ⟨{x}, isCompact_singleton⟩
  exact (summable_norm_translateSchwartzMap b K).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ by
      simpa only [ContinuousMap.restrict_apply, translateSchwartzMap_apply] using
        ContinuousMap.norm_coe_le_norm ((translateSchwartzMap b n).restrict K)
          (⟨x, Set.mem_singleton x⟩ : K))

public theorem continuous_tsum_schwartz_add_int (b : 𝓢(ℝ, ℂ)) :
    Continuous (fun x : ℝ ↦ ∑' n : ℤ, b (x + n)) := by
  have h := ContinuousMap.summable_of_locally_summable_norm (summable_norm_translateSchwartzMap b)
  have he : (fun x : ℝ ↦ ∑' n : ℤ, b (x + n)) = ⇑(∑' n : ℤ, translateSchwartzMap b n) :=
    funext fun x ↦ by simpa only [translateSchwartzMap_apply] using (ContinuousMap.tsum_apply h x)
  rw [he]
  exact map_continuous _

end Masullo
