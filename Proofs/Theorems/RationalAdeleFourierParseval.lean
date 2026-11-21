module

public import Theorems.RationalAdeleStageFourier
import Lemmas.RationalAdeleCyclicFourier
import Lemmas.RationalAdeleStageNorm

/-! # Parseval for rational adelic Schwartz functions

This is the Schwartz restriction of (D.1.1.9), p. 747, with the same
normalized additive adelic Haar measure on the two copies of the adeles.
It makes no assumption identifying the full Pontryagin dual and does not
assert the `L²` extension (D.1.1.10).
-/

open NumberField MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar

set_option linter.concreteInstances false

private theorem stage_parseval {M : ℕ} (hM : 0 < M) (b : Fin (M ^ 2) → 𝓢(ℝ, ℂ)) :
    (∑ k, ∫ t, ‖rationalAdeleStageFourier M b k t‖ ^ 2) = ∑ j, ∫ t, ‖b j t‖ ^ 2 := by
  have hs (g : 𝓢(ℝ, ℂ)) : Integrable (fun t ↦ ‖g t‖ ^ 2) volume :=
    (g.memLp 2 volume).integrable_norm_pow (by decide)
  calc
    _ = ∫ t, ∑ k, ‖rationalAdeleStageFourier M b k t‖ ^ 2 :=
      (integral_finsetSum _ (fun k _ ↦ hs (rationalAdeleStageFourier M b k))).symm
    _ = ∫ t, ∑ j, ‖𝓕 (b j) t‖ ^ 2 := by simp_rw [rationalAdeleStageFourier_sum_norm_sq hM]
    _ = ∑ j, ∫ t, ‖𝓕 (b j) t‖ ^ 2 := integral_finsetSum _ (fun j _ ↦ hs (𝓕 (b j)))
    _ = _ := Finset.sum_congr rfl fun j _ ↦ SchwartzMap.integral_norm_sq_fourier (b j)

variable [MeasurableSpace A] [BorelSpace A]

/-- Both squared magnitudes are integrable. The normalized Fourier integral
preserves the squared `L²` norm of every rational adelic Schwartz function. -/
public theorem rationalAdeleFourier_parseval (f : RationalAdeleSchwartzLF) :
    let g := rationalAdeleFourier f.toUnion.val
    Integrable (fun x ↦ ‖f.toUnion.val x‖ ^ 2) μA ∧
      Integrable (fun y ↦ ‖g y‖ ^ 2) μA ∧
      (∫ y, ‖g y‖ ^ 2 ∂μA) = ∫ x, ‖f.toUnion.val x‖ ^ 2 ∂μA := by
  dsimp only
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  let b := rationalAdeleLFRead n f
  let hM := rationalAdeleFactorialLevel_pos n
  rw [← rationalAdeleLFAssembly_read n f hn, ← rationalAdeleLFAssembly_fourier n b]
  simp only [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val]
  obtain ⟨hf, hf_eq⟩ := rationalAdeleStage_integrable_integral_norm_sq hM b
  obtain ⟨hg, hg_eq⟩ := rationalAdeleStage_integrable_integral_norm_sq hM
    (rationalAdeleStageFourier (rationalAdeleFactorialLevel n) b)
  exact ⟨hf, hg, by rw [hg_eq, hf_eq, stage_parseval hM]⟩

end Masullo
