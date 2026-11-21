module

public import Theorems.RationalAdeleLFFourierInversion
public import Theorems.RationalAdeleL1L2Fourier
import Lemmas.RationalAdeleFourierFubini

/-! # Inversion against rational adelic Schwartz tests

This is a weak form of (D.1.1.11), p. 747, for integrable inputs with
integrable transforms. For arbitrary representatives, the manuscript's
pointwise statement must be repaired. Testing first avoids assuming
pointwise equality and uses only the normalized Schwartz inverse and
bilinear transposition of the two Fourier kernels.
-/

open NumberField MeasureTheory

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => rationalAdeleAddHaar
local notation "F" => rationalAdeleFourier

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- For `f` and `F f` in `L¹`, the reflected double Fourier integral and
`f` give the same bilinear pairing with every rational adelic Schwartz
function. Both pairings are absolutely integrable. -/
public theorem rationalAdeleFourier_test_inversion {f : A → ℂ}
    (hf : Integrable f μA) (hFf : Integrable (F f) μA) (g : RationalAdeleSchwartzLF) :
    Integrable (fun x ↦ F (F f) (-x) * g.toUnion.val x) μA ∧
      Integrable (fun x ↦ f x * g.toUnion.val x) μA ∧
      (∫ x, F (F f) (-x) * g.toUnion.val x ∂μA) = ∫ x, f x * g.toUnion.val x ∂μA := by
  let h := rationalAdeleLFFourierEquiv.symm g
  have h₁ (x : A) : F g.toUnion.val (-x) = h.toUnion.val x :=
    (rationalAdeleLFFourierEquiv_symm_apply g x).symm
  have h₂ (x : A) : F h.toUnion.val x = g.toUnion.val x := by
    rw [← rationalAdeleLFFourierEquiv_apply, rationalAdeleLFFourierEquiv.apply_symm_apply]
  obtain ⟨hu, -, e₁⟩ := rationalAdeleFourier_transpose hFf (integrable_rationalAdeleSchwartzLF g) (-1)
  obtain ⟨-, hf', e₂⟩ := rationalAdeleFourier_transpose hf (integrable_rationalAdeleSchwartzLF h) 1
  simp only [neg_one_mul, h₁] at hu e₁
  simp only [one_mul, h₂] at hf' e₂
  exact ⟨hu, hf', e₁.trans e₂⟩

end Masullo
