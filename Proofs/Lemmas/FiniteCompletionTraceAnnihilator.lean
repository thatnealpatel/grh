module

public import Lemmas.FiniteCompletionCanonicalTraceDual
public import Theorems.PadicStandardCharacter

/-! # The annihilator of the local integer ring under the trace character -/

open IsDedekindDomain NumberField
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "p" => finiteCompletionBasePrime v
local notation "R" => ℤ_[p]
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K

/-- The trace character is trivial on all integral multiples of `x` exactly when
`x` belongs to the local trace dual. -/
public theorem finiteCompletion_traceChar_trivial_iff (x : F) :
    (∀ y : O, padicStdAddChar p (Algebra.trace ℚ_[p] F (x * (y : F))) = 1) ↔
      x ∈ Submodule.traceDual R ℚ_[p] (1 : Submodule O F) := by
  rw [Submodule.mem_traceDual]
  simp only [padicStdAddChar_eq_one_iff, Submodule.mem_one, forall_exists_index,
    forall_apply_eq_imp_iff, Algebra.traceForm_apply]
  apply forall_congr'
  intro y
  exact ⟨fun h ↦ ⟨⟨_, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.property⟩

end Masullo
