module

public import Lemmas.ArchimedeanAdeleTrace
public import Theorems.FiniteAdeleTraceCharacter

/-! # The trace character on the adeles of a number field

Masullo's trace pullback (A.3.1.7), PDF p. 558, and Example A.3.1.5, p. 557,
supply the trace and the positive phase at infinity. The finite factors are
conjugated relative to the positive local trace phases of Example A.3.1.10,
p. 558. The checked finite diagonal identity shows why the conjugation is
needed: The finite product cancels the positive Archimedean phase on `K`.
Thus the conjugated global kernel in (2.2.4.32), p. 92, has negative sign at
infinity and positive sign at finite places. This module constructs the
character, not the factorization of the global integral.
Source reading: Provisional, pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain NumberField

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K

/-- The continuous trace pairing character on the actual adelic ring:
positive at infinity and conjugated at finite places. -/
@[expose] public noncomputable def numberFieldAdeleAddChar : AddChar A ℂ where
  toFun z := numberFieldInfiniteAdeleAddChar K z.1 * numberFieldFiniteAdeleAddChar z.2
  map_zero_eq_one' := by
    change numberFieldInfiniteAdeleAddChar K 0 * numberFieldFiniteAdeleAddChar 0 = 1
    simp
  map_add_eq_mul' x y := by
    change numberFieldInfiniteAdeleAddChar K (x.1 + y.1) *
      numberFieldFiniteAdeleAddChar (x.2 + y.2) = _
    simp only [AddChar.map_add_eq_mul]
    ac_rfl

/-- Continuity uses the actual restricted-product topology in the finite factor. -/
public theorem continuous_numberFieldAdeleAddChar :
    Continuous (numberFieldAdeleAddChar : A → ℂ) :=
  ((continuous_numberFieldInfiniteAdeleAddChar K).comp continuous_fst).mul
    (continuous_numberFieldFiniteAdeleAddChar.comp continuous_snd)

public theorem norm_numberFieldAdeleAddChar (z : A) : ‖numberFieldAdeleAddChar z‖ = 1 := by
  change ‖numberFieldInfiniteAdeleAddChar K z.1 * numberFieldFiniteAdeleAddChar z.2‖ = 1
  rw [norm_mul, norm_numberFieldInfiniteAdeleAddChar, norm_numberFieldFiniteAdeleAddChar, mul_one]

/-- The restricted-product character is trivial on every diagonal field element. -/
public theorem numberFieldAdeleAddChar_diagonal (x : K) :
    numberFieldAdeleAddChar (algebraMap K A x) = 1 := by
  change numberFieldInfiniteAdeleAddChar K (algebraMap K (InfiniteAdeleRing K) x) *
    numberFieldFiniteAdeleAddChar (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) = 1
  rw [numberFieldInfiniteAdeleAddChar_diagonal, numberFieldFiniteAdeleAddChar_diagonal]

end Masullo
