module

public import Lemmas.RationalDiagonalPairing
public import Theorems.RationalAdeleClassTopology

/-!
# The dual of the discrete rational diagonal

The standard pairing identifies the compact rational adele classes with the
characters of the discrete diagonal. This is a step toward the full adelic
self-duality in Example A.3.1.8, p. 558, not a Haar comparison.
-/

open NumberField Function Set Topology

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "D" => rationalDiagonal
local notation "C" => A ⧸ D
local notation "R" => Multiplicative D

/-- The standard pairing descends to a map from additive adele classes to the
compact-open dual of the discrete diagonal. -/
public noncomputable def rationalAdeleClassToDiagonalDual :
    C →+ Additive (PontryaginDual R) :=
  QuotientAddGroup.lift D rationalAdeleRestrictChar ker_rationalAdeleRestrictChar.ge

@[simp] public theorem rationalAdeleClassToDiagonalDual_mk (a : A) :
    rationalAdeleClassToDiagonalDual (a : C) = rationalAdeleRestrictChar a := by
  rw [rationalAdeleClassToDiagonalDual, QuotientAddGroup.lift_mk]

/-- The value on a diagonal input is the original pairing, evaluated at a representative. -/
public theorem rationalAdeleClassToDiagonalDual_mk_apply (a : A) (r : R) :
    ((rationalAdeleClassToDiagonalDual (a : C)).toMul r : ℂ) =
      rationalAdeleAddChar (a * (r.toAdd : A)) := by
  rw [rationalAdeleClassToDiagonalDual_mk, rationalAdeleRestrictChar_apply]

public theorem continuous_rationalAdeleClassToDiagonalDual :
    Continuous rationalAdeleClassToDiagonalDual :=
  (QuotientAddGroup.isQuotientMap_mk D).continuous_iff.mpr continuous_rationalAdeleRestrictChar

/-- Every character of the discrete rational diagonal is represented by pairing with
an adele, and its representing adele is unique modulo the diagonal. -/
public theorem bijective_rationalAdeleClassToDiagonalDual :
    Bijective rationalAdeleClassToDiagonalDual := by
  refine ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero rationalAdeleClassToDiagonalDual).mpr
    intro c hc
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    rw [QuotientAddGroup.eq_zero_iff, ← ker_rationalAdeleRestrictChar]
    exact hc
  · intro χ
    let : CompactSpace C := compactSpace_rationalAdeleClasses
    -- Each prescribed value is closed on the compact quotient. The finite tests
    -- have a common solution, so all the value constraints have a common solution.
    let E (r : ℚ) : Set C :=
      {c | (rationalAdeleClassToDiagonalDual c).toMul (rationalDiagonalInput r) =
        χ.toMul (rationalDiagonalInput r)}
    have hclosed (r : ℚ) : IsClosed (E r) :=
      isClosed_eq ((continuous_eval_const (F := R →ₜ* Circle) (rationalDiagonalInput r)).comp
        continuous_rationalAdeleClassToDiagonalDual) continuous_const
    have hfinite (s : Finset ℚ) : (⋂ r ∈ s, E r).Nonempty := by
      obtain ⟨a, ha⟩ := exists_rationalAdele_matching_diagonal_tests χ.toMul s
      exact ⟨(a : C), mem_iInter₂.mpr ha⟩
    obtain ⟨c, hc⟩ := CompactSpace.iInter_nonempty hclosed hfinite
    refine ⟨c, ?_⟩
    change (rationalAdeleClassToDiagonalDual c).toMul = χ.toMul
    apply PontryaginDual.ext
    intro r
    obtain ⟨q, hq⟩ := rationalDiagonalEquiv.surjective r.toAdd
    change rationalDiagonalInput q = r at hq
    rw [← hq]
    exact mem_iInter.mp hc q

end Masullo
