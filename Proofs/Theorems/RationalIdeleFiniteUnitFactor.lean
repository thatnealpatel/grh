module

public import Lemmas.RationalFiniteUnits
import Theorems.RationalIdeleClassTopology

/-!
# The finite-unit factor of the rational idele class group

This identifies the norm-one factor of (A.2.2.3), p. 546, by the
representatives in (A.2.3.14), p. 549. The real coordinate is fixed to one,
so no quotient by the diagonal signs remains. No measure is chosen here.
-/

namespace Masullo

/-- The product of the local integral unit groups is isomorphic as a topological
group to the norm-one rational idele classes via `u ↦ [(1, u)]`. -/
public noncomputable def rationalFiniteUnitClassEquiv :
    RationalFiniteUnits ≃ₜ* rationalIdeleClassNormOne := by
  letI := compactSpace_rationalFiniteUnits
  letI := t2Space_rationalIdeleClassGroup
  let e := Equiv.ofBijective rationalFiniteUnitClass
    ⟨rationalFiniteUnitClass_injective, rationalFiniteUnitClass_surjective⟩
  have he : Continuous e := continuous_rationalFiniteUnitClass
  exact { he.homeoOfEquivCompactToT2 with map_mul' := rationalFiniteUnitClass_mul }

@[simp] public theorem rationalFiniteUnitClassEquiv_apply (u : RationalFiniteUnits) :
    rationalFiniteUnitClassEquiv u = rationalFiniteUnitClass u := by
  unfold rationalFiniteUnitClassEquiv
  rfl

end Masullo
