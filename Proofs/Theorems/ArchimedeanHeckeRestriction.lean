module

public import Mathlib.NumberTheory.NumberField.HeckeLFunction
public import Mathlib.Topology.Algebra.Group.Quotient

/-! # Restriction to an Archimedean place

Masullo, p. 121, §3.1.2.2 and (3.1.2.4), uses the continuous insertion
of local units into idele classes. We verify its continuity in Mathlib's
units and quotient topologies and obtain continuity of the composed
character. This does not assert the local analytic isomorphism on character
spaces in Lemma 3.1.2.1.
-/

open NumberField

namespace Masullo

/-- Archimedean single-place insertion into the idele class group is continuous. -/
public theorem continuous_ideleClassGroup_ofCompletion (R K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (v : InfinitePlace K) :
    Continuous (IdeleClassGroup.ofCompletion R K v) := by
  have harch : Continuous (InfiniteAdeleRing.ofCompletion v) := by
    let _ : DecidableEq (InfinitePlace K) := Classical.decEq _
    apply continuous_pi
    intro w
    change Continuous fun x : v.Completion => Pi.mulSingle (M := fun u : InfinitePlace K =>
      u.Completion) v x w
    by_cases hw : w = v
    · subst w
      simp only [Pi.mulSingle_eq_same]
      exact continuous_id
    · simpa only [Pi.mulSingle_eq_of_ne hw] using
        (continuous_const : Continuous fun _ : v.Completion => (1 : w.Completion))
  have hadele : Continuous (AdeleRing.ofCompletion R K v) := harch.prodMk continuous_const
  have hidele : Continuous (IdeleGroup.ofCompletion R K v) := Units.continuous_map hadele
  exact QuotientGroup.continuous_mk.comp hidele

/-- The local character in (3.1.2.4) is continuous on the actual completion units. -/
public theorem continuous_archimedeanHeckeRestriction {K : Type*} [Field K] [NumberField K]
    (χ : HeckeCharacter (𝓞 K) K) (v : InfinitePlace K) :
    Continuous fun x : v.Completionˣ => χ (IdeleClassGroup.ofCompletion (𝓞 K) K v x) :=
  χ.continuous.comp (continuous_ideleClassGroup_ofCompletion (𝓞 K) K v)

end Masullo
