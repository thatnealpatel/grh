module

public import Lemmas.RationalLocalUnitHaar
public import Theorems.RationalIdeleClassHaar
public import Theorems.RationalIdeleFiniteUnitFactor
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The product of the local unit probabilities on rational idele classes

The rational norm-one Haar probability in (A.3.2.1), p. 560, is the
transport of the local unit probabilities by `u ↦ [(1, u)]`. The
rational local unit mass prescribed by (A.3.2.2) is one. The splitting
in A.3.3.1, p. 561, then gives the radial factor in log coordinates.
This does not construct the restricted product measure upstairs.
-/

open MeasureTheory

namespace Masullo

set_option linter.concreteInstances false

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

local instance : CompactSpace rationalIdeleClassNormOne := compactSpace_rationalIdeleClassNormOne
local instance : T2Space RationalIdeleClasses := t2Space_rationalIdeleClassGroup

/-- The product of the local integral-unit Haar probabilities is sent to the
Haar probability on norm-one classes by `u ↦ [(1, u)]`. -/
public theorem measurePreserving_rationalFiniteUnitClassEquiv :
    MeasurePreserving rationalFiniteUnitClassEquiv rationalFiniteUnitHaar rationalNormOneHaar := by
  let := isHaarMeasure_rationalNormOneHaar
  let := isProbabilityMeasure_rationalNormOneHaar
  exact rationalFiniteUnitClassEquiv.toMonoidHom.measurePreserving
    rationalFiniteUnitClassEquiv.continuous rationalFiniteUnitClassEquiv.surjective
    (by rw [measure_univ, measure_univ])

/-- The normalized Haar measure on the quotient is Lebesgue measure in the
log-norm coordinate times the product of the local integral-unit probabilities,
transported by the canonical class splitting. -/
public theorem rationalIdeleClassHaar_eq_logVolume_prod_finiteUnitHaar :
    rationalIdeleClassHaar = (logVolume.prod rationalFiniteUnitHaar).map
      (fun p ↦ rationalIdeleClassLogSplit (p.1, rationalFiniteUnitClassEquiv p.2)) := by
  have h := measurePreserving_rationalFiniteUnitClassEquiv
  have hp := Measure.map_prod_map logVolume rationalFiniteUnitHaar
    (f := id) measurable_id h.measurable
  rw [Measure.map_id, h.map_eq] at hp
  have hsplit : Measurable (⇑rationalIdeleClassLogSplit) :=
    rationalIdeleClassLogSplit.continuous.measurable
  rw [rationalIdeleClassHaar, hp, Measure.map_map hsplit (measurable_id.prodMap h.measurable)]
  apply congrArg (fun f ↦ (logVolume.prod rationalFiniteUnitHaar).map f)
  funext p
  cases p
  rfl

end Masullo
