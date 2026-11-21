module

public import Lemmas.RationalIdeleWindowMeasure

/-!
# Comparing upstairs and quotient Haar measures over the rationals

Definition A.3.2.1 and (A.3.2.1), pp. 559–560, normalize the quotient
by counting measure on the principal ideles and norm-one mass one.
The window gives a single representative of each class. As in A.3.3.1,
p. 561, mass on a strip of unit log width fixes the Haar scalar.
We assume the upstairs strip mass, not the local product formula
(A.3.2.5) for the upstairs measure.
-/

open NumberField MeasureTheory Set

namespace Masullo

set_option linter.concreteInstances false in
/-- A Haar measure upstairs with mass one on the positive finite-unit
window between norms `1` and `e` induces the checked rational quotient
Haar measure by restriction to that window and pushforward. -/
public theorem map_restrict_rationalIdeleUnitWindow_eq_rationalIdeleClassHaar
    [MeasurableSpace (IdeleGroup (𝓞 ℚ) ℚ)] [BorelSpace (IdeleGroup (𝓞 ℚ) ℚ)]
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    (ν : Measure (IdeleGroup (𝓞 ℚ) ℚ)) [ν.IsHaarMeasure]
    (hν : ν (rationalIdeleUnitWindow ∩ {a | ideleNorm a ∈ Icc 1 (Real.exp 1)}) = 1) :
    (ν.restrict rationalIdeleUnitWindow).map
      (QuotientGroup.mk : IdeleGroup (𝓞 ℚ) ℚ → RationalIdeleClasses) = rationalIdeleClassHaar := by
  let := isHaarMeasure_map_restrict_rationalIdeleUnitWindow ν
  apply eq_rationalIdeleClassHaar_of_normStrip
  have hs : MeasurableSet {c : RationalIdeleClasses | ideleClassNorm c ∈ Icc 1 (Real.exp 1)} :=
    continuous_ideleClassNorm.measurable measurableSet_Icc
  rw [Measure.map_apply QuotientGroup.continuous_mk.measurable hs,
    Measure.restrict_apply (QuotientGroup.continuous_mk.measurable hs), inter_comm]
  simpa only [preimage_ofPred_eq, ideleClassNorm_mk] using hν

end Masullo
