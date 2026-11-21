module

public import Lemmas.RationalIdeleWindowMeasure

/-!
# Comparing upstairs and quotient Haar measures over the rationals

Definition A.3.2.1 and (A.3.2.1), pp. 559–560, normalize the quotient
by counting measure on the principal ideles and norm-one mass one.
The window gives a single representative of each class. As in A.3.3.1,
p. 561, mass on a strip of unit log width fixes the Haar scalar.
We construct upstairs Haar at that scale and compare its restriction
with quotient Haar. This does not identify it with the local product
in (A.3.2.5).
-/

open NumberField MeasureTheory Set

namespace Masullo

local notation "Ideles" => IdeleGroup (𝓞 ℚ) ℚ

local instance : T2Space Ideles := t2Space_rationalIdeleGroup

set_option linter.concreteInstances false

variable [MeasurableSpace Ideles] [BorelSpace Ideles]

/-- Haar on the full rational idele group, normalized on the positive
finite-unit window between idelic norms `1` and `e`. -/
public noncomputable def rationalIdeleHaar : Measure Ideles :=
  Measure.haarMeasure rationalIdeleWindowUnitStrip

public instance : rationalIdeleHaar.IsHaarMeasure := by
  unfold rationalIdeleHaar
  infer_instance

/-- The calibration strip has mass one under the constructed upstairs Haar. -/
public theorem rationalIdeleHaar_unitStrip :
    rationalIdeleHaar (rationalIdeleUnitWindow ∩ {a | ideleNorm a ∈ Icc 1 (Real.exp 1)}) = 1 :=
  Measure.haarMeasure_self (K₀ := rationalIdeleWindowUnitStrip)

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

/-- A Haar measure upstairs with mass one on the positive finite-unit
window between norms `1` and `e` induces the checked rational quotient
Haar measure by restriction to that window and pushforward. -/
public theorem map_restrict_rationalIdeleUnitWindow_eq_rationalIdeleClassHaar
    (ν : Measure Ideles) [ν.IsHaarMeasure]
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

/-- Restricting the constructed Haar measure to the fundamental domain
and projecting gives the rational quotient Haar with no extra scalar. -/
public theorem map_restrict_rationalIdeleHaar :
    (rationalIdeleHaar.restrict rationalIdeleUnitWindow).map
      (QuotientGroup.mk : Ideles → RationalIdeleClasses) = rationalIdeleClassHaar :=
  map_restrict_rationalIdeleUnitWindow_eq_rationalIdeleClassHaar _ rationalIdeleHaar_unitStrip

/-- The rational positive finite-unit window strip of norms from `1` to `T`
has upstairs mass `log T`, as in A.3.3.1 for the canonical section. -/
public theorem rationalIdeleHaar_normStrip {T : ℝ} (hT : 1 ≤ T) :
    rationalIdeleHaar (rationalIdeleUnitWindow ∩ {a | ideleNorm a ∈ Icc 1 T}) =
      ENNReal.ofReal (Real.log T) := by
  have hs : MeasurableSet {c : RationalIdeleClasses | ideleClassNorm c ∈ Icc 1 T} :=
    continuous_ideleClassNorm.measurable measurableSet_Icc
  have h := rationalIdeleClassHaar_normStrip hT
  rw [← map_restrict_rationalIdeleHaar,
    Measure.map_apply QuotientGroup.continuous_mk.measurable hs,
    Measure.restrict_apply (QuotientGroup.continuous_mk.measurable hs), inter_comm] at h
  simpa only [preimage_ofPred_eq, ideleClassNorm_mk] using h

end Masullo
