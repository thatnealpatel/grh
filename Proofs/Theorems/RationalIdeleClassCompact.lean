module

public import Lemmas.RationalFiniteUnits

/-!
# Compactness of the rational norm-one idele class group

This is the compactness part of Theorem A.1.4.3(1), pp. 542–543, over `ℚ`.
It does not assert the Hausdorff property or fix Haar measure.
-/

namespace Masullo

/-- The norm-one rational idele class group is compact. Every class has a
representative with real coordinate one and all finite coordinates integral
units, and the map from the compact product of these unit groups is continuous. -/
public theorem compactSpace_rationalIdeleClassNormOne : CompactSpace rationalIdeleClassNormOne := by
  let := compactSpace_rationalFiniteUnits
  exact rationalFiniteUnitClass_surjective.compactSpace continuous_rationalFiniteUnitClass

end Masullo
