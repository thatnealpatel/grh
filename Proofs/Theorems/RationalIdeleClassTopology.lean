module

public import Theorems.RationalIdeleClassCompact

import Lemmas.RationalIdeleUnitWindow
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Separation and local compactness of rational idele classes

This is the rational case of Lemma A.1.3.4(1)–(2), p. 542. The proof isolates
`1` among the principal ideles, then uses the log-norm splitting and the
compact norm-one factor for local compactness. It does not fix Haar measure.
-/

open NumberField

namespace Masullo

private noncomputable abbrev Principal := IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ

/-- The principal rational ideles are discrete in the restricted-product units topology. -/
public theorem discreteTopology_rationalPrincipalIdeles :
    DiscreteTopology (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) := by
  change DiscreteTopology Principal
  rw [discreteTopology_iff_isOpen_singleton_one]
  suffices h : ((↑) : Principal → IdeleGroup (𝓞 ℚ) ℚ) ⁻¹' rationalIdeleUnitWindow = {1} by
    rw [← h]
    exact isOpen_rationalIdeleUnitWindow.preimage continuous_subtype_val
  ext a
  change (a : IdeleGroup (𝓞 ℚ) ℚ) ∈ rationalIdeleUnitWindow ↔ a = 1
  constructor
  · rcases a with ⟨_, r, rfl⟩
    intro ha
    have hnorm : ideleNorm (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r) = 1 := by
      rw [ideleNorm_apply]
      exact AdeleRing.norm_algebraMap_eq_one_of_ne_zero r.ne_zero
    have hfin := finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow ha
    have habs := (ideleNorm_eq_abs_rationalIdeleReal _ hfin).symm.trans hnorm
    have hpos : 0 < rationalIdeleReal (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r) := ha.1
    rw [abs_of_pos hpos] at habs
    have hreal : ((r : ℚ) : ℝ) = 1 := by
      rw [← mul_one (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r), rationalIdeleReal_principal_mul]
        at habs
      rwa [rationalIdeleReal_one, mul_one] at habs
    have hr : r = 1 := Units.ext (Rat.cast_injective (by
      simpa only [Units.val_one, Rat.cast_one] using hreal))
    apply Subtype.ext
    simp [hr]
  · rintro rfl
    exact one_mem_rationalIdeleUnitWindow

/-- The principal rational ideles form a closed subgroup of the idele group. -/
public theorem isClosed_rationalPrincipalIdeles :
    IsClosed ((IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) : Set (IdeleGroup (𝓞 ℚ) ℚ)) := by
  change IsClosed (Principal : Set (IdeleGroup (𝓞 ℚ) ℚ))
  let := t2Space_rationalIdeleGroup
  let := discreteTopology_rationalPrincipalIdeles
  exact Subgroup.isClosed_of_discreteTopology

/-- The actual quotient of the rational idele group by the principal ideles is Hausdorff. -/
public theorem t2Space_rationalIdeleClassGroup : T2Space (IdeleClassGroup (𝓞 ℚ) ℚ) := by
  let := isClosed_rationalPrincipalIdeles
  infer_instance

/-- The rational idele class group is locally compact: It is the product of
its compact norm-one factor with the real log-norm line. -/
public theorem locallyCompactSpace_rationalIdeleClassGroup : LocallyCompactSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := by
  let := t2Space_rationalIdeleClassGroup
  let := compactSpace_rationalIdeleClassNormOne
  exact rationalIdeleClassLogSplit.toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace

end Masullo
