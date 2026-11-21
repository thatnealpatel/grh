module

public import Lemmas.RationalFiniteUnits
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Compactness of the rational norm-one idele class group

This is the compactness part of Theorem A.1.4.3(1), pp. 542–543, over `ℚ`.
The log-norm splitting then gives compactness of closed positive norm bands.
-/

open NumberField Set

namespace Masullo

/-- The norm-one rational idele class group is compact. Every class has a
representative with real coordinate one and all finite coordinates integral
units, and the map from the compact product of these unit groups is continuous. -/
public theorem compactSpace_rationalIdeleClassNormOne : CompactSpace rationalIdeleClassNormOne := by
  let := compactSpace_rationalFiniteUnits
  exact rationalFiniteUnitClass_surjective.compactSpace continuous_rationalFiniteUnitClass

/-- A closed band bounded away from idelic norm zero is compact on the rational
quotient, by the compact norm-one factor and the closed interval in log norm. -/
public theorem isCompact_rationalIdeleClass_normStrip {u v : ℝ} (hu : 0 < u) :
    IsCompact {d : IdeleClassGroup (𝓞 ℚ) ℚ | ideleClassNorm d ∈ Icc u v} := by
  by_cases huv : u ≤ v
  · have hv := hu.trans_le huv
    let := compactSpace_rationalIdeleClassNormOne
    let e := rationalIdeleClassLogSplit
    have hcompact : IsCompact ((Multiplicative.ofAdd '' Icc (Real.log u) (Real.log v)) ×ˢ
        (univ : Set rationalIdeleClassNormOne)) :=
      (isCompact_Icc.image continuous_ofAdd).prod isCompact_univ
    convert hcompact.image e.continuous using 1
    ext d
    change _ ↔ d ∈ e.toEquiv '' _
    rw [e.toEquiv.image_eq_preimage_symm]
    change (u ≤ ideleClassNorm d ∧ ideleClassNorm d ≤ v) ↔
      ((rationalIdeleClassLogSplit.symm d).1 ∈
        Multiplicative.ofAdd '' Icc (Real.log u) (Real.log v) ∧ True)
    rw [and_true, rationalIdeleClassLogSplit_symm_fst]
    have hlog : rationalIdeleClassLogNorm d = Multiplicative.ofAdd (Real.log (ideleClassNorm d)) :=
      congrArg Multiplicative.ofAdd (rationalIdeleClassLogNorm_apply d)
    rw [hlog, Multiplicative.ofAdd.injective.mem_set_image, mem_Icc,
      Real.le_log_iff_exp_le (ideleClassNorm_pos d), Real.log_le_iff_le_exp (ideleClassNorm_pos d),
      Real.exp_log hu, Real.exp_log hv]
  · convert isCompact_empty (X := IdeleClassGroup (𝓞 ℚ) ℚ) using 1
    exact Set.eq_empty_iff_forall_notMem.mpr fun _ h ↦ huv (h.1.trans h.2)

end Masullo
