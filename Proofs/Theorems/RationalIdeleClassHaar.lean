module

public import Lemmas.LogVolume
public import Theorems.RationalIdeleClassTopology
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Normalized Haar measure on rational idele classes

In Definition A.3.2.1 and (A.3.2.1), pp. 559–560, the norm-one
factor over `ℚ` has volume one. In the log coordinate of the canonical
section, the radial `dt/t` of A.3.3.1, p. 561, is Lebesgue measure.
Here we construct this normalization on the actual quotient and deduce
the integration formula for functions that depend only on the norm.
-/

open NumberField MeasureTheory Set TopologicalSpace

namespace Masullo

public abbrev RationalIdeleClasses := IdeleClassGroup (𝓞 ℚ) ℚ

-- Keep the Borel instance explicit, as in the rational fundamental-domain theorem.
set_option linter.concreteInstances false

variable [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

local instance : CompactSpace rationalIdeleClassNormOne := compactSpace_rationalIdeleClassNormOne
local instance : T2Space RationalIdeleClasses := t2Space_rationalIdeleClassGroup

/-- Haar probability on the compact norm-one group of rational idele classes. -/
public noncomputable def rationalNormOneHaar : Measure rationalIdeleClassNormOne :=
  Measure.haarMeasure (⊤ : PositiveCompacts rationalIdeleClassNormOne)

public theorem isHaarMeasure_rationalNormOneHaar : rationalNormOneHaar.IsHaarMeasure := by
  unfold rationalNormOneHaar
  infer_instance

public theorem isProbabilityMeasure_rationalNormOneHaar : IsProbabilityMeasure rationalNormOneHaar :=
  ⟨by simpa only [rationalNormOneHaar, PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts rationalIdeleClassNormOne)))⟩

/-- Quotient Haar measure with Lebesgue log norm and Haar probability on
norm-one classes, transported along the canonical splitting. -/
public noncomputable def rationalIdeleClassHaar : Measure RationalIdeleClasses :=
  (logVolume.prod rationalNormOneHaar).map rationalIdeleClassLogSplit

public theorem isHaarMeasure_rationalIdeleClassHaar : rationalIdeleClassHaar.IsHaarMeasure := by
  let := isHaarMeasure_rationalNormOneHaar
  let := isProbabilityMeasure_rationalNormOneHaar
  have := isHaarMeasure_logVolume_prod rationalNormOneHaar
  unfold rationalIdeleClassHaar
  infer_instance

/-- The log norm sends the normalized quotient Haar measure to Lebesgue measure. -/
public theorem measurePreserving_rationalIdeleClass_logNorm :
    MeasurePreserving (fun c : RationalIdeleClasses ↦ Real.log (ideleClassNorm c))
      rationalIdeleClassHaar volume := by
  have hlog : Measurable (fun c : RationalIdeleClasses ↦ Real.log (ideleClassNorm c)) := by
    simpa only [Function.comp_def, rationalIdeleClassLogNorm_apply] using
      Measurable.comp measurable_toAdd (map_continuous rationalIdeleClassLogNorm).measurable
  let := isProbabilityMeasure_rationalNormOneHaar
  refine ⟨hlog, ?_⟩
  have hcomp : (fun c : RationalIdeleClasses ↦ Real.log (ideleClassNorm c)) ∘
      rationalIdeleClassLogSplit = Multiplicative.toAdd ∘ Prod.fst := by
    funext p
    rw [Function.comp_apply, ← rationalIdeleClassLogNorm_apply,
      ← rationalIdeleClassLogSplit_symm_fst, ContinuousMulEquiv.symm_apply_apply]
    rfl
  have hsplit : Measurable rationalIdeleClassLogSplit := rationalIdeleClassLogSplit.continuous.measurable
  rw [rationalIdeleClassHaar, Measure.map_map hlog hsplit,
    hcomp, ← Measure.map_map measurable_toAdd measurable_fst,
    (measurePreserving_fst (μ := logVolume) (ν := rationalNormOneHaar)).map_eq,
    map_toAdd_logVolume]

/-- The norm strip from `1` to `T` has mass `log T` for `T ≥ 1`,
expressed in `ℝ≥0∞`. -/
public theorem rationalIdeleClassHaar_normStrip {T : ℝ} (hT : 1 ≤ T) :
    rationalIdeleClassHaar {c : RationalIdeleClasses | ideleClassNorm c ∈ Icc 1 T} =
      ENNReal.ofReal (Real.log T) := by
  have hstrip : {c : RationalIdeleClasses | ideleClassNorm c ∈ Icc 1 T} =
      (fun c : RationalIdeleClasses ↦ Real.log (ideleClassNorm c)) ⁻¹' Icc 0 (Real.log T) := by
    ext c
    change (1 ≤ ideleClassNorm c ∧ ideleClassNorm c ≤ T) ↔
      (0 ≤ Real.log (ideleClassNorm c) ∧ Real.log (ideleClassNorm c) ≤ Real.log T)
    rw [Real.le_log_iff_exp_le (ideleClassNorm_pos c), Real.exp_zero,
      Real.log_le_iff_le_exp (ideleClassNorm_pos c), Real.exp_log (zero_lt_one.trans_le hT)]
  rw [hstrip, measurePreserving_rationalIdeleClass_logNorm.measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc, sub_zero]

/-- In particular, a measurable complex test of the log norm is integrable
on the quotient precisely when it is integrable on the real log line. -/
public theorem integrable_rationalIdeleClass_logNorm_iff {f : ℝ → ℂ} (hf : Measurable f) :
    Integrable (fun c : RationalIdeleClasses ↦ f (Real.log (ideleClassNorm c)))
      rationalIdeleClassHaar ↔ Integrable f :=
  measurePreserving_rationalIdeleClass_logNorm.integrable_comp hf.aestronglyMeasurable

/-- Integration of a function of log norm needs no extra compact volume factor. -/
public theorem integral_rationalIdeleClass_logNorm {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ c : RationalIdeleClasses, f (Real.log (ideleClassNorm c)) ∂rationalIdeleClassHaar) =
      ∫ x : ℝ, f x := by
  have h := measurePreserving_rationalIdeleClass_logNorm
  exact (integral_map h.measurable.aemeasurable (h.map_eq.symm ▸ hf.aestronglyMeasurable)).symm.trans
    (congrArg (fun μ ↦ ∫ x : ℝ, f x ∂μ) h.map_eq)

end Masullo
