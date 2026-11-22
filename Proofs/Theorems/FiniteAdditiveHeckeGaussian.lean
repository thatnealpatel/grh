module

public import Theorems.IdeleHeckeGaussian
import Lemmas.FiniteCompletionAddHaar
import Lemmas.FiniteHeckeRestriction
import Lemmas.FiniteLocalNormShell
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-! # The finite additive Gaussian and its zero modes

Definition 3.4.3.2, (3.4.3.7)–(9), PDF p. 152, gives the integer-ring
indicator in the unramified case and the inverse character times the
integer-unit indicator in the ramified case. We identify the restrictions
with the Gaussian already used on ideles, and compute the additive
zero modes needed in (2.2.3.2), p. 82. The reading uses pinned Markdown and
numbered PDF layout and is provisional.
-/

open IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace
open scoped Classical Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
variable (χ : HeckeCharacter (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "U" => Metric.sphere (0 : F) 1

/-- The finite Gaussian of (3.4.3.7)–(8) as a function on the additive
completion, including zero. -/
@[expose] public noncomputable def finiteAdditiveHeckeGaussian (x : F) : ℂ :=
  if χ.IsUnramifiedAt v then (O : Set F).indicator (fun _ ↦ 1) x
  else (U).indicator (fun y ↦ (χ.restrict v y)⁻¹) x

/-- This is an extension of the very same finite test used on the ideles. -/
public theorem finiteAdditiveHeckeGaussian_coe_unit (x : Fˣ) :
    finiteAdditiveHeckeGaussian χ v (x : F) = finiteHeckeGaussian χ v x := by
  classical
  unfold finiteAdditiveHeckeGaussian finiteHeckeGaussian
  by_cases h : χ.IsUnramifiedAt v
  · simp only [ite_eq_left h, finiteCompletionIntegers_eq_closedBall v, indicator_apply,
      Metric.mem_closedBall, dist_zero_right]
  · simp only [ite_eq_right h, indicator_apply, finiteLocalUnitSet, Metric.mem_sphere, dist_zero_right,
      mem_ofPred_eq]

/-- The finite additive Gaussian is continuous and supported on a compact
subset of the integer ring. -/
public theorem continuous_hasCompactSupport_finiteAdditiveHeckeGaussian :
    Continuous (finiteAdditiveHeckeGaussian χ v) ∧
      HasCompactSupport (finiteAdditiveHeckeGaussian χ v) := by
  classical
  have hc : IsCompact (O : Set F) := isCompact_iff_compactSpace.mpr
    (compactSpace_finiteCompletionIntegers K v)
  have hU : U ⊆ (O : Set F) := by
    rw [finiteCompletionIntegers_eq_closedBall v]
    exact Metric.sphere_subset_closedBall
  unfold finiteAdditiveHeckeGaussian
  split_ifs
  · refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hc support_indicator_subset⟩
    rw [finiteCompletionIntegers_eq_closedBall v]
    exact (IsUltrametricDist.isClopen_closedBall (0 : F) one_ne_zero).continuous_indicator
      continuous_const
  · refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hc
      (support_indicator_subset.trans hU)⟩
    have hs : IsClopen U := IsUltrametricDist.isClopen_sphere (0 : F) one_ne_zero
    apply continuous_indicator (by simp [isClopen_iff_frontier_eq_empty.mp hs])
    rw [hs.1.closure_eq]
    have hne (y : F) (hy : y ∈ U) : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hcont : ContinuousOn (χ.restrict v : F → ℂ) {y | y ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      let e : Fˣ ≃ₜ {y : F // y ≠ 0} := unitsHomeomorphNeZero
      have he (u : Fˣ) : (e u : F) = (u : F) := rfl
      have hcomp := (continuous_finiteHeckeRestriction χ v).comp e.symm.continuous
      convert hcomp using 1
      ext y
      exact congrArg (χ.restrict v) ((congrArg Subtype.val (e.apply_symm_apply y)).symm.trans
        (he (e.symm y)))
    exact (hcont.mono fun y hy ↦ hne y hy).inv₀ fun y hy ↦
      (isUnit_iff_ne_zero.mpr (hne y hy)).map (χ.restrict v) |>.ne_zero

/-- The original zero mode, before any norm-one averaging. -/
public theorem finiteAdditiveHeckeGaussian_zero :
    finiteAdditiveHeckeGaussian χ v 0 = if χ.IsUnramifiedAt v then 1 else 0 := by
  classical
  unfold finiteAdditiveHeckeGaussian
  split_ifs <;> simp

/-- The Fourier zero mode is the additive Haar mass of the integer ring
in the unramified case. In the ramified case the integral is zero by
multiplication by an integral unit on which the character is nontrivial. -/
public theorem integral_finiteAdditiveHeckeGaussian [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    (∫ x, finiteAdditiveHeckeGaussian χ v x ∂μ) =
      if χ.IsUnramifiedAt v then (μ.real (O : Set F) : ℂ) else 0 := by
  classical
  by_cases h : χ.IsUnramifiedAt v
  · simp only [finiteAdditiveHeckeGaussian, ite_eq_left h]
    have ho : MeasurableSet (O : Set F) := (Valued.isOpen_valuationSubring F).measurableSet
    simpa using integral_indicator_const (μ := μ) (1 : ℂ) ho
  · obtain ⟨a, ha⟩ := not_forall.mp (fun hh ↦ h (HeckeCharacter.isUnramifiedAt_iff.mpr hh))
    let u : Fˣ := Units.map (O).subtype.toMonoidHom a
    have hu : ‖(u : F)‖ = 1 := (finiteLocalUnitSet_eq_range v).ge ⟨a, rfl⟩
    change χ.restrict v (u : F) ≠ 1 at ha
    let e := ContinuousAddEquiv.mulLeft u
    let f := finiteAdditiveHeckeGaussian χ v
    have he (x : F) : f (e x) = (χ.restrict v (u : F))⁻¹ * f x := by
      have hnorm : ‖e x‖ = ‖x‖ := by simp [e, norm_mul, hu]
      simp only [f, finiteAdditiveHeckeGaussian, ite_eq_right h, indicator_apply, Metric.mem_sphere,
        dist_zero_right, hnorm]
      split_ifs
      · change (χ.restrict v ((u : F) * x))⁻¹ = _
        rw [map_mul, mul_inv_rev, mul_comm]
      · rw [mul_zero]
    have hint := (finiteCompletion_measurePreserving_mul_unit v μ u hu).integral_comp
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding f
    change (∫ x, f (e x) ∂μ) = ∫ x, f x ∂μ at hint
    simp_rw [he, integral_const_mul] at hint
    have ha' : (χ.restrict v (u : F))⁻¹ ≠ 1 := by simpa using ha
    rw [ite_eq_right h]
    by_contra hi
    exact ha' (mul_right_cancel₀ hi (hint.trans (one_mul _).symm))

end Masullo
