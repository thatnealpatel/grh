module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Log reflection on the rational theta Hilbert chart

The Hilbert chart absorbs the symmetric-strip weight. On this unweighted
log-line space, inversion of norm is measure-preserving pullback by negation.
-/

open MeasureTheory

namespace Masullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

private theorem reflection_measurePreserving :
    MeasurePreserving (fun x : ℝ ↦ -x) volume volume :=
  Measure.measurePreserving_neg volume

private noncomputable def logReflectionₗᵢ : H →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ -x) reflection_measurePreserving

private theorem logReflectionₗᵢ_ae (u : H) :
    logReflectionₗᵢ u =ᵐ[(volume : Measure ℝ)] fun x ↦ u (-x) :=
  Lp.coeFn_compMeasurePreserving u reflection_measurePreserving

private theorem logReflectionₗᵢ_involutive : Function.Involutive logReflectionₗᵢ := by
  intro u
  apply Lp.ext
  filter_upwards [logReflectionₗᵢ_ae (logReflectionₗᵢ u),
    reflection_measurePreserving.quasiMeasurePreserving.ae (logReflectionₗᵢ_ae u)] with x h₁ h₂
  exact h₁.trans (by simpa only [neg_neg] using h₂)

/-- Reflection in log norm, acting on the unweighted `L²` chart for the
symmetric-strip norm. The weight root is even. -/
public noncomputable def rationalThetaLogReflection : H ≃ₗᵢ[ℂ] H where
  __ := logReflectionₗᵢ.toLinearMap
  invFun := logReflectionₗᵢ
  left_inv := logReflectionₗᵢ_involutive
  right_inv := logReflectionₗᵢ_involutive
  norm_map' := logReflectionₗᵢ.norm_map

public theorem rationalThetaLogReflection_ae (u : H) :
    rationalThetaLogReflection u =ᵐ[(volume : Measure ℝ)] fun x ↦ u (-x) :=
  logReflectionₗᵢ_ae u

public theorem rationalThetaLogReflection_involutive : Function.Involutive rationalThetaLogReflection :=
  logReflectionₗᵢ_involutive

end Masullo
