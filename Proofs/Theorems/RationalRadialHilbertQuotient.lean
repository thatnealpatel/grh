module

public import Lemmas.HilbertDenseQuotient
public import Theorems.RadialHardySobolevCompletion
public import Theorems.RationalThetaWeightedStage
public import Theorems.RationalIdeleClassHaar
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # The separated rational radial Hardy–Sobolev quotient

For the trivial norm-one character over `ℚ`, use the actual half-twisted
class theta on the represented two-mode adelic LF input. The completed
middle space is the closure of all-weight log profiles, and the completed
left space is the closure of the original theta range *in that middle
space*. The right space is its orthogonal complement. The original
algebraic quotient maps densely into it, with the quotient seminorm, not
an asserted separated norm on the original classes.
-/

open Function NumberField MeasureTheory Set
open scoped ENNReal

namespace Masullo

/-- The ambient Hilbert space is the closure of all-weight profiles in the
same weighted `L²` as the interval model, with the subspace norm. -/
@[expose] public noncomputable def rationalRadialHilbert {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Submodule ℂ (Lp ℂ 2 (logSobolevMeasure a b s)) :=
  (logSobolevAllToLp hab s).range.topologicalClosure

/-- The same completion is obtained from the endpoint-weighted stage. -/
public theorem coe_rationalRadialHilbert {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (rationalRadialHilbert hab s : Set (Lp ℂ 2 (logSobolevMeasure a b s))) =
      closure (range (logSobolevToLp hab s)) :=
  (logSobolev_commonCompletion hab s).1

public instance completeSpace_rationalRadialHilbert {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    CompleteSpace (rationalRadialHilbert hab s) := by
  apply IsComplete.completeSpace_coe
  rw [coe_rationalRadialHilbert]
  exact (logSobolev_commonCompletion hab s).2

private def intervalProfile {a b : ℝ} (f : logWeightedProfiles univ) :
    logWeightedProfiles (Icc a b) :=
  ⟨f.1, f.property.1, fun w ↦ f.property.2 ⟨w, mem_univ _⟩⟩

private theorem logSobolevAllToLp_eq_interval {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : logWeightedProfiles univ) :
    logSobolevAllToLp hab s f = logSobolevToLp hab s (intervalProfile f) := by
  have h₁ : (logSobolevAllToLp hab s f : ℝ → ℂ) =ᵐ[logSobolevMeasure a b s] f.val :=
    logSobolevAllToLp_ae_eq hab s f
  have h₂ : (logSobolevToLp hab s (intervalProfile f) : ℝ → ℂ) =ᵐ[logSobolevMeasure a b s] f.val :=
    logSobolevToLp_ae_eq hab s (intervalProfile f)
  exact Lp.ext (h₁.trans h₂.symm)

/-- The original all-weight test stage in the completed middle term. -/
@[expose] public noncomputable def rationalRadialHilbertInclusion {a b : ℝ}
    (hab : a ≤ b) (s : ℝ) : logWeightedProfiles univ →ₗ[ℂ] rationalRadialHilbert hab s :=
  (logSobolevAllToLp hab s).codRestrict _ (fun f ↦ subset_closure ⟨f, rfl⟩)

/-- The ambient inclusion loses no pointwise information. -/
public theorem injective_rationalRadialHilbertInclusion {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Injective (rationalRadialHilbertInclusion hab s) := by
  intro F G h
  have hh := congrArg (fun y : rationalRadialHilbert hab s ↦ y.val) h
  change logSobolevAllToLp hab s F = logSobolevAllToLp hab s G at hh
  rw [logSobolevAllToLp_eq_interval, logSobolevAllToLp_eq_interval] at hh
  exact Subtype.ext (congrArg (fun u : logWeightedProfiles (Icc a b) ↦ u.val)
    (logSobolevToLp_injective hab s hh))

/-- Test profiles are dense in the completed middle term. -/
public theorem denseRange_rationalRadialHilbertInclusion {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    DenseRange (rationalRadialHilbertInclusion hab s) := by
  intro y
  rw [closure_subtype, ← Set.range_comp]
  exact y.property

set_option linter.concreteInstances false

/-- The weighted formula for the representative norm, with its exact canonical
Haar normalization on rational idele classes. The radial test given by `f`
reads `f(log |d|)` on a class `d`. -/
public theorem norm_rationalRadialHilbertInclusion {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    (f : logWeightedProfiles univ) :
    ‖rationalRadialHilbertInclusion hab s f‖ = Real.sqrt
      (∫ d : RationalIdeleClasses, logSobolevWeight a b s (Real.log (ideleClassNorm d)) *
        ‖f.1 (Real.log (ideleClassNorm d))‖ ^ 2 ∂rationalIdeleClassHaar) := by
  change ‖logSobolevAllToLp hab s f‖ = _
  rw [logSobolevAllToLp_eq_interval, norm_logSobolevToLp]
  let w (x : ℝ) : ℝ := logSobolevWeight a b s x * ‖f.1 x‖ ^ 2
  have hw : Integrable w :=
    integrable_logSobolevWeight_mul_norm_sq (s := s) hab (intervalProfile f).property
  have h := measurePreserving_rationalIdeleClass_logNorm
  change Real.sqrt (∫ x, w x) = Real.sqrt (∫ d, w (Real.log (ideleClassNorm d)) ∂rationalIdeleClassHaar)
  have hw' : AEStronglyMeasurable w (rationalIdeleClassHaar.map
      (fun d ↦ Real.log (ideleClassNorm d))) := h.map_eq.symm ▸ hw.aestronglyMeasurable
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hw']

/-- The same representative norm in the positive-real variable and `dt/t`. -/
public theorem norm_rationalRadialHilbertInclusion_positiveIntegral {a b : ℝ}
    (hab : a ≤ b) (s : ℝ) (f : logWeightedProfiles univ) :
    let μ := (((volume : Measure ℝ).restrict ({0}ᶜ)).withDensity
      (fun t ↦ ENNReal.ofReal |t|⁻¹)).restrict (Ioi 0)
    ‖rationalRadialHilbertInclusion hab s f‖ = Real.sqrt
      (∫ t, max (t ^ (2 * a)) (t ^ (2 * b)) *
        (1 + |Real.log t| ^ 2) ^ (s / 2) * ‖f.1 (Real.log t)‖ ^ 2 ∂μ) := by
  change ‖logSobolevAllToLp hab s f‖ = _
  rw [logSobolevAllToLp_eq_interval]
  exact (logSobolevToLp_positiveIntegral hab s (intervalProfile f)).2

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "Θ" => rationalAdeleClassThetaLFLinear
variable [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

private noncomputable def allWeightStageEquiv :
    logWeightedProfiles univ ≃ₗ[ℂ] logWeightedStage univ :=
  LinearEquiv.ofInjective (logWeightedProfileMap univ) (logWeightedProfileMap_injective univ_nonempty)

/-- Recover the actual pointwise profile from the accepted all-weight stage
arrow by forgetting its redundant Schwartz coordinates. -/
public noncomputable def rationalRadialThetaProfiles :
    RationalThetaRadialInput →ₗ[ℂ] logWeightedProfiles univ :=
  allWeightStageEquiv.symm.toLinearMap.comp rationalThetaRadialWeightedStage

/-- The profile is exactly the half twist, not a reconstruction from a.e. data. -/
public theorem rationalRadialThetaProfiles_apply (f : RationalThetaRadialInput) (x : ℝ) :
    (rationalRadialThetaProfiles f).val x = rationalThetaRadialTwistedProfile (1 / 2) f x := by
  let c : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  have hW : allWeightStageEquiv (rationalRadialThetaProfiles f) = rationalThetaRadialWeightedStage f :=
    allWeightStageEquiv.apply_symm_apply _
  have hc := congrArg (fun F : logWeightedStage univ ↦ F.val c x) hW
  change logWeightedProfileMap univ (rationalRadialThetaProfiles f) c x = _ at hc
  rw [logWeightedProfileMap_apply, rationalThetaRadialWeightedStage_apply] at hc
  simpa only [c, logStageWeight, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using hc

/-- The original half-twisted theta range in the all-weight test space.
This is a range on the global LF inputs, not on local or fixed-band tests. -/
@[expose] public noncomputable def rationalRadialThetaTestRange :
    Submodule ℂ (logWeightedProfiles univ) := rationalRadialThetaProfiles.range

/-- The original global LF theta map followed by the exact weighted inclusion. -/
@[expose] public noncomputable def rationalRadialThetaToHilbert {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    RationalThetaRadialInput →ₗ[ℂ] rationalRadialHilbert hab s :=
  (rationalRadialHilbertInclusion hab s).comp rationalRadialThetaProfiles

/-- Its weighted `L²` representative is the accepted half-twisted profile, not
just a test with the same moments. -/
public theorem rationalRadialThetaToHilbert_ae_eq {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : RationalThetaRadialInput) :
    ((rationalRadialThetaToHilbert hab s f).val : ℝ → ℂ) =ᵐ[logSobolevMeasure a b s]
      rationalThetaRadialTwistedProfile (1 / 2) f := by
  exact (logSobolevAllToLp_ae_eq hab s (rationalRadialThetaProfiles f)).trans
    (Filter.Eventually.of_forall (rationalRadialThetaProfiles_apply f))

/-- The finer stage's theta kernel is unchanged by this faithful `L²` embedding.
This concerns the left arrow, not the kernel of the quotient on the right. -/
public theorem rationalRadialThetaToHilbert_eq_zero_iff {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (f : RationalThetaRadialInput) :
    rationalRadialThetaToHilbert hab s f = 0 ↔ Θ f.val = 0 := by
  have hIncl := injective_rationalRadialHilbertInclusion hab s
  have hStage : Injective (allWeightStageEquiv.symm.toLinearMap :
      logWeightedStage univ →ₗ[ℂ] logWeightedProfiles univ) := allWeightStageEquiv.symm.injective
  change rationalRadialHilbertInclusion hab s
    (allWeightStageEquiv.symm.toLinearMap (rationalThetaRadialWeightedStage f)) = 0 ↔ _
  rw [← map_zero (rationalRadialHilbertInclusion hab s), hIncl.eq_iff,
    ← map_zero allWeightStageEquiv.symm.toLinearMap, hStage.eq_iff,
    rationalThetaRadialWeightedStage_eq_zero_iff]

/-- The actual theta range inside the Hilbert ambient, before closing it. -/
public noncomputable abbrev rationalRadialThetaHilbertRange {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Submodule ℂ (rationalRadialHilbert hab s) :=
  rationalRadialThetaTestRange.map (rationalRadialHilbertInclusion hab s)

/-- The submodule used for the quotient is exactly the range on original inputs. -/
public theorem rationalRadialThetaHilbertRange_eq_range {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    rationalRadialThetaHilbertRange hab s = (rationalRadialThetaToHilbert hab s).range := by
  rw [rationalRadialThetaToHilbert, LinearMap.range_comp]
  rfl

/-- The completed theta subspace, with its inherited Hilbert norm. -/
public noncomputable abbrev rationalRadialThetaClosure {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Submodule ℂ (rationalRadialHilbert hab s) :=
  (rationalRadialThetaHilbertRange hab s).topologicalClosure

/-- The global LF source modulo its original class-theta kernel embeds densely
in the completed left term. The map on representatives is precisely the
weighted inclusion, so it preserves the norm induced by the middle term. -/
public theorem exists_rationalRadialThetaClosureEmbedding {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    let Θ₀ := LinearMap.comp Θ rationalThetaRadialInputSubmodule.subtype
    ∃ L : (RationalThetaRadialInput ⧸ Θ₀.ker) →ₗ[ℂ] rationalRadialThetaClosure hab s,
      Injective L ∧ DenseRange L ∧ ∀ f : RationalThetaRadialInput,
        (L (Θ₀.ker.mkQ f)).val = rationalRadialThetaToHilbert hab s f := by
  dsimp only
  let Θ₀ := LinearMap.comp Θ rationalThetaRadialInputSubmodule.subtype
  have hker : Θ₀.ker = (rationalRadialThetaToHilbert hab s).ker := by
    ext f
    simp only [LinearMap.mem_ker]
    exact (rationalRadialThetaToHilbert_eq_zero_iff hab s f).symm
  have h := exists_denseEmbedding_quotient_rangeClosure _ _ hker
  rw [← rationalRadialThetaHilbertRange_eq_range hab s] at h
  exact h

/-- Realize the Hilbert quotient by the closed theta range as a genuine closed
inner-product subspace of the Hilbert ambient. -/
public noncomputable abbrev rationalRadialHilbertQuotient {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    Submodule ℂ (rationalRadialHilbert hab s) := (rationalRadialThetaHilbertRange hab s)ᗮ

/-- Completed quotient projection, in the inherited norm topology. -/
public noncomputable abbrev rationalRadialQuotientProjection {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    rationalRadialHilbert hab s →L[ℂ] rationalRadialHilbertQuotient hab s :=
  hilbertQuotientProjection (rationalRadialThetaHilbertRange hab s)

/-- The completed sequence is exact and the projection is onto. -/
public theorem rationalRadialQuotientProjection_exact {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (rationalRadialQuotientProjection hab s).ker = rationalRadialThetaClosure hab s ∧
      Surjective (rationalRadialQuotientProjection hab s) :=
  ⟨ker_hilbertQuotientProjection _, surjective_hilbertQuotientProjection _⟩

/-- Descend to the original radial test quotient by the *unclosed* theta range. -/
public noncomputable abbrev rationalRadialQuotientMap {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (logWeightedProfiles univ ⧸ rationalRadialThetaTestRange) →ₗ[ℂ]
      rationalRadialHilbertQuotient hab s :=
  hilbertDenseQuotientMap (rationalRadialHilbertInclusion hab s) rationalRadialThetaTestRange

/-- The norm of an original class is the infimum distance to the range of
half-twisted theta of actual global LF tests, not just to a fixed band. -/
public theorem norm_rationalRadialQuotientMap_mk {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (u : logWeightedProfiles univ) :
    ‖rationalRadialQuotientMap hab s (rationalRadialThetaTestRange.mkQ u)‖ =
      Metric.infDist (rationalRadialHilbertInclusion hab s u)
        (range (rationalRadialThetaToHilbert hab s)) := by
  rw [← LinearMap.coe_range, ← rationalRadialThetaHilbertRange_eq_range hab s]
  exact norm_hilbertDenseQuotientMap_mk _ _ _

/-- On the original algebraic quotient, the kernel is the pullback of the
Hilbert closure modulo the original theta range. -/
public theorem ker_rationalRadialQuotientMap {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    LinearMap.ker (rationalRadialQuotientMap hab s) =
      ((rationalRadialThetaClosure hab s).comap (rationalRadialHilbertInclusion hab s)).map
        rationalRadialThetaTestRange.mkQ :=
  ker_hilbertDenseQuotientMap _ _

/-- Separating the distance seminorm and then completing the original quotient
gives this Hilbert model: the descended map preserves seminorm and has dense
range in a complete space with its inherited inner-product norm. -/
public theorem rationalRadialQuotientMap_dense_complete {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    DenseRange (rationalRadialQuotientMap hab s) ∧
      CompleteSpace (rationalRadialHilbertQuotient hab s) :=
  ⟨denseRange_hilbertDenseQuotientMap _ _ (denseRange_rationalRadialHilbertInclusion hab s),
    inferInstance⟩

end Masullo
