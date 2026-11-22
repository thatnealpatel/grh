module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lemmas.SchwartzLineComplete
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The radial weighted Schwartz stage

For Masullo §1.1.2, second bullet, (1.1.2.1) (p. 11), take `G = ℝ₊ˣ` with identity
module and `k = 1`. The change of coordinates `t = exp x` identifies the unweighted
Schwartz–Bruhat factor with the ordinary Schwartz space (p. 593, before Definition
B.2.1.1), and the multiplier `t ^ a` becomes `exp (a * x)`. The stage is the image
of the weighted map, with the subspace topology of the product of the actual Schwartz
spaces, not a topology of pointwise convergence.

We check closedness and completeness in the all-weight product. This gives the radial
closed-image step cited in Example D.3.3.5 (p. 805), without passing to its countable
subproduct. It is not a proof of the nuclear Fréchet claim or of (D.3.3.7).
-/

open Set
open scoped ContDiff SchwartzMap

namespace Masullo

/-- The radial weight in logarithmic coordinates. -/
@[expose] public noncomputable def logStageWeight (a x : ℝ) : ℂ := Real.exp (a * x)

/-- Back on the positive reals the log-coordinate multiplier is the real power `t ^ a`. -/
public theorem logStageWeight_log (a : ℝ) {t : ℝ} (ht : 0 < t) :
    logStageWeight a (Real.log t) = ((t ^ a : ℝ) : ℂ) := by
  rw [logStageWeight, Real.rpow_def_of_pos ht, mul_comm]

private theorem logStageWeight_ne_zero (a x : ℝ) : logStageWeight a x ≠ 0 := by
  unfold logStageWeight
  exact_mod_cast (Real.exp_pos (a * x)).ne'

private theorem logStageWeight_neg_mul (a x : ℝ) :
    logStageWeight (-a) x * logStageWeight a x = 1 := by
  rw [logStageWeight, logStageWeight, ← Complex.ofReal_mul, ← Real.exp_add, neg_mul,
    neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

private theorem smooth_logStageWeight (a : ℝ) : ContDiff ℝ ∞ (logStageWeight a) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

/-- Smooth profiles whose weighted copies are Schwartz for all weights in `I`. -/
@[expose] public def logWeightedProfiles (I : Set ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := { f | ContDiff ℝ ∞ f ∧
    ∀ a : I, ∃ g : 𝓢(ℝ, ℂ), ∀ x, g x = logStageWeight a x * f x }
  zero_mem' := ⟨contDiff_const, fun a ↦ ⟨0, by simp⟩⟩
  add_mem' := by
    rintro f g ⟨hf, hfw⟩ ⟨hg, hgw⟩
    refine ⟨hf.add hg, fun a ↦ ?_⟩
    obtain ⟨F, hF⟩ := hfw a
    obtain ⟨G, hG⟩ := hgw a
    exact ⟨F + G, fun x ↦ by simp [hF, hG, mul_add]⟩
  smul_mem' := by
    rintro c f ⟨hf, hfw⟩
    refine ⟨contDiff_const.mul hf, fun a ↦ ?_⟩
    obtain ⟨F, hF⟩ := hfw a
    exact ⟨c • F, fun x ↦ by simp [hF, smul_eq_mul, mul_left_comm]⟩

/-- The weighted map (1.1.2.1) for profiles on the logarithmic line. Its range,
not the pointwise topology on the profile functions, models the stage. -/
@[expose] public noncomputable def logWeightedProfileMap (I : Set ℝ) :
    logWeightedProfiles I →ₗ[ℂ] ((a : I) → 𝓢(ℝ, ℂ)) := by
  classical
  let T (f : logWeightedProfiles I) (a : I) := (f.property.2 a).choose
  have hT (f : logWeightedProfiles I) (a : I) (x : ℝ) :
      T f a x = logStageWeight a x * f.1 x := (f.property.2 a).choose_spec x
  refine { toFun := T, map_add' := ?_, map_smul' := ?_ }
  · intro f g
    funext a
    ext x
    simp [hT, mul_add]
  · intro c f
    funext a
    ext x
    simp [hT, smul_eq_mul, mul_left_comm]

@[simp] public theorem logWeightedProfileMap_apply {I : Set ℝ} (f : logWeightedProfiles I)
    (a : I) (x : ℝ) : logWeightedProfileMap I f a x = logStageWeight a x * f.1 x :=
  (f.property.2 a).choose_spec x

/-- The radial stage as a submodule of a product of Schwartz spaces, with its
inherited topology and uniformity. -/
@[expose] public noncomputable def logWeightedStage (I : Set ℝ) :
    Submodule ℂ ((a : I) → 𝓢(ℝ, ℂ)) := (logWeightedProfileMap I).range

/-- A nonempty set of weights suffices to read the original profile from the image. -/
public theorem logWeightedProfileMap_injective {I : Set ℝ} (hI : I.Nonempty) :
    Function.Injective (logWeightedProfileMap I) := by
  obtain ⟨a, ha⟩ := hI
  intro f g h
  apply Subtype.ext
  funext x
  have hx := congrArg (fun F : (i : I) → 𝓢(ℝ, ℂ) ↦ F ⟨a, ha⟩ x) h
  simp only [logWeightedProfileMap_apply] at hx
  exact mul_left_cancel₀ (logStageWeight_ne_zero a x) hx

/-- In the radial stage, compatibility is sufficient as well as necessary: one
coordinate, multiplied by its inverse weight, gives a single smooth profile. -/
public theorem mem_logWeightedStage_iff {I : Set ℝ} (hI : I.Nonempty)
    {F : (a : I) → 𝓢(ℝ, ℂ)} :
    F ∈ logWeightedStage I ↔
      ∀ (a b : I) (x : ℝ), logStageWeight b x * F a x = logStageWeight a x * F b x := by
  change (∃ f : logWeightedProfiles I, logWeightedProfileMap I f = F) ↔ _
  constructor
  · rintro ⟨f, rfl⟩ a b x
    simp only [logWeightedProfileMap_apply]
    rw [mul_left_comm]
  · intro h
    obtain ⟨a, ha⟩ := hI
    let i : I := ⟨a, ha⟩
    let f : ℝ → ℂ := fun x ↦ logStageWeight (-a) x * F i x
    have hf (b : I) (x : ℝ) : F b x = logStageWeight b x * f x := by
      have hx := congrArg (logStageWeight (-a) x * ·) (h i b x)
      calc
        F b x = logStageWeight (-a) x * (logStageWeight a x * F b x) := by
          rw [← mul_assoc, logStageWeight_neg_mul, one_mul]
        _ = logStageWeight (-a) x * (logStageWeight b x * F i x) := hx.symm
        _ = logStageWeight b x * f x := mul_left_comm ..
    let g : logWeightedProfiles I :=
      ⟨f, (smooth_logStageWeight (-a)).mul ((F i).smooth _), fun b ↦ ⟨F b, hf b⟩⟩
    exact ⟨g, funext fun b ↦ DFunLike.ext _ _ fun x ↦
      (logWeightedProfileMap_apply g b x).trans (hf b x).symm⟩

private theorem continuous_schwartz_eval (x : ℝ) : Continuous fun f : 𝓢(ℝ, ℂ) ↦ f x :=
  (BoundedContinuousFunction.evalCLM ℂ x).continuous.comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous

/-- The radial weighted image is closed for the product of the Schwartz topologies. -/
public theorem isClosed_logWeightedStage {I : Set ℝ} (hI : I.Nonempty) :
    IsClosed (logWeightedStage I : Set ((a : I) → 𝓢(ℝ, ℂ))) := by
  have hEq (a b : I) (x : ℝ) : IsClosed
      {F : (a : I) → 𝓢(ℝ, ℂ) | logStageWeight b x * F a x = logStageWeight a x * F b x} :=
    isClosed_eq (continuous_const.mul ((continuous_schwartz_eval x).comp (continuous_apply a)))
      (continuous_const.mul ((continuous_schwartz_eval x).comp (continuous_apply b)))
  convert isClosed_iInter (fun a : I ↦ isClosed_iInter fun b : I ↦
    isClosed_iInter fun x : ℝ ↦ hEq a b x) using 1
  ext F
  change F ∈ logWeightedStage I ↔ _
  simpa only [mem_iInter, mem_ofPred_eq] using (mem_logWeightedStage_iff hI (F := F))

/-- The radial stage is complete in the uniformity induced by the weighted maps. -/
public theorem completeSpace_logWeightedStage {I : Set ℝ} (hI : I.Nonempty) :
    CompleteSpace (logWeightedStage I) := by
  let : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzLine
  exact (isClosed_logWeightedStage hI).isComplete.completeSpace_coe

end Masullo
