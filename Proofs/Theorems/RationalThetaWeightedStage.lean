module

public import Theorems.RadialWeightedSchwartzStage
public import Theorems.RationalThetaRadialCore
import Theorems.RationalAdeleLFDilationZeroModes

/-! # The weighted Schwartz left arrow for rational radial theta

The first isotypic arrow of Masullo §1.2.1 (p. 13), for `F = ℚ` and
trivial norm-one character, uses the global theta sum on two-mode tests
and the half-norm twist. The radial target is the all-real-weight Schwartz
stage in log coordinates, not a weighted Hilbert completion.
-/

open Bornology NumberField MeasureTheory Set
open scoped ContDiff SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "τ" x:max => rationalIdeleClassLogSection (Multiplicative.ofAdd x)
local notation "Θ" => rationalAdeleClassThetaLFLinear
local notation "D" => rationalAdeleLFDilationDeriv
set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]

private def Modes (f : E) : Prop :=
  f.toUnion.val 0 = 0 ∧ rationalAdeleFourier f.toUnion.val 0 = 0

private noncomputable def logTheta (a : ℝ) (f : E) (x : ℝ) : ℂ :=
  logStageWeight a x * Θ f (τ x)

private noncomputable def shiftDeriv (a : ℝ) : E →L[ℂ] E :=
  (a : ℂ) • ContinuousLinearMap.id ℂ E + D

private theorem shiftDeriv_modes (a : ℝ) {f : E} (hf : Modes f) : Modes (shiftDeriv a f) := by
  unfold Modes at hf ⊢
  obtain ⟨h₀, hF⟩ := rationalAdeleLFDilationDeriv_preserves_zero_modes f hf.1 hf.2
  constructor
  · change (((a : ℂ) • f + D f).toUnion.val) 0 = _
    simp only [map_add, map_smul, Submodule.coe_smul, Submodule.coe_add, Pi.smul_apply,
      Pi.add_apply, hf.1, h₀, smul_zero, add_zero]
  · have hfF := hf.2
    change rationalAdeleFourier (((a : ℂ) • f + D f).toUnion.val) 0 = _
    rw [← rationalAdeleLFFourier_eq, map_add, map_smul, map_add, map_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply]
    rw [rationalAdeleLFFourier_eq, rationalAdeleLFFourier_eq, hfF, hF, smul_zero, add_zero]

private theorem hasDerivAt_logTheta (a : ℝ) (f : E) (x : ℝ) :
    HasDerivAt (logTheta a f) (logTheta a (shiftDeriv a f) x) x := by
  have hΘ : HasDerivAt (fun t : ℝ ↦ Θ f (τ t)) (Θ (D f) (τ x)) x := by
    have h := hasDerivAt_rationalAdeleClassTheta_logDilation f 1 x
    have h1 (t : ℝ) : τ t * 1 = τ t := by
      have ht := (map_mul rationalIdeleClassLogSection (Multiplicative.ofAdd t) 1).symm
      rw [mul_one, map_one] at ht
      exact ht
    simp only [h1] at h
    simpa only [rationalAdeleClassThetaLFLinear_apply] using h
  have hW : HasDerivAt (logStageWeight a) ((a : ℂ) * logStageWeight a x) x := by
    have h := (Real.hasDerivAt_exp (a * x)).comp x ((hasDerivAt_id x).const_mul a)
    change HasDerivAt (fun t : ℝ ↦ (Real.exp (a * t) : ℂ))
      ((a : ℂ) * (Real.exp (a * x) : ℂ)) x
    simpa only [id_eq, mul_one, Function.comp_apply, Complex.ofReal_mul,
      mul_comm (Complex.ofReal (Real.exp (a * x)))] using h.ofReal_comp
  convert hW.mul hΘ using 1
  · rfl
  change logStageWeight a x * Θ (shiftDeriv a f) (τ x) = _
  change logStageWeight a x * Θ ((a : ℂ) • f + D f) (τ x) = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem smooth_logTheta (a : ℝ) (f : E) : ContDiff ℝ ∞ (logTheta a f) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing f with
  | zero => simpa only [Nat.cast_zero, contDiff_zero] using
      continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_logTheta a f x).continuousAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (hasDerivAt_logTheta a f x).differentiableAt, by simp, ?_⟩
    rw [show deriv (logTheta a f) = logTheta a (shiftDeriv a f) from
      funext fun x ↦ (hasDerivAt_logTheta a f x).deriv]
    exact ih _

private theorem iteratedDeriv_logTheta (a : ℝ) (n : ℕ) (f : E) :
    iteratedDeriv n (logTheta a f) = logTheta a ((shiftDeriv a)^[n] f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact funext fun x ↦ (hasDerivAt_logTheta a _ x).deriv

variable [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

private theorem weighted_logTheta_bound (a : ℝ) (k n : ℕ) {B : Set E}
    (hB : IsVonNBounded ℂ B) (hm : ∀ f ∈ B, Modes f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f ∈ B, ∀ x : ℝ,
      |x| ^ k * ‖iteratedDeriv n (logTheta a f) x‖ ≤ C := by
  let L : E →L[ℂ] E := shiftDeriv a
  let L' : E →L[ℂ] E := L ^ n
  have hL (f : E) : L' f = L^[n] f := by
    dsimp only [L']
    induction n generalizing f with
    | zero => rfl
    | succ n ih => rw [pow_succ', mul_apply_eq_comp, Function.iterate_succ_apply', ih]
  have hm' (f : E) (hf : Modes f) (j : ℕ) : Modes (L^[j] f) := by
    induction j with
    | zero => exact hf
    | succ j ih => rw [Function.iterate_succ_apply']; exact shiftDeriv_modes a ih
  obtain ⟨m, hm₁⟩ := exists_nat_ge (|a| + 1)
  obtain ⟨K, hK, hθ⟩ := rationalAdeleLF_uniform_theta_log_bound m (hB.image L')
  refine ⟨(k.factorial : ℝ) * K, by positivity, fun f hf x ↦ ?_⟩
  have hmL : Modes (L' f) := by rw [hL]; exact hm' f (hm f hf) n
  have h := hθ (L' f) ⟨f, hf, rfl⟩ hmL.1 hmL.2 (τ x)
  have hnorm : ideleClassNorm (τ x) = Real.exp x := by
    rw [rationalIdeleClassLogSection_apply, ideleClassNorm_mk, ideleNorm_logSection]
    rfl
  rw [hnorm, Real.log_exp] at h
  have hpol : |x| ^ k ≤ Real.exp |x| * k.factorial :=
    (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos k)).mp
      (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k)
  rw [iteratedDeriv_logTheta, ← hL, logTheta, logStageWeight, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hax : a * x ≤ |a| * |x| := by rw [← abs_mul]; exact le_abs_self _
  have hexp : Real.exp (|x| + a * x + (-(m : ℝ) * |x|)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hm₁) (abs_nonneg x)]
  have hθ' : ‖Θ (L' f) (τ x)‖ ≤ K * Real.exp (-(m : ℝ) * |x|) := by
    simpa only [rationalAdeleClassThetaLFLinear_apply] using h
  calc
    _ ≤ (Real.exp |x| * k.factorial) * (Real.exp (a * x) *
        (K * Real.exp (-(m : ℝ) * |x|))) := by gcongr
    _ = ((k.factorial : ℝ) * K) * Real.exp (|x| + a * x + (-(m : ℝ) * |x|)) := by
      rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hexp

private noncomputable def logThetaSchwartz (a : ℝ) (f : E) (hf : Modes f) : 𝓢(ℝ, ℂ) where
  toFun := logTheta a f
  smooth' := smooth_logTheta a f
  decay' k n := by
    obtain ⟨C, _, hC⟩ := weighted_logTheta_bound a k n
      (isVonNBounded_singleton (𝕜 := ℂ) f) (fun g hg ↦ (Set.mem_singleton_iff.mp hg).symm ▸ hf)
    refine ⟨C, fun x ↦ ?_⟩
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
      hC f rfl x

private theorem logThetaSchwartz_apply (a : ℝ) (f : E) (hf : Modes f) (x : ℝ) :
    logThetaSchwartz a f hf x = logTheta a f x := rfl

/-- The once-twisted radial profile of every global rational two-mode test
whose theta is norm-one invariant is in the genuine all-weight Schwartz stage.
The factor at weight `a` is the Schwartz profile with total weight `a + 1/2`. -/
public noncomputable def rationalThetaRadialWeightedProfiles :
    RationalThetaRadialInput →ₗ[ℂ] logWeightedProfiles univ where
  toFun f := ⟨rationalThetaRadialTwistedProfile (1 / 2) f, by
    refine ⟨?_, fun a ↦ ?_⟩
    · have h : rationalThetaRadialTwistedProfile (1 / 2) f = logTheta (1 / 2) f.val := by
        funext x
        rw [rationalThetaRadialTwistedProfile_apply, rationalThetaRadialProfile_apply, logTheta,
          logStageWeight, rationalAdeleClassThetaLFLinear_apply]
      rw [h]
      exact smooth_logTheta _ _
    have hf : Modes f.val := rationalThetaRadialInput_zero_modes f
    refine ⟨logThetaSchwartz (a.val + 1 / 2) f.val hf, fun x ↦ ?_⟩
    rw [logThetaSchwartz_apply, logTheta, rationalThetaRadialTwistedProfile_apply,
      rationalThetaRadialProfile_apply, rationalAdeleClassThetaLFLinear_apply]
    simp only [logStageWeight, add_mul, Real.exp_add, Complex.ofReal_mul, mul_assoc]⟩
  map_add' f g := by
    ext x
    change rationalThetaRadialTwistedProfile (1 / 2) (f + g) x =
      rationalThetaRadialTwistedProfile (1 / 2) f x + rationalThetaRadialTwistedProfile (1 / 2) g x
    rw [rationalThetaRadialTwistedProfile_apply, rationalThetaRadialTwistedProfile_apply,
      rationalThetaRadialTwistedProfile_apply, rationalThetaRadialProfile_add, mul_add]
  map_smul' c f := by
    ext x
    change rationalThetaRadialTwistedProfile (1 / 2) (c • f) x =
      c * rationalThetaRadialTwistedProfile (1 / 2) f x
    have h : rationalThetaRadialProfile (c • f) x = c * rationalThetaRadialProfile f x := by
      simpa only [rationalThetaRadialProfileLinear_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun (rationalThetaRadialProfileLinear.map_smul c f) x
    rw [rationalThetaRadialTwistedProfile_apply, rationalThetaRadialTwistedProfile_apply,
      h, mul_left_comm]

/-- The rational radial arrow with the manuscript's ambient weighted topology. -/
public noncomputable def rationalThetaRadialWeightedStage :
    RationalThetaRadialInput →ₗ[ℂ] logWeightedStage univ :=
  (logWeightedProfileMap univ).rangeRestrict.comp rationalThetaRadialWeightedProfiles

/-- Evaluating the coordinate of weight `a` gives exactly the once-twisted
profile followed by weight `a`, not its Hilbert closure. -/
public theorem rationalThetaRadialWeightedStage_apply (f : RationalThetaRadialInput)
    (a : (univ : Set ℝ)) (x : ℝ) :
    (rationalThetaRadialWeightedStage f).val a x =
      logStageWeight a.val x * rationalThetaRadialTwistedProfile (1 / 2) f x :=
  logWeightedProfileMap_apply _ _ _

/-- Uniform control of the actual stage seminorms across each bounded family
of radial inputs (the bound may depend on the weight and seminorm). This
asserts neither continuity nor closedness of the range. -/
public theorem rationalThetaRadialWeightedStage_uniform_seminorm
    (a : (univ : Set ℝ)) (k n : ℕ) {B : Set RationalThetaRadialInput}
    (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f ∈ B,
      SchwartzMap.seminorm ℂ k n ((rationalThetaRadialWeightedStage f).val a) ≤ C := by
  let i : RationalThetaRadialInput →L[ℂ] E :=
    { toLinearMap := (rationalThetaRadialInputSubmodule : Submodule ℂ E).subtype
      cont := continuous_subtype_val }
  have hm : ∀ f ∈ i '' B, Modes f := by
    rintro _ ⟨f, _, rfl⟩
    exact rationalThetaRadialInput_zero_modes f
  obtain ⟨C, hC, h⟩ := weighted_logTheta_bound (a.val + 1 / 2) k n (hB.image i) hm
  refine ⟨C, hC, fun f hf ↦ SchwartzMap.seminorm_le_bound' ℂ k n _ hC fun x ↦ ?_⟩
  have hfun : (((rationalThetaRadialWeightedStage f).val a) : ℝ → ℂ) =
      logTheta (a.val + 1 / 2) f.val := by
    funext t
    rw [rationalThetaRadialWeightedStage_apply, logTheta, rationalThetaRadialTwistedProfile_apply,
      rationalThetaRadialProfile_apply, rationalAdeleClassThetaLFLinear_apply]
    simp only [logStageWeight, add_mul, Real.exp_add, Complex.ofReal_mul, mul_assoc]
  rw [hfun]
  exact h (i f) ⟨f, hf, rfl⟩ x

/-- The weighted linear realization kills exactly the original class-theta
kernel on radial two-mode inputs. -/
public theorem rationalThetaRadialWeightedStage_eq_zero_iff (f : RationalThetaRadialInput) :
    rationalThetaRadialWeightedStage f = 0 ↔ Θ f.val = 0 := by
  constructor
  · intro h
    funext d
    let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
    let x := Real.log (ideleClassNorm d)
    have hval := congrArg (fun F : logWeightedStage univ ↦ F.val a x) h
    have hx : logStageWeight a.val x * rationalThetaRadialTwistedProfile (1 / 2) f x = 0 :=
      (rationalThetaRadialWeightedStage_apply f a x).symm.trans (by simpa using hval)
    have hne (b : ℝ) : (Real.exp (b * x) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos (b * x)).ne'
    rw [logStageWeight, rationalThetaRadialTwistedProfile_apply] at hx
    have h₀ := (mul_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (hne _))).resolve_left (hne _)
    rw [rationalAdeleClassThetaLFLinear_apply, rationalThetaRadialProfile_class]
    exact h₀
  · intro h
    apply Subtype.ext
    funext a
    ext x
    rw [rationalThetaRadialWeightedStage_apply, rationalThetaRadialTwistedProfile_apply,
      rationalThetaRadialProfile_apply, ← rationalAdeleClassThetaLFLinear_apply, h]
    simp

end Masullo
