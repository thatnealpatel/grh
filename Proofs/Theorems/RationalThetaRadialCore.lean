module

public import Lemmas.RationalAdeleLFStageOperators
public import Theorems.RationalAdeleClassThetaDerivative
public import Theorems.RationalAdeleLFThetaTails
public import Theorems.RationalIdeleFiniteUnitFactor
public import Lemmas.RationalLocalNormShell
public import Lemmas.InteriorLogJet
import Lemmas.HardySobolevWeight
import Lemmas.SinglePlaceNorm
import Lemmas.RationalAdeleAffineIntegral
import Mathlib.Data.Finset.NoncommProd

/-! # The radial two-mode theta core over `ℚ`

The source of (10.1.1.1)–(10.1.1.3), p. 434, consists of theta functions of
Schwartz–Bruhat tests with the spatial and Fourier zero modes removed. We
restrict to the trivial norm-one isotype as in (10.2.1.2), p. 439. Our
representation uses all rational adelic Schwartz LF tests whose theta is
norm-one invariant, not just unramified tensors. We do not identify the
manuscript's topological coinvariants, their topology, or their closure
with this model.
-/

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap ComplexConjugate

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "σ" => fun x : ℝ ↦ rationalIdeleLogSection (Multiplicative.ofAdd x)
local notation "τ" => fun x : ℝ ↦ rationalIdeleClassLogSection (Multiplicative.ofAdd x)
local notation "Θ[" f "]" => rationalAdeleClassTheta (Subtype.val (RationalAdeleSchwartzLF.toUnion f))
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "FinA" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "P[" v "]" => ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)

/-- Realize a test from any finite support and invariance stage of the form
`K/H` used in the proof of Proposition 2.1.3.2, pp. 69–70. Only openness of
`H` and compactness of `K` are needed for the cofinality argument. -/
public theorem exists_rationalAdeleLF_of_compactOpenStage (f : A → ℂ)
    (H K : AddSubgroup FinA) (hH : IsOpen (H : Set FinA)) (hK : IsCompact (K : Set FinA))
    (hzero : ∀ x : A, x.2 ∉ K → f x = 0)
    (hinv : ∀ (x : A) (z : FinA), z ∈ H → f (x + rationalAdeleAt 0 z) = f x)
    (hreal : ∀ z : FinA, ∃ b : 𝓢(ℝ, ℂ), ∀ t, b t = f (rationalAdeleAt t z)) :
    ∃ F : E, F.toUnion.val = f := by
  obtain ⟨M, hM, hsubH, hsubK⟩ := exists_rationalAdeleBoxStage_cofinal H K hH hK
  have hf : f ∈ rationalAdeleSchwartzStage M :=
    ⟨fun x hx ↦ hzero x (fun hxK ↦ hx (hsubK hxK)),
      fun x z hz ↦ hinv x _ (hsubH ⟨z, hz, rfl⟩), hreal⟩
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp (rationalAdeleSchwartzStage_le_union hM hf)
  let e := rationalAdeleStageCoordinates (rationalAdeleFactorialLevel_pos n)
  refine ⟨rationalAdeleLFAssembly n (e ⟨f, hn⟩), ?_⟩
  rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val]
  change (e.symm (e ⟨f, hn⟩)).val = f
  rw [e.symm_apply_apply]

private theorem norm_section (x : ℝ) : ideleClassNorm (τ x) = Real.exp x := by
  change ideleClassNorm (rationalIdeleClassLogSection _) = _
  rw [rationalIdeleClassLogSection_apply, ideleClassNorm_mk, ideleNorm_logSection]
  rfl

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]

private theorem theta_summable (f : E) (k : J) :
    Summable (fun q : ℚˣ ↦ f.toUnion.val ((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q * k : J) : A)) := by
  obtain ⟨_, b, a, g, hf⟩ := exists_rationalAdeleLF_eq_boxSum f
  rw [hf]
  exact (summable_norm_rationalAdeleBoxSum_theta Finset.univ (fun _ ↦ 1) b a g k).1.of_norm

private theorem theta_add (f g : E) (d : C) : Θ[f + g] d = Θ[f] d + Θ[g] d := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
  simpa only [rationalAdeleClassTheta_mk, rationalAdeleTheta, map_add, Submodule.coe_add,
    Pi.add_apply] using (theta_summable f k).tsum_add (theta_summable g k)

omit [MeasurableSpace A] [BorelSpace A] in
private theorem theta_smul (c : ℂ) (f : E) (d : C) : Θ[c • f] d = c • Θ[f] d := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
  simp only [rationalAdeleClassTheta_mk, rationalAdeleTheta, map_smul, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, tsum_mul_left]


/-- Class theta on represented tests, before restriction to the radial sector. -/
public noncomputable def rationalAdeleClassThetaLFLinear : E →ₗ[ℂ] (C → ℂ) where
  toFun f := Θ[f]
  map_add' f g := funext (theta_add f g)
  map_smul' c f := funext (theta_smul c f)

@[simp] public theorem rationalAdeleClassThetaLFLinear_apply (f : E) :
    rationalAdeleClassThetaLFLinear f = Θ[f] := by
  unfold rationalAdeleClassThetaLFLinear
  rfl

/-- All represented two-mode tests whose theta lies in the trivial norm-one isotype.
Invariance is imposed on class theta, not on the test itself. -/
public noncomputable def rationalThetaRadialInputSubmodule : Submodule ℂ E where
  carrier := {f | f.toUnion.val 0 = 0 ∧ rationalAdeleFourier f.toUnion.val 0 = 0 ∧
    ∀ (k : rationalIdeleClassNormOne) (d : C), Θ[f] ((k : C) * d) = Θ[f] d}
  zero_mem' := by
    change (0 : E).toUnion.val 0 = 0 ∧ rationalAdeleFourier (0 : E).toUnion.val 0 = 0 ∧ _
    refine ⟨by simp, ?_, ?_⟩
    · rw [← rationalAdeleLFFourier_eq, map_zero, map_zero, Submodule.coe_zero, Pi.zero_apply]
    intro k d
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨i, hi⟩ := QuotientGroup.mk_surjective ((k : C) * QuotientGroup.mk j)
    rw [← hi]
    simp [rationalAdeleTheta]
  add_mem' := by
    rintro f g ⟨hf, hfF, hfi⟩ ⟨hg, hgF, hgi⟩
    refine ⟨?_, ?_, fun k d ↦ by rw [theta_add, theta_add, hfi, hgi]⟩
    · simp only [map_add, Submodule.coe_add, Pi.add_apply, hf, hg, add_zero]
    · rw [← rationalAdeleLFFourier_eq, map_add, map_add, Submodule.coe_add, Pi.add_apply,
        rationalAdeleLFFourier_eq, rationalAdeleLFFourier_eq, hfF, hgF, add_zero]
  smul_mem' := by
    rintro c f ⟨hf, hfF, hfi⟩
    refine ⟨?_, ?_, fun k d ↦ by rw [theta_smul, theta_smul, hfi]⟩
    · simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, hf, smul_zero]
    · rw [← rationalAdeleLFFourier_eq, map_smul, map_smul, Submodule.coe_smul, Pi.smul_apply,
        rationalAdeleLFFourier_eq, hfF, smul_zero]

public abbrev RationalThetaRadialInput := ↥rationalThetaRadialInputSubmodule

public theorem mem_rationalThetaRadialInputSubmodule (f : E) :
    f ∈ rationalThetaRadialInputSubmodule ↔
      f.toUnion.val 0 = 0 ∧ rationalAdeleFourier f.toUnion.val 0 = 0 ∧
        ∀ (k : rationalIdeleClassNormOne) (d : C), Θ[f] ((k : C) * d) = Θ[f] d := by
  unfold rationalThetaRadialInputSubmodule
  rfl

/-- Class theta restricted to the canonical log section. -/
public noncomputable def rationalThetaRadialProfile (f : RationalThetaRadialInput) (x : ℝ) : ℂ :=
  Θ[f.val] (τ x)

public theorem rationalThetaRadialProfile_apply (f : RationalThetaRadialInput) (x : ℝ) :
    rationalThetaRadialProfile f x = Θ[f.val] (τ x) := by
  unfold rationalThetaRadialProfile
  rfl

/-- The once-twisted radial theta profile in the manuscript's convention. -/
public noncomputable def rationalThetaRadialTwistedProfile (a : ℝ) (f : RationalThetaRadialInput)
    (x : ℝ) : ℂ :=
  (Real.exp (a * x) : ℂ) * rationalThetaRadialProfile f x

omit [MeasurableSpace A] [BorelSpace A] in
/-- Theta invariance under the norm-one subgroup is exactly descent to the norm.
This applies to any function on rational idele classes, in particular to theta. -/
public theorem rationalIdeleClass_normOne_invariant_iff (F : C → ℂ) :
    (∀ (k : rationalIdeleClassNormOne) (d : C), F ((k : C) * d) = F d) ↔
    (∀ d : C, F d = F (τ (Real.log (ideleClassNorm d)))) := by
  constructor
  · intro h d
    let x := Real.log (ideleClassNorm d)
    have hnorm : ideleClassNorm (τ x) = ideleClassNorm d :=
      (norm_section x).trans (Real.exp_log (ideleClassNorm_pos d))
    let k : rationalIdeleClassNormOne := ⟨d * (τ x)⁻¹, by
      rw [mem_rationalIdeleClassNormOne, map_mul, map_inv, hnorm,
        mul_inv_cancel₀ (ideleClassNorm_pos d).ne']⟩
    simpa only [k, inv_mul_cancel_right] using h k (τ x)
  · intro h k d
    have hk : ideleClassNorm (k : C) = 1 :=
      (mem_rationalIdeleClassNormOne _).mp k.property
    rw [h ((k : C) * d), h d, map_mul, hk, one_mul]

omit [MeasurableSpace A] [BorelSpace A] in
/-- Check the radial condition using exactly the rational finite-unit classes. -/
public theorem rationalIdeleClass_normOne_invariant_iff_finiteUnits (F : C → ℂ) :
    (∀ (k : rationalIdeleClassNormOne) (d : C), F ((k : C) * d) = F d) ↔
      (∀ (u : RationalFiniteUnits) (d : C), F ((rationalFiniteUnitClass u : C) * d) = F d) := by
  refine ⟨fun h u ↦ h (rationalFiniteUnitClass u), fun h k ↦ ?_⟩
  obtain ⟨u, hu⟩ := rationalFiniteUnitClassEquiv.surjective k
  rw [rationalFiniteUnitClassEquiv_apply] at hu
  rw [← hu]
  exact h u

public theorem rationalThetaRadialProfile_class (f : RationalThetaRadialInput) (d : C) :
    Θ[f.val] d = rationalThetaRadialProfile f (Real.log (ideleClassNorm d)) :=
  (rationalIdeleClass_normOne_invariant_iff _).mp f.property.2.2 d

public theorem continuous_rationalThetaRadialProfile (f : RationalThetaRadialInput) :
    Continuous (rationalThetaRadialProfile f) :=
  (continuous_rationalAdeleClassTheta_LF f.val).comp
    ((map_continuous rationalIdeleClassLogSection).comp continuous_id)

public theorem continuous_rationalThetaRadialTwistedProfile (a : ℝ) (f : RationalThetaRadialInput) :
    Continuous (rationalThetaRadialTwistedProfile a f) :=
  (Complex.continuous_ofReal.comp (by fun_prop)).mul (continuous_rationalThetaRadialProfile f)

/-- The algebraic range includes the profile of every represented radial test. -/
public noncomputable def rationalThetaRadialProfileLinear : RationalThetaRadialInput →ₗ[ℂ] (ℝ → ℂ) where
  toFun := rationalThetaRadialProfile
  map_add' f g := funext fun x ↦ theta_add f.val g.val (τ x)
  map_smul' c f := funext fun x ↦ theta_smul c f.val (τ x)

/-- The log profile map is the linear map obtained by restricting class theta. -/
@[simp] public theorem rationalThetaRadialProfileLinear_apply (f : RationalThetaRadialInput) :
    rationalThetaRadialProfileLinear f = rationalThetaRadialProfile f := by
  rw [rationalThetaRadialProfileLinear, LinearMap.coe_mk, AddHom.coe_mk]

@[simp] public theorem rationalThetaRadialProfile_add (f g : RationalThetaRadialInput) (x : ℝ) :
    rationalThetaRadialProfile (f + g) x = rationalThetaRadialProfile f x + rationalThetaRadialProfile g x := by
  simpa only [rationalThetaRadialProfileLinear_apply, Pi.add_apply] using
    congrFun (rationalThetaRadialProfileLinear.map_add f g) x

@[simp] public theorem rationalThetaRadialProfile_sub (f g : RationalThetaRadialInput) (x : ℝ) :
    rationalThetaRadialProfile (f - g) x = rationalThetaRadialProfile f x - rationalThetaRadialProfile g x := by
  simpa only [rationalThetaRadialProfileLinear_apply, Pi.sub_apply] using
    congrFun (rationalThetaRadialProfileLinear.map_sub f g) x

/-- The represented, uncompleted radial theta core on the log line. -/
public noncomputable def rationalThetaRadialCore : Submodule ℂ (ℝ → ℂ) :=
  rationalThetaRadialProfileLinear.range

/-- Positive real dilation of an arbitrary rational Schwartz LF test. The
weighted stage operator already supplies the realization at the original stage. -/
public noncomputable def rationalAdeleLFLogTranslate (s : ℝ) (f : E) : E :=
  (Real.exp (-s) : ℂ) • rationalAdeleLFWeightedInverseDilation (-s) f

omit [MeasurableSpace A] [BorelSpace A] in
public theorem rationalAdeleLFLogTranslate_apply (s : ℝ) (f : E) (z : A) :
    (rationalAdeleLFLogTranslate s f).toUnion.val z = f.toUnion.val ((σ s : A) * z) := by
  rw [rationalAdeleLFLogTranslate, map_smul, Submodule.coe_smul, Pi.smul_apply,
    rationalAdeleLFWeightedInverseDilation_apply, neg_neg, Complex.real_smul, smul_eq_mul,
    ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    Complex.ofReal_one, one_mul]

/-- The two zero modes transform by `1` and `exp(-s)` respectively. -/
public theorem rationalAdeleLFLogTranslate_zero_modes (s : ℝ) (f : E) :
    (rationalAdeleLFLogTranslate s f).toUnion.val 0 = f.toUnion.val 0 ∧
      rationalAdeleFourier (rationalAdeleLFLogTranslate s f).toUnion.val 0 =
        Real.exp (-s) • rationalAdeleFourier f.toUnion.val 0 := by
  refine ⟨by rw [rationalAdeleLFLogTranslate_apply, mul_zero], ?_⟩
  simp only [rationalAdeleFourier, mul_zero, AddChar.map_zero_eq_one, map_one, mul_one,
    rationalAdeleLFLogTranslate_apply]
  rw [integral_rationalAdele_affine (fun z ↦ f.toUnion.val ((σ s : A) * z)) 0 (σ (-s))]
  have h : σ (-s) = (σ s)⁻¹ := by
    change rationalIdeleLogSection ((Multiplicative.ofAdd s)⁻¹) = _
    exact map_inv rationalIdeleLogSection _
  rw [h]
  simp only [zero_add, ← mul_assoc, Units.mul_inv, one_mul, map_inv]
  change (ideleNorm (rationalIdeleLogSection (Multiplicative.ofAdd s)))⁻¹ • _ = _
  rw [ideleNorm_logSection, Real.exp_neg]
  rfl

omit [MeasurableSpace A] [BorelSpace A] in
/-- Theta intertwines positive real dilation with multiplication by the
idele class of the real section. This holds before taking the radial part. -/
public theorem rationalAdeleClassTheta_LFLogTranslate (s : ℝ) (f : E) (d : C) :
    Θ[rationalAdeleLFLogTranslate s f] d = Θ[f] (τ s * d) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
  change Θ[rationalAdeleLFLogTranslate s f] (QuotientGroup.mk k) =
    Θ[f] (rationalIdeleClassLogSection (Multiplicative.ofAdd s) * QuotientGroup.mk k)
  rw [rationalIdeleClassLogSection_apply, ← QuotientGroup.mk_mul]
  simp only [rationalAdeleClassTheta_mk, rationalAdeleTheta, rationalAdeleLFLogTranslate_apply]
  congr 1
  funext q
  simp only [Units.val_mul]
  ac_rfl

/-- Translation of log profiles is represented by dilation of two-mode tests;
the translated theta still lies in the trivial norm-one isotype. -/
public noncomputable def rationalThetaRadialInputTranslate (s : ℝ) (f : RationalThetaRadialInput) :
    RationalThetaRadialInput := by
  refine ⟨rationalAdeleLFLogTranslate s f.val, ?_⟩
  obtain ⟨h₀, hF⟩ := rationalAdeleLFLogTranslate_zero_modes s f.val
  refine ⟨h₀.trans f.property.1, by rw [hF, f.property.2.1, smul_zero], fun k d ↦ ?_⟩
  rw [rationalAdeleClassTheta_LFLogTranslate, rationalAdeleClassTheta_LFLogTranslate]
  have h : τ s * ((k : C) * d) = (k : C) * (τ s * d) := mul_left_comm (τ s) (k : C) d
  rw [h]
  exact f.property.2.2 k (τ s * d)

public noncomputable def rationalThetaRadialInputTranslateAdd (s : ℝ) :
    RationalThetaRadialInput →+ RationalThetaRadialInput := by
  let D := rationalThetaRadialInputTranslate s
  have hadd (f g : RationalThetaRadialInput) : D (f + g) = D f + D g := by
    apply Subtype.ext
    change rationalAdeleLFLogTranslate s (f.val + g.val) =
      rationalAdeleLFLogTranslate s f.val + rationalAdeleLFLogTranslate s g.val
    simp only [rationalAdeleLFLogTranslate, map_add, smul_add]
  exact { toFun := D, map_add' := hadd, map_zero' := by simpa using hadd 0 0 }

@[simp] public theorem rationalThetaRadialInputTranslateAdd_apply (s : ℝ)
    (f : RationalThetaRadialInput) :
    rationalThetaRadialInputTranslateAdd s f = rationalThetaRadialInputTranslate s f := by
  unfold rationalThetaRadialInputTranslateAdd
  rfl

@[simp] public theorem rationalThetaRadialProfile_translate (s : ℝ) (f : RationalThetaRadialInput)
    (x : ℝ) : rationalThetaRadialProfile (rationalThetaRadialInputTranslate s f) x =
      rationalThetaRadialProfile f (x + s) := by
  unfold rationalThetaRadialProfile
  change Θ[rationalAdeleLFLogTranslate s f.val] (τ x) = Θ[f.val] (τ (x + s))
  rw [rationalAdeleClassTheta_LFLogTranslate, mul_comm (τ s) (τ x)]
  exact congrArg (Θ[f.val]) (map_mul rationalIdeleClassLogSection
    (Multiplicative.ofAdd x) (Multiplicative.ofAdd s)).symm

public theorem rationalThetaRadialCore_translate {F : ℝ → ℂ} (hF : F ∈ rationalThetaRadialCore)
    (s : ℝ) : (fun x ↦ F (x + s)) ∈ rationalThetaRadialCore := by
  rcases hF with ⟨f, rfl⟩
  exact ⟨rationalThetaRadialInputTranslate s f, funext (rationalThetaRadialProfile_translate s f)⟩

section Tails

variable [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

/-- Individual two-mode rational adelic theta profiles have arbitrary
exponential decay in both log directions, hence in particular on the right. -/
public theorem rationalThetaRadialProfile_log_bound (f : RationalThetaRadialInput) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ,
      ‖rationalThetaRadialProfile f x‖ ≤ K * Real.exp (-(m : ℝ) * |x|) := by
  obtain ⟨K, hK, ht⟩ := rationalAdeleLF_uniform_theta_log_bound m
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) f.val)
  refine ⟨K, hK, fun x ↦ ?_⟩
  simpa only [rationalThetaRadialProfile, norm_section, Real.log_exp] using
    ht f.val (Set.mem_singleton _) f.property.1 f.property.2.1 (τ x)

/-- The full radial core embeds in the symmetric weighted log-line `L²`; no
estimate uniform over LF stages is needed for this membership. -/
public theorem memLp_rationalThetaRadialProfile_weighted (f : RationalThetaRadialInput)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    MemLp (fun x : ℝ ↦ (symmetricStripWeightRoot α s x : ℂ) * rationalThetaRadialProfile f x)
      2 volume := by
  have hc := continuous_rationalThetaRadialProfile f
  have hw := (Complex.continuous_ofReal.comp (continuous_symmetricStripWeightRoot α s)).mul hc
  apply (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).2
  obtain ⟨N, hN⟩ := exists_nat_ge (max |(-α)| |α| + s / 2 + 1)
  obtain ⟨K, _, ht⟩ := rationalThetaRadialProfile_log_bound f N
  have hi := integrable_hardySobolevWeight_mul_norm_sq hc hs (by linarith) ht
  convert hi using 1
  ext x
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (symmetricStripWeightRoot_pos α s x).le, mul_pow, mul_comm]
  have h := symmetricStripWeightRoot_mul_exp_sq hα s 0 x
  simp only [zero_mul, Real.exp_zero, mul_one, zero_add] at h
  rw [h, ← mul_assoc]

/-- The canonical weighted `L²(dx)` vector of a radial theta input, on the zero line. -/
public noncomputable def rationalThetaRadialWeightedLog {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (f : RationalThetaRadialInput) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_rationalThetaRadialProfile_weighted f hα hs).toLp _

public theorem rationalThetaRadialWeightedLog_ae {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (f : RationalThetaRadialInput) :
    (rationalThetaRadialWeightedLog hα hs f : ℝ → ℂ) =ᵐ[volume]
      fun x ↦ (symmetricStripWeightRoot α s x : ℂ) * rationalThetaRadialProfile f x :=
  (memLp_rationalThetaRadialProfile_weighted f hα hs).coeFn_toLp

end Tails

section Uniformizer

omit [MeasurableSpace A] [BorelSpace A]

/-- Embed the rational prime as a uniformizer at its own place, with all
other coordinates (including the real coordinate) equal to one. -/
public noncomputable def rationalThetaRadialUniformizer (v : V) : J :=
  IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (rationalLocalUniformizer v)

/-- The finite uniformizer decreases the idelic norm by the factor `1/p`. -/
public theorem ideleNorm_rationalThetaRadialUniformizer (v : V) :
    ideleNorm (rationalThetaRadialUniformizer v) = (P[v] : ℝ)⁻¹ := by
  have h : rationalLocalUniformizer v ∈ rationalLocalNormShell v 1 := by
    rw [RationalLocalNormShell.eq_translate]
    exact ⟨1, ⟨1, map_one _⟩, by simp⟩
  change ‖(rationalLocalUniformizer v : v.adicCompletion ℚ)‖ = (P[v] : ℝ)⁻¹ ^ (1 : ℤ) at h
  rw [rationalThetaRadialUniformizer, ideleNorm_apply, norm_idele_ofAdicCompletion]
  simpa only [zpow_one] using h

/-- The principal multiplier clearing the uniformizer has positive real value
`1/p`; the resulting representative has that real coordinate and all finite
coordinates integral units. -/
public theorem rationalThetaRadialUniformizer_principal_clearing (v : V) :
    ∃ r : ℚˣ, ((r : ℚ) : ℝ) = (P[v] : ℝ)⁻¹ ∧
      rationalIdeleReal (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * rationalThetaRadialUniformizer v) =
        (P[v] : ℝ)⁻¹ ∧
      ∀ w : V, Valued.v (((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r *
        rationalThetaRadialUniformizer v : J) : A).2 w) = 1 := by
  obtain ⟨r, hr, hf⟩ :=
    exists_rational_principal_mul_norm_section (rationalThetaRadialUniformizer v)
  rw [ideleNorm_rationalThetaRadialUniformizer] at hr
  have hreal : rationalIdeleReal (rationalThetaRadialUniformizer v) = 1 := by
    unfold rationalIdeleReal
    exact map_one _
  have hq := hr
  rw [rationalIdeleReal_principal_mul, hreal, mul_one] at hq
  exact ⟨r, hq, hr, hf⟩

end Uniformizer

/-- Left translation of class theta by the uniformizer evaluates theta at
its inverse, hence gives the positive log shift `x + log p`. -/
public theorem rationalThetaRadialProfile_uniformizer (v : V) (f : RationalThetaRadialInput)
    (d : C) :
    Θ[f.val] ((QuotientGroup.mk (rationalThetaRadialUniformizer v) : C)⁻¹ * d) =
      rationalThetaRadialProfile f (Real.log (ideleClassNorm d) + Real.log (P[v] : ℝ)) := by
  rw [rationalThetaRadialProfile_class, map_mul, map_inv, ideleClassNorm_mk,
    ideleNorm_rationalThetaRadialUniformizer, inv_inv,
    Real.log_mul (RationalLocalNormShell.prime_pos v).ne' (ideleClassNorm_pos d).ne', add_comm]

/-- On the zero line the log difference `Dₚ` is identity minus left translation
by the finite uniformizer, with no scalar or norm twist. -/
public theorem rationalThetaRadialProfile_primeDifference (v : V) (f : RationalThetaRadialInput)
    (x : ℝ) :
    Θ[f.val] (τ x) -
        Θ[f.val] ((QuotientGroup.mk (rationalThetaRadialUniformizer v) : C)⁻¹ * τ x) =
      rationalThetaRadialProfile f x - rationalThetaRadialProfile f (x + Real.log (P[v] : ℝ)) := by
  rw [rationalThetaRadialProfile_uniformizer, norm_section, Real.log_exp]
  rfl

section PrimeDifferences

local notation "R" => RationalThetaRadialInput

private noncomputable def radialTranslateEnd (d : ℝ) : AddMonoid.End R :=
  rationalThetaRadialInputTranslateAdd d

private theorem translate_commute (d e : ℝ) :
    Commute (radialTranslateEnd d) (radialTranslateEnd e) := by
  apply AddMonoidHom.ext
  intro f
  apply Subtype.ext
  apply RationalAdeleSchwartzLF.ext
  funext z
  change (rationalAdeleLFLogTranslate d (rationalAdeleLFLogTranslate e f.val)).toUnion.val z =
    (rationalAdeleLFLogTranslate e (rationalAdeleLFLogTranslate d f.val)).toUnion.val z
  simp only [rationalAdeleLFLogTranslate_apply]
  ac_rfl

/-- The represented prime difference, before any weight or cutoff. -/
public noncomputable def rationalThetaRadialPrimeDifference (v : V) : AddMonoid.End R :=
  1 - radialTranslateEnd (Real.log (P[v] : ℝ))

public theorem rationalThetaRadialPrimeDifference_apply (v : V) (f : R) :
    rationalThetaRadialPrimeDifference v f =
      f - rationalThetaRadialInputTranslateAdd (Real.log (P[v] : ℝ)) f := by
  unfold rationalThetaRadialPrimeDifference radialTranslateEnd
  rfl

private theorem translate_commute_primeDifference (d : ℝ) (v : V) :
    Commute (radialTranslateEnd d) (rationalThetaRadialPrimeDifference v) :=
  (Commute.one_right _).sub_right (translate_commute d _)

public theorem rationalThetaRadialPrimeDifference_commute (v w : V) :
    Commute (rationalThetaRadialPrimeDifference v) (rationalThetaRadialPrimeDifference w) :=
  (Commute.one_left _).sub_left (translate_commute_primeDifference _ _)

/-- The order-independent product of the prime differences over a finite set of places.
It acts on radial inputs and therefore realizes the successive differences of their raw theta. -/
public noncomputable def rationalThetaRadialPrimeDifferences (P : Finset V) : AddMonoid.End R :=
  P.noncommProd rationalThetaRadialPrimeDifference fun v _ w _ _ ↦
    rationalThetaRadialPrimeDifference_commute v w

@[simp] public theorem rationalThetaRadialPrimeDifferences_empty :
    rationalThetaRadialPrimeDifferences ∅ = 1 :=
  Finset.noncommProd_empty _ _

public theorem rationalThetaRadialPrimeDifferences_insert [DecidableEq V] {P : Finset V}
    {v : V} (hv : v ∉ P) :
    rationalThetaRadialPrimeDifferences (insert v P) =
      rationalThetaRadialPrimeDifference v * rationalThetaRadialPrimeDifferences P :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ hv

public theorem rationalThetaRadialPrimeDifferences_insert' [DecidableEq V] {P : Finset V}
    {v : V} (hv : v ∉ P) :
    rationalThetaRadialPrimeDifferences (insert v P) =
      rationalThetaRadialPrimeDifferences P * rationalThetaRadialPrimeDifference v :=
  Finset.noncommProd_insert_of_notMem' _ _ _ _ hv

public theorem rationalThetaRadialPrimeDifferences_commute_translate (P : Finset V) (d : ℝ) :
    Function.Commute (rationalThetaRadialPrimeDifferences P)
      (rationalThetaRadialInputTranslateAdd d) := by
  have h : Commute (radialTranslateEnd d) (rationalThetaRadialPrimeDifferences P) :=
    Finset.noncommProd_commute _ _ _ _ fun v _ ↦ translate_commute_primeDifference d v
  exact fun f ↦ DFunLike.congr_fun h.symm.eq f

@[simp] public theorem rationalThetaRadialPrimeDifferences_class_empty (f : R) (g : C) :
    Θ[(rationalThetaRadialPrimeDifferences ∅ f).val] g = Θ[f.val] g := by
  rw [rationalThetaRadialPrimeDifferences_empty, AddMonoid.End.coe_one, id_eq]

/-- The represented product inserts the actual inverse-uniformizer difference of the
raw class theta, without a scalar or weight. -/
public theorem rationalThetaRadialPrimeDifferences_class_insert [DecidableEq V] {P : Finset V}
    {v : V} (hv : v ∉ P) (f : R) (g : C) :
    Θ[(rationalThetaRadialPrimeDifferences (insert v P) f).val] g =
      Θ[(rationalThetaRadialPrimeDifferences P f).val] g -
        Θ[(rationalThetaRadialPrimeDifferences P f).val] (
          (QuotientGroup.mk (rationalThetaRadialUniformizer v) : C)⁻¹ * g) := by
  rw [rationalThetaRadialPrimeDifferences_insert hv, AddMonoid.End.coe_mul, Function.comp_apply,
    rationalThetaRadialPrimeDifference_apply, rationalThetaRadialProfile_class,
    rationalThetaRadialProfile_sub, rationalThetaRadialInputTranslateAdd_apply,
    rationalThetaRadialProfile_translate, rationalThetaRadialProfile_uniformizer,
    rationalThetaRadialProfile_class]

end PrimeDifferences

end Masullo
