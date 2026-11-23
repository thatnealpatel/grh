module

public import Theorems.IdeleClassCharacterComponent
public import Theorems.IdeleClassGaussianContinuation
public import Mathlib.Analysis.Meromorphic.Order

/-! # The completed Hecke zero divisor in an open centered strip

Use the positive norm power in (3.2.1.1)–(2) and the unshifted zero
quasi-character `c` of (12.5.1.3). Its Mellin term in that formula is at
`c |·|⁻¹/²`, not at `c`. The log-norm splitting chooses one unitary base
character per norm-one restriction, and the Gaussian continuation is
normalized on `Re(s) > 1`.
-/

open Filter IsDedekindDomain MeasureTheory NumberField
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)
local notation "I₁" => ideleNormOne (K := K)
local notation "Ω" => HeckeCharacter (𝓞 K) K

private theorem exists_completedHeckeContinuation (χ : Ω) (hχ : ∀ c, ‖χ c‖ = 1) :
    ∃ L : ℂ → ℂ, Meromorphic L ∧ ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ hχ s := by
  let : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ := fun _ ↦ borel _
  let : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ := fun _ ↦ ⟨rfl⟩
  let : MeasurableSpace C := borel _
  let : BorelSpace C := ⟨rfl⟩
  let : MeasurableSpace C₁ := borel _
  let : BorelSpace C₁ := ⟨rfl⟩
  let : MeasurableSpace I₁ := borel _
  let : BorelSpace I₁ := ⟨rfl⟩
  let : MeasurableSpace I := borel _
  let : BorelSpace I := ⟨rfl⟩
  let : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ := fun _ ↦ borel _
  let : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ := fun _ ↦ ⟨rfl⟩
  let : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ :=
    fun _ ↦ borel _
  let : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ := fun _ ↦ ⟨rfl⟩
  have hr : Function.Surjective (ideleIdealClassNormOne (K := K)) :=
    fun g ↦ by
      obtain ⟨x, hx⟩ := ideleIdealClass_normOne_surjective g
      exact ⟨x, (ideleIdealClassNormOne_apply x).trans hx⟩
  choose r hr using hr
  obtain ⟨T, ν, F, E, μ, lam, h⟩ :=
    exists_completedHeckeEulerProduct_gaussianContinuation χ hχ w₀ r hr
  dsimp only at h
  obtain ⟨_, _, _, _, _, _, _, _, hM, _, _, hL, _⟩ := h
  exact ⟨_, hM, hL⟩

private noncomputable def normOneProjection : C →ₜ* C₁ :=
  let e := (ideleClassLogSplit (ideleClassLogSection (w₀ : InfinitePlace K))
    (ideleClassLogNorm_section w₀)).symm
  (ContinuousMonoidHom.snd _ _).comp ⟨e.toMonoidHom, e.continuous⟩

/-- Extend the restriction to norm-one classes trivially on the chosen log-norm section. -/
public noncomputable def ideleClassHeckeBase (χ : Ω) : Ω :=
  χ.comp (ContinuousMonoidHom.comp ⟨Subgroup.subtype C₁, continuous_subtype_val⟩ normOneProjection)

public theorem ideleClassHeckeBase_unitary (χ : Ω) (c : C) : ‖ideleClassHeckeBase χ c‖ = 1 := by
  change ‖χ (normOneProjection c : C)‖ = _
  rw [← ideleClassNormOneRestriction_apply]
  exact Circle.norm_coe _

private noncomputable def radialPart (χ : Ω) : Ω :=
  χ.comp ((ideleClassLogSection (w₀ : InfinitePlace K)).comp ideleClassLogNorm)

private theorem exists_normExponent (χ : Ω) : ∃ s : ℂ, radialPart χ = ideleClassNormPower s :=
  (ideleClassNormPower_existsUnique (radialPart χ) (fun c ↦ by
    have hn : ideleClassLogNorm (c : C) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [ideleClassLogNorm_apply, (mem_ideleClassNormOne _).mp c.property, Real.log_one]
      rfl
    change χ (ideleClassLogSection w₀ (ideleClassLogNorm (c : C))) = _
    rw [hn, map_one, map_one])).exists

/-- The unique complex exponent of the restriction to the chosen log-norm section. -/
public noncomputable def ideleClassNormExponent (χ : Ω) : ℂ := (exists_normExponent χ).choose

public theorem ideleClass_eq_heckeBase_mul_normPower (χ : Ω) :
    χ = ideleClassHeckeBase χ * ideleClassNormPower (ideleClassNormExponent χ) := by
  have hs : radialPart χ = ideleClassNormPower (ideleClassNormExponent χ) :=
    (exists_normExponent χ).choose_spec
  rw [← hs]
  ext c
  change χ c = χ (normOneProjection c : C) * χ (ideleClassLogSection w₀ (ideleClassLogNorm c))
  rw [← map_mul]
  apply congrArg χ
  let s := ideleClassLogSection (w₀ : InfinitePlace K)
  let e := ideleClassLogSplit s (ideleClassLogNorm_section w₀)
  have hfst : (e.symm c).1 = ideleClassLogNorm c := by
    dsimp only [e]
    rw [ideleClassLogSplit_symm]
  calc
    c = e (e.symm c) := (e.apply_symm_apply c).symm
    _ = s (e.symm c).1 * ((e.symm c).2 : C) := ideleClassLogSplit_apply _ _ _
    _ = s (ideleClassLogNorm c) * (normOneProjection c : C) := by rw [hfst]; rfl
    _ = _ := mul_comm (s (ideleClassLogNorm c)) (normOneProjection c : C)

private noncomputable def completedHeckeContinuation (χ : Ω) (hχ : ∀ c, ‖χ c‖ = 1) : ℂ → ℂ :=
  (exists_completedHeckeContinuation χ hχ).choose

/-- Local signed order of the completed Hecke function on the norm-twist line through `χ`. -/
public noncomputable def ideleClassHeckeOrder (χ : Ω) : WithTop ℤ :=
  meromorphicOrderAt
    (completedHeckeContinuation (ideleClassHeckeBase χ) (ideleClassHeckeBase_unitary χ))
    (ideleClassNormExponent χ)

/-- The order is that of any meromorphic continuation of the normalized completed product
in these coordinates. Uniqueness holds on punctured neighborhoods, so no value assigned at a
pole or removable singularity enters the order. -/
public theorem ideleClassHeckeOrder_eq (χ : Ω) {L : ℂ → ℂ} (hL : Meromorphic L)
    (hEuler : ∀ s, 1 < s.re → L s =
      completedHeckeEulerProduct (ideleClassHeckeBase χ) (ideleClassHeckeBase_unitary χ) s) :
    ideleClassHeckeOrder χ = meromorphicOrderAt L (ideleClassNormExponent χ) := by
  let b := ideleClassHeckeBase χ
  let hb := ideleClassHeckeBase_unitary χ
  let F := completedHeckeContinuation b hb
  obtain ⟨hF, hEulerF⟩ := (exists_completedHeckeContinuation b hb).choose_spec
  change Meromorphic F at hF
  change ∀ s, 1 < s.re → F s = completedHeckeEulerProduct b hb s at hEulerF
  change meromorphicOrderAt F _ = meromorphicOrderAt L _
  have hdiff : Meromorphic (fun z ↦ F z - L z) := fun z ↦ (hF z).fun_sub (hL z)
  have hr : 1 < (2 : ℂ).re := by norm_num
  have htop : meromorphicOrderAt (fun z ↦ F z - L z) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hnear : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hr
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr ((hEulerF z hz).trans (hEuler z hz).symm)
  have hz := (meromorphicOn_univ.mpr hdiff).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) (Set.mem_univ (ideleClassNormExponent χ)) htop
  apply meromorphicOrderAt_congr
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hz] with z hz'
  exact sub_eq_zero.mp hz'

/-- The distinct completed Hecke zeros with `|Re(s) - 1/2| < α` on the norm-twist line.
The index is the quasi-character itself, not a presentation by a unitary character and a
norm power. Membership requires an exactly finite, strictly positive meromorphic order. -/
@[ext] public structure OpenStripHeckeZero (K : Type*) [Field K] [NumberField K] (α : ℝ) where
  /-- The original zero quasi-character, before the half-norm shift in the Mellin term. -/
  character : HeckeCharacter (𝓞 K) K
  re_mem_strip : |(ideleClassNormExponent character).re - 1 / 2| < α
  order_exists : ∃ n : ℕ, 0 < n ∧ ideleClassHeckeOrder character = ((n : ℤ) : WithTop ℤ)

namespace OpenStripHeckeZero

variable {α : ℝ}

public theorem character_injective : Function.Injective (character (K := K) (α := α)) :=
  fun _ _ h ↦ OpenStripHeckeZero.ext h

/-- The full positive multiplicity, with no truncation or totalization of the signed order. -/
public noncomputable def order (ρ : OpenStripHeckeZero K α) : ℕ := ρ.order_exists.choose

public theorem order_pos (ρ : OpenStripHeckeZero K α) : 0 < ρ.order :=
  ρ.order_exists.choose_spec.1

public theorem heckeOrder_eq (ρ : OpenStripHeckeZero K α) :
    ideleClassHeckeOrder ρ.character = ((ρ.order : ℤ) : WithTop ℤ) :=
  ρ.order_exists.choose_spec.2

end OpenStripHeckeZero

end Masullo
