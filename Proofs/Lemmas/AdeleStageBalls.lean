module

public import Lemmas.AdeleBoxDilation

/-! # A translated finite box with prescribed active coordinates -/

open Filter IsDedekindDomain NumberField Set
open scoped Classical Pointwise SchwartzMap

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "L[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v

private theorem eventually_integral_of_eq_one_outside (S : Finset V)
    (b : (v : V) → L[v]) (hb : ∀ v ∉ S, b v = 1) :
    ∀ᶠ v in cofinite, b v ∈ O[v] :=
  S.eventually_cofinite_notMem.mono fun v hv ↦ hb v hv ▸ (O[v]).one_mem

private def stageCenter (S : Finset V) (a : (v : S) → L[v.val]) : F :=
  ⟨fun v ↦ if hv : v ∈ S then a ⟨v, hv⟩ else 0,
    S.eventually_cofinite_notMem.mono fun v hv ↦ by simp [hv]⟩

private def stageScaleValue (S : Finset V) (r : (v : S) → L[v.val]ˣ) : F :=
  ⟨fun v ↦ if hv : v ∈ S then (r ⟨v, hv⟩ : L[v]) else 1,
    eventually_integral_of_eq_one_outside S _ fun _ hv ↦ dite_eq_right hv⟩

private def stageScale (S : Finset V) (r : (v : S) → L[v.val]ˣ) : Fˣ :=
  Units.mkOfMulEqOne (stageScaleValue S r) (stageScaleValue S fun v ↦ (r v)⁻¹) (by
    ext v : 1
    change (if hv : v ∈ S then (r ⟨v, hv⟩ : L[v]) else 1) *
      (if hv : v ∈ S then (↑((r ⟨v, hv⟩)⁻¹) : L[v]) else 1) = (1 : L[v])
    by_cases hv : v ∈ S <;> simp [hv])

private theorem mem_translate_scale_iff {v : V} (x a : L[v]) (r : L[v]ˣ) :
    x ∈ (a + ·) '' ((r : L[v]) • (O[v] : Set L[v])) ↔
      (↑r⁻¹ : L[v]) * (x - a) ∈ O[v] := by
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    change (↑r⁻¹ : L[v]) * (a + (r : L[v]) * t - a) ∈ O[v]
    change t ∈ O[v] at ht
    simpa only [add_sub_cancel_left, Units.inv_mul_cancel_left] using ht
  · intro hx
    refine ⟨(r : L[v]) * ((↑r⁻¹ : L[v]) * (x - a)),
      ⟨_, hx, rfl⟩, ?_⟩
    change a + (r : L[v]) * ((↑r⁻¹ : L[v]) * (x - a)) = x
    rw [Units.mul_inv_cancel_left, add_sub_cancel]

private theorem mem_stageBox_iff (S : Finset V) (a : (v : S) → L[v.val])
    (r : (v : S) → L[v.val]ˣ) (z : F) :
    z ∈ finiteAdeleBox (stageCenter S a) (stageScale S r) ↔
      (∀ v ∉ S, z v ∈ O[v]) ∧
        ∀ v : S, (↑(r v)⁻¹ : L[v.val]) * (z v.val - a v) ∈ O[v.val] := by
  change (∀ v : V, z v ∈ ((stageCenter S a v + ·) ''
    ((stageScale S r).val v • (O[v] : Set L[v])))) ↔ _
  have hc (v : V) : stageCenter S a v = (if hv : v ∈ S then a ⟨v, hv⟩ else 0) := rfl
  have hg (v : V) : (stageScale S r).val v =
      (if hv : v ∈ S then (r ⟨v, hv⟩ : L[v]) else 1) := rfl
  constructor
  · intro hh
    constructor
    · intro v hv
      change z v ∈ (O[v] : Set L[v])
      simpa [hc, hg, hv] using hh v
    · intro v
      apply (mem_translate_scale_iff _ _ _).mp
      simpa [hc, hg, v.property] using hh v.val
  · rintro ⟨hout, hin⟩ v
    by_cases hv : v ∈ S
    · simpa [hc, hg, hv] using
        (mem_translate_scale_iff (z v) (a ⟨v, hv⟩) (r ⟨v, hv⟩)).mpr (hin ⟨v, hv⟩)
    · have hh : z v ∈ (O[v] : Set L[v]) := hout v hv
      simpa [hc, hg, hv] using hh

/-- The product of the active local ball indicators, extended by zero off the
finite stage, is one actual translated adelic box tensor. -/
public theorem exists_adeleBoxTensor_eq_stageBalls
    (φ : 𝓢(mixedEmbedding.euclidean.mixedSpace K, ℂ)) (S : Finset V)
    (a : (v : S) → L[v.val]) (r : (v : S) → L[v.val]ˣ) :
    ∃ (b : F) (g : Fˣ), ∀ z : AdeleRing (𝓞 K) K,
      adeleBoxTensor φ b g z =
        if ∀ v ∉ S, z.2 v ∈ O[v] then
          φ ((archimedeanEuclideanToAdele K).symm z.1) *
            ∏ v : S, ({y : L[v.val] | (↑(r v)⁻¹ : L[v.val]) * (y - a v) ∈ O[v.val]} :
              Set L[v.val]).indicator (fun _ ↦ (1 : ℂ)) (z.2 v.val)
        else 0 := by
  refine ⟨stageCenter S a, stageScale S r, fun z ↦ ?_⟩
  have hm := mem_stageBox_iff S a r z.2
  rw [adeleBoxTensor]
  by_cases ho : ∀ v ∉ S, z.2 v ∈ O[v]
  · rw [ite_eq_left ho]
    by_cases hi : ∀ v : S, (↑(r v)⁻¹ : L[v.val]) * (z.2 v.val - a v) ∈ O[v.val]
    · rw [indicator_of_mem (hm.mpr ⟨ho, hi⟩)]
      congr 1
      symm
      exact Finset.prod_eq_one fun v _ ↦ by simp only [indicator_apply, mem_ofPred_eq, ite_eq_left (hi v)]
    · obtain ⟨v, hv⟩ := not_forall.mp hi
      rw [indicator_of_notMem (fun hz ↦ hi (hm.mp hz).2),
        Finset.prod_eq_zero (Finset.mem_univ v) (by simp only [indicator_apply, mem_ofPred_eq, ite_eq_right hv])]
  · rw [ite_eq_right ho, indicator_of_notMem (fun hz ↦ ho (hm.mp hz).1), mul_zero]

end

end Masullo
