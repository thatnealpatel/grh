module

public import Theorems.IdeleClassWeil
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Radial Mellin integration on the idele classes

The pointwise integral equality used for (3.2.2.5), PDF pp. 125, 127,
applies quotient integration to the norm-one classes with radial
quotient measure `dt/t`. The homogeneous pairing (2.2.5.2), p. 95,
uses the restriction of the quasi-character itself, not its conjugate.
Here the checked log-product measure identifies the quotient integral
with a product integral, and Bochner Fubini gives the radial formula
on the absolute-integrability domain. This does not prove the
Schwartz–Bruhat convergence bounds or the meromorphic identity.
Source reading: Provisional, from Markdown and numbered PDF text.
-/

open NumberField MeasureTheory
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "q" => (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
local notation "W" => (w₀ : InfinitePlace K)
local notation "σ" => ideleLogSplit (ideleLogSection W) (ideleLogNorm_section W)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)
local notation "η₁" => ideleClassNormOneQuotientMeasure
local notation "η" => ideleClassQuotientMeasure

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

/-- The norm-one pairing at the section point of log radius `u`, as in
(2.2.5.2). The integral is Lean's totalized Bochner integral; slice
integrability in the Borel setting is established almost everywhere below. -/
public noncomputable def ideleClassRadialPairing (m : Measure C₁) (F : C → ℂ)
    (c : C →* ℂ) (u : Multiplicative ℝ) : ℂ :=
  ∫ h : C₁, F (τ (u, h)) * c (h : C) ∂m

variable (ν : Measure (ideleNormOne (K := K))) [SFinite ν] (v : InfinitePlace K)
  (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))

private theorem logVolume_sFinite : SFinite logVolume := by
  have h := congrArg (Measure.map (Multiplicative.ofAdd : ℝ → Multiplicative ℝ))
    map_toAdd_logVolume
  rw [Measure.map_map measurable_ofAdd measurable_toAdd, show
    Multiplicative.ofAdd ∘ Multiplicative.toAdd = (id : Multiplicative ℝ → Multiplicative ℝ)
    from rfl, Measure.map_id] at h
  rw [h]
  infer_instance

/-- Product Fubini and character factorization give the radial part of
(3.2.2.5) whenever the class integrand is absolutely integrable. -/
public theorem integral_ideleClass_radial {F : C → ℂ} (c : C →* ℂ)
    (hFi : Integrable (fun g ↦ F g * c g) (η ν v r)) :
    (∀ᵐ u ∂logVolume, Integrable (fun h : C₁ ↦ F (τ (u, h)) * c (h : C)) (η₁ ν v r)) ∧
    Integrable (fun u ↦ c (τ (u, 1)) * ideleClassRadialPairing (η₁ ν v r) F c u) logVolume ∧
    (∫ u, c (τ (u, 1)) * ideleClassRadialPairing (η₁ ν v r) F c u ∂logVolume) =
      ∫ g, F g * c g ∂(η ν v r) := by
  let m := η₁ ν v r
  let H : Multiplicative ℝ × C₁ → ℂ := fun p ↦ F (τ p) * c (τ p)
  have ht : Measurable τ := (τ).continuous.measurable
  let := logVolume_sFinite
  let : SFinite m := by unfold m ideleClassNormOneQuotientMeasure; infer_instance
  have hH : Integrable H (logVolume.prod m) := hFi.comp_aemeasurable ht.aemeasurable
  -- The split is the product of the section and the norm-one inclusion.
  have hfactor (u : Multiplicative ℝ) (h : C₁) :
      H (u, h) = c (τ (u, 1)) * (F (τ (u, h)) * c (h : C)) := by
    have hc : c (τ (u, h)) = c (τ (u, 1)) * c (h : C) := by
      simp only [ideleClassLogSplit_apply, OneMemClass.coe_one, mul_one, map_mul]
    simp only [H, hc]
    ring
  have hslices : ∀ᵐ u ∂logVolume, Integrable (fun h : C₁ ↦ F (τ (u, h)) * c (h : C)) m := by
    filter_upwards [hH.prod_right_ae] with u hu
    have hunit := (Group.isUnit (τ (u, 1))).map c
    simpa only [hfactor, integrable_const_mul_iff hunit] using hu
  -- Fubini for the weighted integrand, then identify the inner integral.
  have hinner (u : Multiplicative ℝ) : (∫ h, H (u, h) ∂m) =
      c (τ (u, 1)) * ideleClassRadialPairing m F c u := by
    simp only [hfactor, integral_const_mul, ideleClassRadialPairing]
  refine ⟨hslices, hH.integral_prod_left.congr (Filter.Eventually.of_forall hinner), ?_⟩
  calc
    _ = ∫ u, (∫ h, H (u, h) ∂m) ∂logVolume := integral_congr_ae
      (Filter.Eventually.of_forall fun u ↦ (hinner u).symm)
    _ = ∫ p, H p ∂(logVolume.prod m) := (integral_prod H hH).symm
    _ = ∫ g, F g * c g ∂(η ν v r) := (integral_map ht.aemeasurable hFi.1).symm

variable [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]

/-- On the upstairs weighted `L¹` domain, (3.2.2.11) and radial Fubini
identify the global idelic integral with the radial Mellin integral of the
norm-one pairing of the principal periodization. -/
public theorem integral_ideleClass_Weil_radial
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p)
    (μ : Measure I) [μ.IsMulLeftInvariant] (hsplit : μ.map (σ).symm = logVolume.prod ν)
    {f : I → ℂ} (hf : Measurable f) (c : C →* ℂ) (hc : Continuous c)
    (hfi : Integrable (fun x ↦ f x * c (q x)) μ) :
    ∃ F : C → ℂ, Measurable F ∧ (∀ x, F (q x) = ∑' a : Kˣ, f (d a * x)) ∧
      Integrable (fun g ↦ F g * c g) (η ν v r) ∧
      (∀ᵐ u ∂logVolume, Integrable (fun h : C₁ ↦ F (τ (u, h)) * c (h : C)) (η₁ ν v r)) ∧
      Integrable (fun u ↦ c (τ (u, 1)) * ideleClassRadialPairing (η₁ ν v r) F c u) logVolume ∧
      (∫ u, c (τ (u, 1)) * ideleClassRadialPairing (η₁ ν v r) F c u ∂logVolume) =
        ∫ x, f x * c (q x) ∂μ := by
  obtain ⟨F, hF, hperiod, hFi, _, hWeil⟩ :=
    integral_ideleClass_Weil_weighted ν v r hr μ hsplit hf hc.measurable hfi
  obtain ⟨hslice, hradial, hFubini⟩ := integral_ideleClass_radial ν v r c hFi
  exact ⟨F, hF, hperiod, hFi, hslice, hradial, hFubini.trans hWeil⟩

end Masullo
