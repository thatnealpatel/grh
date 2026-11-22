module

public import Theorems.IdeleClassRadialMellin
public import Theorems.IdeleGaussianThetaInversion
import Lemmas.IdeleFiniteStageMeasure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Metrizable.Urysohn

/-! # Norm-one averaging of the different-translated Gaussian inversion

Masullo uses Poisson inversion with both zero values in (2.2.3.7), p. 83,
and the compact norm-one average in (2.2.5.2), p. 95. For the fixed
Gaussian, the checked pointwise inversion expresses the transformed test
using the original test translated by the different. The norm of that
translation changes the reflected log radius. Its remaining norm-one
component disappears by Haar invariance, without normalizing the mass to
one. This gives the radial input to (3.2.2.4)–(5), p. 125, for a proof of
the specific epsilon factor needed in (B.4.2.3), p. 614. It is not yet a
functional equation of the continued Mellin transform. Source reading:
Provisional, from pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField Topology
open NumberField.InfinitePlace (nrComplexPlaces)
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Classical

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)
local notation "q" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
local notation "σ" => ideleClassLogSection (w₀ : InfinitePlace K)
local notation "τ" => ideleClassLogSplit σ (ideleClassLogNorm_section (w₀ : InfinitePlace K))
local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

private theorem rearrange_reflection {G : Type*} [CommGroup G] (a b c e : G) :
    a * (b * c)⁻¹ = e * b⁻¹ * (a / e / c) := by
  simp only [mul_inv_rev, div_eq_mul_inv]
  calc
    a * (c⁻¹ * b⁻¹) = (e * e⁻¹) * (a * (c⁻¹ * b⁻¹)) := by simp
    _ = e * b⁻¹ * (a * e⁻¹ * c⁻¹) := by ac_rfl

/-- At every log radius, the integrable trivial-character average satisfies
exact theta inversion, including the Gaussian zero value times the full
norm-one Haar mass on both sides. The reflected log radius is `-δ - x`,
where `δ` is the logarithm of the absolute discriminant. -/
public theorem ideleHeckeGaussian_one_radialPairing_reflection
    (T : Finset (HeightOneSpectrum (𝓞 K))) (m : Measure C₁) [m.IsHaarMeasure]
    (F : C → ℂ)
    (hperiod : ∀ g : I, F (q g) = ∑' a : Kˣ,
      ideleHeckeGaussian χ₀ (fun _ ↦ norm_one) T (IdeleGroup.unitEmbedding (𝓞 K) K a * g))
    (hslice : ∀ x : ℝ, Integrable (fun h : C₁ ↦ F (τ (Multiplicative.ofAdd x, h))) m) :
    let δ := Real.log ((discr K).natAbs : ℝ)
    let P (x : ℝ) := ∫ h : C₁, F (τ (Multiplicative.ofAdd x, h)) ∂m
    let a : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ nrComplexPlaces K * (m.real Set.univ : ℂ)
    ∀ x : ℝ, P x + a = (Real.exp (-δ / 2 - x) : ℂ) * (P (-δ - x) + a) := by
  dsimp only
  let : CompactSpace C₁ := (compactHausdorff_ideleClassNormOne (K := K)).1
  let : T2Space C₁ := (compactHausdorff_ideleClassNormOne (K := K)).2
  let : SecondCountableTopology I := secondCountable_ideleGroup K
  let : SecondCountableTopology C :=
    (QuotientGroup.isOpenQuotientMap_mk : IsOpenQuotientMap (q : I → C)).secondCountableTopology
  let : SecondCountableTopology C₁ :=
    (Topology.IsInducing.subtypeVal (t := (C₁ : Set C))).secondCountableTopology
  let : Measure.Regular m := inferInstance
  let : m.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular m
  let δ := Real.log ((discr K).natAbs : ℝ)
  let d : C := q (gaussianDifferentIdele K)
  let f₀ : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ nrComplexPlaces K
  have hD : 0 < ((discr K).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hd : ideleClassNorm d = Real.exp (-δ) := by
    change ideleClassNorm (QuotientGroup.mk (gaussianDifferentIdele K)) = _
    rw [ideleClassNorm_mk, ideleNorm_gaussianDifferentIdele, Real.exp_neg, Real.exp_log hD]
  -- The difference between the translated inverse and the reflected section is norm one.
  let k : C₁ := ⟨d / σ (Multiplicative.ofAdd (-δ)), by
    rw [mem_ideleClassNormOne, div_eq_mul_inv, map_mul, map_inv, hd, ideleClassNorm_logSection]
    exact mul_inv_cancel₀ (Real.exp_ne_zero _)⟩
  have hk : (k : C) = d / σ (Multiplicative.ofAdd (-δ)) := rfl
  intro x
  let R (y : ℝ) (h : C₁) := F (τ (Multiplicative.ofAdd y, h))
  let y := -δ - x
  let b : ℂ := (Real.exp (-δ / 2 - x) : ℝ)
  have hpoint (h : C₁) : R x h + f₀ = b * (R y (k / h) + f₀) := by
    obtain ⟨g, hg⟩ := (QuotientGroup.mk_surjective : Function.Surjective (q : I → C))
      (τ (Multiplicative.ofAdd x, h))
    change q g = _ at hg
    have hnorm : ideleNorm g = Real.exp x := by
      rw [← ideleClassNorm_mk g, show QuotientGroup.mk g = _ from hg,
        ideleClassLogSplit_apply, map_mul, ideleClassNorm_logSection,
        (mem_ideleClassNormOne (h : C)).mp h.property, mul_one]
      rfl
    have hreflect : q (gaussianDifferentIdele K * g⁻¹) = τ (Multiplicative.ofAdd y, k / h) := by
      rw [map_mul, map_inv, hg, ideleClassLogSplit_apply, ideleClassLogSplit_apply,
        Subgroup.coe_div, hk, show Multiplicative.ofAdd y =
          Multiplicative.ofAdd (-δ) * (Multiplicative.ofAdd x)⁻¹ from rfl,
        map_mul, map_inv]
      exact rearrange_reflection d (σ (Multiplicative.ofAdd x)) (h : C)
        (σ (Multiplicative.ofAdd (-δ)))
    have hscale : (Real.sqrt |(discr K : ℝ)| * ideleNorm g)⁻¹ = Real.exp (-δ / 2 - x) := by
      rw [hnorm, ← Int.cast_abs, ← Nat.cast_natAbs, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hD,
        ← Real.exp_add, ← Real.exp_neg]
      congr 1
      dsimp [δ]
      ring
    have h := ideleHeckeGaussian_one_radial_theta_inversion T F hperiod g
    rw [hg, hreflect, hscale] at h
    exact eq_sub_iff_add_eq.mp h
  -- The affine inversion on the compact norm-one group preserves its Haar measure.
  change (∫ h, R x h ∂m) + f₀ * (m.real Set.univ : ℂ) =
    b * ((∫ h, R y h ∂m) + f₀ * (m.real Set.univ : ℂ))
  calc
    _ = ∫ h, (R x h + f₀) ∂m := by
      rw [integral_add (hslice x) (integrable_const _), integral_const, Complex.real_smul, mul_comm _ f₀]
    _ = ∫ h, b * (R y (k / h) + f₀) ∂m := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = b * (∫ h, (R y h + f₀) ∂m) := by
      rw [integral_const_mul, integral_div_left_eq_self (fun h ↦ R y h + f₀) m k]
    _ = _ := by
      rw [integral_add (hslice y) (integrable_const _), integral_const, Complex.real_smul, mul_comm _ f₀]

end Masullo
