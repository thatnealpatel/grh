module

public import Theorems.AdeleBoxThetaDecay
public import Theorems.AdeleHeckeGaussianTheta
public import Theorems.IdeleClassRadialMellin
import all Theorems.IdeleClassRadialMellin -- For unfolding the norm-one pairing.
import Mathlib.MeasureTheory.Group.Integral

/-! # The corrected Gaussian pairing at small norm

The proof of Theorem 2.2.5.4(2), PDF pp. 97–98, averages the estimate
(2.2.3.5), p. 83, with the finite norm-one Haar of (2.2.5.2), p. 95.
We use the pointwise estimate for the repaired Fourier kernel of
`AdeleBoxThetaInversion` (corrected finite trace signs), on the very same
fixed-stage Gaussian as in the radial Mellin integral, with its Borel
periodization. The pairing uses ordinary multiplication by the norm-one
class as in the p. 97 computation, not the literal inverse translation
in the p. 96 description of (2.2.5.2).
Integrate the error after removing the two zero terms, and compute the
integral of those terms by character orthogonality. This gives (2.2.5.10)
on the radial section, with the actual norm-one mass, not probability
normalization. Source reading: Provisional pinned Markdown and PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Classical Masullo.AdeleStage

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "q" => (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
local notation "W" => (w₀ : InfinitePlace K)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)
local notation "η₁" => ideleClassNormOneQuotientMeasure

variable [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

/-- The trivial restriction contributes the full quotient mass. A
nontrivial restriction has mean zero, by a single left translation. -/
private theorem integral_normOne_character (m : Measure C₁) [m.IsHaarMeasure]
    (χ : HeckeCharacter (𝓞 K) K) :
    (∫ h : C₁, χ (h : C) ∂m) = if ∀ h : C₁, χ (h : C) = 1 then
      (m.real Set.univ : ℂ) else 0 := by
  by_cases htriv : ∀ h : C₁, χ (h : C) = 1
  · simp [htriv, integral_const, Complex.real_smul]
  · obtain ⟨k, hk⟩ := not_forall.mp htriv
    simp only [htriv, ↓reduceIte]
    have heq := integral_mul_left_eq_self (μ := m) (fun h : C₁ ↦ χ (h : C)) k
    simp only [Subgroup.coe_mul, map_mul, integral_const_mul] at heq
    exact (mul_eq_zero.mp (show (χ (k : C) - 1) * (∫ h : C₁, χ (h : C) ∂m) = 0 by
      rw [sub_mul, one_mul, heq, sub_self])).resolve_left (sub_ne_zero.mpr hk)

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))]

/-- At every nonpositive log radius the corrected Gaussian slice is
integrable. The norm-one pairing satisfies (2.2.5.10), with both zero
terms multiplied by the full quotient mass for the trivial restriction
and both absent for a nontrivial restriction. The stage and periodization
can be taken from `exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin`.
The additive cofinal-stage Haar is a separate input from its
multiplicative Haar. -/
public theorem ideleHeckeGaussian_radialPairing_smallNorm_decay
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (T : Finset V) (μ : Measure A) [μ.IsAddHaarMeasure]
    (E : Finset V) (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    (ν : Measure I₁) (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hη₁ : (η₁ ν v r).IsHaarMeasure) {F : C → ℂ} (hF : Measurable F)
    (hperiod : ∀ g : I, F (q g) = ∑' a : Kˣ, ideleHeckeGaussian χ hχ T (d a * g))
    (N : ℕ) :
    let f := adeleHeckeTest χ T (archimedeanHeckeSchwartz χ hχ)
    let m := η₁ ν v r
    let b : ℂ := if ∀ h : C₁, χ (h : C) = 1 then (m.real Set.univ : ℂ) else 0
    ∃ B : ℝ, 0 < B ∧ ∀ u : Multiplicative ℝ, u.toAdd ≤ 0 →
      Integrable (fun h : C₁ ↦ F (τ (u, h)) * χ (h : C)) m ∧
      ‖ideleClassRadialPairing m F χ.toMonoidHom u -
        ((Real.exp u.toAdd)⁻¹ • adeleFourier μ f 0 - f 0) * b‖ ≤
        B * Real.exp ((N : ℝ) * u.toAdd) * m.real Set.univ := by
  dsimp only
  let f := adeleHeckeTest χ T (archimedeanHeckeSchwartz χ hχ)
  let m := η₁ ν v r
  let : CompactSpace C₁ := (compactHausdorff_ideleClassNormOne (K := K)).1
  let : m.IsHaarMeasure := hη₁
  have hf : f ∈ adeleBoxSpan K := adeleHeckeTest_mem_adeleBoxSpan χ T _
  obtain ⟨B, hB, hbound⟩ := adeleBoxSpan_theta_smallNorm_decay μ E hμ hf N
  refine ⟨B, hB, fun u hu ↦ ?_⟩
  let z : ℂ := (Real.exp u.toAdd)⁻¹ • adeleFourier μ f 0 - f 0
  have hslice : Measurable (fun h : C₁ ↦ F (τ (u, h))) :=
    hF.comp ((τ).continuous.measurable.comp (measurable_const.prodMk measurable_id))
  have hweight : Measurable (fun h : C₁ ↦ χ (h : C)) :=
    (χ.continuous.comp continuous_subtype_val).measurable
  -- The corrected estimate holds at any representative of the slice.
  have hmajor (h : C₁) : ‖(F (τ (u, h)) - z) * χ (h : C)‖ ≤
      B * Real.exp ((N : ℝ) * u.toAdd) := by
    obtain ⟨g, hg⟩ := (QuotientGroup.mk_surjective : Function.Surjective (q : I → C)) (τ (u, h))
    have hnorm : ideleNorm g = Real.exp u.toAdd := by
      rw [← ideleClassNorm_mk g, show QuotientGroup.mk g = τ (u, h) from hg,
        ideleClassLogSplit_apply, map_mul, ideleClassNorm_logSection,
        (mem_ideleClassNormOne (h : C)).mp h.property, mul_one]
    have htest (a : Kˣ) : ideleHeckeGaussian χ hχ T (d a * g) =
        f ((g : A) * algebraMap K A (a : K)) := by
      rw [mul_comm (d a) g]
      exact (adeleHeckeTest_archimedeanHeckeSchwartz_coe_idele χ hχ T (g * d a)).symm
    rw [norm_mul, hχ, mul_one, ← hg]
    change ‖F (q g) - z‖ ≤ _
    rw [hperiod]
    simp only [htest]
    have hsub (x y w : ℂ) : x - (y - w) = x - y + w := by abel
    simpa only [hnorm, ← Real.exp_nat_mul, z, hsub] using
      hbound g (hnorm ▸ Real.exp_le_one_iff.mpr hu)
  -- Integrate the error and the character-weighted zero terms separately.
  have herr : Integrable (fun h : C₁ ↦ (F (τ (u, h)) - z) * χ (h : C)) m :=
    Integrable.of_bound ((hslice.sub measurable_const).mul hweight).aestronglyMeasurable _
      (Filter.Eventually.of_forall hmajor)
  have hzero : Integrable (fun h : C₁ ↦ z * χ (h : C)) m :=
    Integrable.of_bound (measurable_const.mul hweight).aestronglyMeasurable ‖z‖
      (Filter.Eventually.of_forall fun h ↦ by rw [norm_mul, hχ, mul_one])
  have hweighted : Integrable (fun h : C₁ ↦ F (τ (u, h)) * χ (h : C)) m := by
    apply (herr.add hzero).congr
    exact Filter.Eventually.of_forall fun h ↦ by simp [sub_mul]
  refine ⟨hweighted, ?_⟩
  change ‖(∫ h : C₁, F (τ (u, h)) * χ (h : C) ∂m) -
    z * (if ∀ h : C₁, χ (h : C) = 1 then (m.real Set.univ : ℂ) else 0)‖ ≤ _
  rw [← integral_normOne_character m χ, ← integral_const_mul, ← integral_sub hweighted hzero]
  simp_rw [← sub_mul]
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hmajor)

end Masullo
