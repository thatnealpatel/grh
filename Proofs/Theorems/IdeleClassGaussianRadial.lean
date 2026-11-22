module

public import Theorems.DiscriminantNormalizedIdeleHeckeGaussian
public import Theorems.IdeleClassRadialMellin
import all Theorems.IdeleClassRadialMellin -- For unfolding the norm-one pairing.
import Lemmas.IdeleHeckeGaussianMeasurable

/-! # The Gaussian radial Mellin integral above one

We identify the radial integral in (3.2.2.5), PDF pp. 125, 127, for the
corrected Gaussian tensor of Definition 3.4.3.2, p. 152, on `Re s > 1`.
Equation (3.2.2.11), p. 127, uses the same upstairs measure in the Weil
formula as in the Euler evaluation. Here `exists_discriminantNormalizedIdeleHaar`
identifies the two Haar witnesses by the stage restrictions of (A.3.2.5),
p. 560, and `measurable_ideleHeckeGaussian` supplies the pointwise Borel
premise of the checked Weil integral. The raw discriminant factor is
retained; the norm-one Haar is counting-normalized, not a probability.
No continuation or decay estimate for the norm-one average is used. Source reading:
Provisional, from pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField
open NumberField.InfinitePlace (nrRealPlaces nrComplexPlaces)
open NumberField.Units (regulator torsionOrder)
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped ENNReal Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "D" => differentIdeal ℤ (𝓞 K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "q" => (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
local notation "W" => (w₀ : InfinitePlace K)
local notation "σ" => ideleLogSplit (ideleLogSection W) (ideleLogNorm_section W)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)
local notation "η₁" => ideleClassNormOneQuotientMeasure
local notation "η" => ideleClassQuotientMeasure

private theorem norm_cpow_eq_exp (g : C) (s : ℂ) :
    (ideleClassNorm g : ℂ) ^ s = Complex.exp ((Real.log (ideleClassNorm g) : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ideleClassNorm_pos g).ne'),
    ← Complex.ofReal_log (ideleClassNorm_pos g).le]

private noncomputable def twist (χ : HeckeCharacter (𝓞 K) K) (s : ℂ) : C →ₜ* ℂ where
  toFun g := χ g * (ideleClassNorm g : ℂ) ^ s
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul χ, map_mul ideleClassNorm, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (ideleClassNorm_pos g).le (ideleClassNorm_pos h).le]
    ac_rfl
  continuous_toFun := by
    simp_rw [norm_cpow_eq_exp]
    have hlog : Continuous (fun g : C ↦ Real.log (ideleClassNorm g)) :=
      continuous_iff_continuousAt.mpr fun g ↦
        (Real.continuousAt_log (ideleClassNorm_pos g).ne').comp continuous_ideleClassNorm.continuousAt
    exact χ.continuous.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hlog).mul continuous_const))

private theorem twist_section (χ : HeckeCharacter (𝓞 K) K) (s : ℂ) (u : Multiplicative ℝ) :
    twist χ s (τ (u, 1)) = χ (τ (u, 1)) * Complex.exp ((u.toAdd : ℂ) * s) := by
  have h : ideleClassNorm (τ (u, (1 : C₁))) = Real.exp u.toAdd := by
    rw [ideleClassLogSplit_apply, OneMemClass.coe_one, mul_one, ideleClassNorm_logSection]
  change χ (τ (u, 1)) * (ideleClassNorm (τ (u, 1)) : ℂ) ^ s = _
  rw [norm_cpow_eq_exp, h, Real.log_exp]

private theorem twist_normOne (χ : HeckeCharacter (𝓞 K) K) (s : ℂ) (h : C₁) :
    twist χ s (h : C) = χ (h : C) := by
  change χ (h : C) * (ideleClassNorm (h : C) : ℂ) ^ s = χ (h : C)
  rw [(mem_ideleClassNormOne (h : C)).mp h.property, Complex.ofReal_one, Complex.one_cpow, mul_one]

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

/-- One corrected Gaussian and one counting-normalized periodization realize
 the completed Euler product (with the raw discriminant factor) by radial
 Mellin integration for every `Re s > 1`. The restriction of the twist to
 norm-one classes is independent of `s`. -/
public theorem exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ (T : Finset V) (μ : Measure I) (ν : Measure I₁) (F : C → ℂ),
      (∀ w ∉ T, χ.IsUnramifiedAt w ∧ multiplicity w.asIdeal D = 0) ∧
      μ.IsHaarMeasure ∧
      (∀ S : Finset V, (∀ w ∉ S, multiplicity w.asIdeal D = 0) →
        μ.comap (ideleFiniteStageEmbedding K S) =
          ideleFiniteStageProduct K (fun w ↦ archimedeanCompletionHaar w)
            (fun w ↦ finiteCompletionMultiplicativeHaar w) S) ∧
      ν.IsHaarMeasure ∧ μ.map (σ).symm = logVolume.prod ν ∧
      (η₁ ν v r).IsHaarMeasure ∧
      η₁ ν v r Set.univ = (classNumber K : ℝ≥0∞) *
        (ENNReal.ofReal (regulator K) *
          (((2 : ℝ≥0∞) ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K) /
            (torsionOrder K : ℝ≥0∞))) *
        ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹) ∧
      (η ν v r).IsHaarMeasure ∧
      Measurable F ∧ (∀ x, F (q x) = ∑' a : Kˣ, ideleHeckeGaussian χ hχ T (d a * x)) ∧
      (∀ᵐ u ∂logVolume, Integrable (fun h : C₁ ↦ F (τ (u, h)) * χ (h : C)) (η₁ ν v r)) ∧
      ∀ s : ℂ, 1 < s.re →
        Integrable (fun g ↦ F g * (χ g * (ideleClassNorm g : ℂ) ^ s)) (η ν v r) ∧
        let M (u : Multiplicative ℝ) := (χ (τ (u, 1)) * Complex.exp ((u.toAdd : ℂ) * s)) *
          ideleClassRadialPairing (η₁ ν v r) F χ.toMonoidHom u
        Integrable M logVolume ∧ (∫ u, M u ∂logVolume) =
          (((Real.sqrt ((discr K).natAbs : ℝ))⁻¹ : ℝ) : ℂ) * completedHeckeEulerProduct χ hχ s := by
  classical
  -- Identify the two upstairs measures by their exact local products.
  obtain ⟨T, μE, _, _, hT, hE, hEuler⟩ :=
    exists_discriminantNormalizedIdeleHeckeGaussian_zetaIntegral χ hχ
  obtain ⟨μ, ν, hμ, hstage, hν, hsplit, hη₁, hmass⟩ :=
    exists_discriminantNormalizedIdeleClassNormOneHaar v r hr
  obtain ⟨_, _, _, hunique, _⟩ := exists_discriminantNormalizedIdeleHaar K
  have hsame : μE = μ := ((hunique μE).mpr hE).trans ((hunique μ).mpr hstage).symm
  subst μE
  let : μ.IsHaarMeasure := hμ
  let : ν.IsHaarMeasure := hν
  let : SecondCountableTopology I₁ :=
    (Topology.IsInducing.subtypeVal (t := (I₁ : Set I))).secondCountableTopology
  let : CompactSpace C₁ := (compactHausdorff_ideleClassNormOne (K := K)).1
  let : (η₁ ν v r).IsHaarMeasure := hη₁
  have hfin : ν (ideleFundamentalDomain v r) < ⊤ := by
    rw [← ideleClassNormOneQuotientMeasure_univ]
    exact measure_lt_top _ _
  have hη := ideleClassQuotientMeasure_isHaarMeasure ν v r hr hfin
  -- Weil and Fubini, with the norm twist constant on the norm-one factor.
  let f := ideleHeckeGaussian χ hχ T
  let M (F : C → ℂ) (s : ℂ) (u : Multiplicative ℝ) :=
    (χ (τ (u, 1)) * Complex.exp ((u.toAdd : ℂ) * s)) *
      ideleClassRadialPairing (η₁ ν v r) F χ.toMonoidHom u
  have hpair (s : ℂ) (hs : 1 < s.re) :
      ∃ F : C → ℂ, Measurable F ∧ (∀ x, F (q x) = ∑' a : Kˣ, f (d a * x)) ∧
        (∀ᵐ u ∂logVolume, Integrable (fun h : C₁ ↦ F (τ (u, h)) * χ (h : C)) (η₁ ν v r)) ∧
        Integrable (fun g ↦ F g * (χ g * (ideleClassNorm g : ℂ) ^ s)) (η ν v r) ∧
        Integrable (M F s) logVolume ∧ (∫ u, M F s u ∂logVolume) =
          (((Real.sqrt ((discr K).natAbs : ℝ))⁻¹ : ℝ) : ℂ) * completedHeckeEulerProduct χ hχ s := by
    obtain ⟨hi, hval⟩ := hEuler s hs
    have htwist (x : I) : f x * twist χ s (q x) =
        f x * χ (q x) * (‖(x : AdeleRing (𝓞 K) K)‖ : ℂ) ^ s := by
      change f x * (χ (q x) * (ideleClassNorm (QuotientGroup.mk x) : ℂ) ^ s) = _
      rw [ideleClassNorm_mk, ideleNorm_apply, mul_assoc]
    have hi' : Integrable (fun x ↦ f x * twist χ s (q x)) μ := by simp_rw [htwist]; exact hi
    obtain ⟨F, hF, hperiod, hFi, hslice, hM, hInt⟩ := integral_ideleClass_Weil_radial ν v r hr
      μ hsplit (measurable_ideleHeckeGaussian χ hχ T)
      (twist χ s).toMonoidHom (twist χ s).continuous hi'
    have hrad (u : Multiplicative ℝ) :
        ideleClassRadialPairing (η₁ ν v r) F (twist χ s).toMonoidHom u =
          ideleClassRadialPairing (η₁ ν v r) F χ.toMonoidHom u := by
      unfold ideleClassRadialPairing
      change (∫ h : C₁, F (τ (u, h)) * twist χ s (h : C) ∂(η₁ ν v r)) =
        ∫ h : C₁, F (τ (u, h)) * χ (h : C) ∂(η₁ ν v r)
      simp only [twist_normOne]
    change (∀ᵐ u ∂logVolume,
      Integrable (fun h : C₁ ↦ F (τ (u, h)) * twist χ s (h : C)) (η₁ ν v r)) at hslice
    simp only [twist_normOne] at hslice
    change Integrable (fun u ↦ twist χ s (τ (u, 1)) *
      ideleClassRadialPairing (η₁ ν v r) F (twist χ s).toMonoidHom u) logVolume at hM
    change (∫ u, twist χ s (τ (u, 1)) *
      ideleClassRadialPairing (η₁ ν v r) F (twist χ s).toMonoidHom u ∂logVolume) =
        (∫ x, f x * twist χ s (q x) ∂μ) at hInt
    simp only [hrad, twist_section] at hM hInt
    change Integrable (fun g ↦ F g * (χ g * (ideleClassNorm g : ℂ) ^ s)) (η ν v r) at hFi
    simp_rw [htwist] at hInt
    exact ⟨F, hF, hperiod, hslice, hFi, hM, hInt.trans hval⟩
  -- The Borel periodization is determined at every class, independent of `s`.
  obtain ⟨F, hF, hperiod, hslice, _⟩ := hpair 2 (by norm_num)
  refine ⟨T, μ, ν, F, hT, hμ, hstage, hν, hsplit, hη₁, hmass, hη, hF, hperiod, hslice, ?_⟩
  intro s hs
  obtain ⟨G, _, hG, _, hGi, hM, hInt⟩ := hpair s hs
  have heq : G = F := by
    funext g
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective (q : I → C)) g
    exact (hG x).trans (hperiod x).symm
  subst G
  exact ⟨hGi, hM, hInt⟩

end Masullo
