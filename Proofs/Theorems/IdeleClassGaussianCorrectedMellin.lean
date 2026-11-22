module

public import Theorems.IdeleClassGaussianRadial
public import Theorems.IdeleClassGaussianSmallNorm
import all Theorems.IdeleClassRadialMellin -- For unfolding the norm-one pairing.
import Theorems.AdeleRestrictedProductHaar
import Lemmas.LogMellinDerivative
import Lemmas.LogMellinTwoTails

/-! # The entire corrected radial Mellin transform of the fixed Gaussian

In the radial formula (3.2.2.4)–(5), p. 125, write `x = log t`. For the
fixed Gaussian, retain the character on the section and subtract both zero
terms in the *paired* profile, only for `x < 0`. The two bounds
(2.2.5.9)–(10), pp. 97–98, now give rapid decay on the entire log line.

For the continuation step in Theorem 3.2.2.1(1a),(3), pp. 124–127, this
replaces the use of the unaveraged estimate in (3.2.2.7)–(10): Character
cancellation does not bound the unaveraged absolute value. We establish
Borel measurability from the product-slice integral and differentiate the
corrected log integral by a local Bochner majorant, including its first
log moment. No continuity at zero is needed. The poles of the removed
terms and the meromorphic identity are not established here. Source
reading: Provisional, from pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain MeasureTheory NumberField
open NumberField.InfinitePlace (nrRealPlaces nrComplexPlaces)
open NumberField.Units (regulator torsionOrder)
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Classical ENNReal Masullo.AdeleStage

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "D" => differentIdeal ℤ (𝓞 K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "q" => (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
local notation "W" => (w₀ : InfinitePlace K)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)
local notation "η₁" => ideleClassNormOneQuotientMeasure

variable [MeasurableSpace (ideleClassNormOne (K := K))]

/-- The norm-one pairing minus its small-radius zero modes, multiplied
by the unitary section phase. The log Mellin weight `exp (s*x)` is not
included. The correction is zero at `x = 0`. -/
public noncomputable def ideleClassCorrectedLogProfile (m : Measure C₁) (F : C → ℂ)
    (χ : HeckeCharacter (𝓞 K) K) (f0 fhat0 : ℂ) (x : ℝ) : ℂ :=
  χ (τ (Multiplicative.ofAdd x, 1)) *
    (ideleClassRadialPairing m F χ.toMonoidHom (Multiplicative.ofAdd x) -
      (if x < 0 then (Real.exp (-x) • fhat0 - f0) *
        (if ∀ h : C₁, χ (h : C) = 1 then (m.real Set.univ : ℂ) else 0) else 0))

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

/-- With the independent additive-stage Haar for the Fourier integral, the
same fixed-stage Gaussian as in the Euler calculation has an entire
corrected radial Mellin transform. Every norm-one slice is integrable. The
complex derivative inserts one log moment in the corrected integral. -/
public theorem ideleHeckeGaussian_correctedRadialMellin_entire
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (T : Finset V) (μ : Measure A) [μ.IsAddHaarMeasure]
    (E : Finset V) (hμ : ∀ S : Finset V, E ⊆ S →
      μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S)
    (ν : Measure I₁) (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hη₁ : (η₁ ν v r).IsHaarMeasure) {F : C → ℂ} (hF : Measurable F)
    (hperiod : ∀ g : I, F (q g) = ∑' a : Kˣ, ideleHeckeGaussian χ hχ T (d a * g)) :
    let f := adeleHeckeTest χ T (archimedeanHeckeSchwartz χ hχ)
    let m := η₁ ν v r
    let p := ideleClassCorrectedLogProfile m F χ (f 0) (adeleFourier μ f 0)
    (∀ u : Multiplicative ℝ, Integrable (fun h : C₁ ↦ F (τ (u, h)) * χ (h : C)) m) ∧
    Measurable p ∧
    Differentiable ℂ (fun s : ℂ ↦ ∫ x : ℝ, p x * Complex.exp (s * x)) ∧
    ∀ s : ℂ, Integrable (fun x : ℝ ↦ p x * Complex.exp (s * x)) ∧
      Integrable (fun x : ℝ ↦ (x : ℂ) * (p x * Complex.exp (s * x))) ∧
      HasDerivAt (fun w : ℂ ↦ ∫ x : ℝ, p x * Complex.exp (w * x))
        (∫ x : ℝ, (x : ℂ) * (p x * Complex.exp (s * x))) s := by
  dsimp only
  let f := adeleHeckeTest χ T (archimedeanHeckeSchwartz χ hχ)
  let m := η₁ ν v r
  let p := ideleClassCorrectedLogProfile m F χ (f 0) (adeleFourier μ f 0)
  let : CompactSpace C₁ := (compactHausdorff_ideleClassNormOne (K := K)).1
  let : m.IsHaarMeasure := hη₁
  have hlarge := ideleHeckeGaussian_radialPairing_rapidDecay χ hχ T ν v r hη₁ hF hperiod
  have hsmall := ideleHeckeGaussian_radialPairing_smallNorm_decay
    χ hχ T μ E hμ ν v r hη₁ hF hperiod
  have hphase : Continuous (fun x : ℝ ↦ χ (τ (Multiplicative.ofAdd x, (1 : C₁)))) :=
    χ.continuous.comp ((τ).continuous.comp (continuous_id.prodMk continuous_const))
  have hpair : Measurable (fun x : ℝ ↦
      ideleClassRadialPairing m F χ.toMonoidHom (Multiplicative.ofAdd x)) := by
    have hproduct : Measurable (fun uh : ℝ × C₁ ↦
        F (τ (Multiplicative.ofAdd uh.1, uh.2)) * χ (uh.2 : C)) :=
      (hF.comp ((τ).continuous.measurable.comp
        ((measurable_ofAdd.comp measurable_fst).prodMk measurable_snd))).mul
        ((χ.continuous.comp continuous_subtype_val).measurable.comp measurable_snd)
    exact (hproduct.stronglyMeasurable.integral_prod_right' (ν := m)).measurable
  -- A Borel half-line correction suffices; the value at the boundary need not match.
  have hp : Measurable p := by
    unfold p ideleClassCorrectedLogProfile
    exact hphase.measurable.mul (hpair.sub (Measurable.ite measurableSet_Iio
      ((((Real.continuous_exp.comp continuous_neg).measurable.smul measurable_const).sub
        measurable_const).mul measurable_const) measurable_const))
  -- Apply the two weighted slice estimates on their own half-lines.
  have hpLarge (N : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 0 ≤ x →
      ‖p x‖ ≤ B * Real.exp (-(N : ℝ) * x) * m.real Set.univ := by
    obtain ⟨B, hB, htail⟩ := hlarge N
    refine ⟨B, hB, fun x hx ↦ ?_⟩
    simpa only [p, m, ideleClassCorrectedLogProfile, ite_eq_right (not_lt.mpr hx), sub_zero,
      norm_mul, hχ, one_mul, toAdd_ofAdd] using (htail (Multiplicative.ofAdd x) hx).2
  have hpSmall (N : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, x < 0 →
      ‖p x‖ ≤ B * Real.exp ((N : ℝ) * x) * m.real Set.univ := by
    obtain ⟨B, hB, htail⟩ := hsmall N
    refine ⟨B, hB, fun x hx ↦ ?_⟩
    simpa only [p, m, f, ideleClassCorrectedLogProfile, ite_eq_left hx, norm_mul, hχ, one_mul,
      Real.exp_neg, toAdd_ofAdd] using (htail (Multiplicative.ofAdd x) hx.le).2
  have hwhole (u : Multiplicative ℝ) :
      Integrable (fun h : C₁ ↦ F (τ (u, h)) * χ (h : C)) m :=
    (le_total 0 u.toAdd).elim (fun hu ↦ ((hlarge 0).choose_spec.2 u hu).1)
      (fun hu ↦ ((hsmall 0).choose_spec.2 u hu).1)
  -- Dominate both the weighted integrand and its derivative locally in `s`.
  have hlocal (s : ℂ) : Integrable (fun x : ℝ ↦ p x * Complex.exp (s * x)) ∧
      Integrable (fun x : ℝ ↦ (x : ℂ) * (p x * Complex.exp (s * x))) ∧
      HasDerivAt (fun w : ℂ ↦ ∫ x : ℝ, p x * Complex.exp (w * x))
        (∫ x : ℝ, (x : ℂ) * (p x * Complex.exp (s * x))) s := by
    obtain ⟨B, hB, htail⟩ := norm_logMellin_mul_exp_le_of_two_tails
      measureReal_nonneg hpLarge hpSmall s
    exact hasDerivAt_logMellin_of_measurable_decay hp s (r := 1) zero_lt_one hB
      (by simpa only [mul_one] using htail)
  exact ⟨hwhole, hp, fun s ↦ (hlocal s).2.2.differentiableAt, hlocal⟩

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [BorelSpace (ideleNormOne (K := K))]

/-- The fixed Gaussian, norm-one Haar and periodization of the above-one
radial Euler calculation also realize the entire corrected transform.
Apply `ideleHeckeGaussian_correctedRadialMellin_entire` to these same
witnesses for absolute convergence and the derivative integral. In the
right half-plane the *uncorrected* log integral has the raw discriminant
factor, exactly as in the multiplicatively tagged log line. No equality
of the corrected integral with the Euler product is asserted. -/
public theorem exists_discriminantNormalizedIdeleHeckeGaussian_correctedRadialMellin
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ (T : Finset V) (ν : Measure I₁) (F : C → ℂ) (E : Finset V) (μ : Measure A),
      let f := adeleHeckeTest χ T (archimedeanHeckeSchwartz χ hχ)
      let m := η₁ ν v r
      let p := ideleClassCorrectedLogProfile m F χ (f 0) (adeleFourier μ f 0)
      (∀ w ∉ T, χ.IsUnramifiedAt w ∧ multiplicity w.asIdeal D = 0) ∧
      μ.IsAddHaarMeasure ∧
      (∀ S : Finset V, E ⊆ S →
        μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S) ∧
      m.IsHaarMeasure ∧
      m Set.univ = (classNumber K : ℝ≥0∞) *
        (ENNReal.ofReal (regulator K) *
          (((2 : ℝ≥0∞) ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K) /
            (torsionOrder K : ℝ≥0∞))) *
        ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹) ∧
      Measurable F ∧ (∀ g : I, F (q g) = ∑' a : Kˣ, ideleHeckeGaussian χ hχ T (d a * g)) ∧
      Differentiable ℂ (fun s : ℂ ↦ ∫ x : ℝ, p x * Complex.exp (s * x)) ∧
      ∀ s : ℂ, 1 < s.re →
        let M (x : ℝ) := (χ (τ (Multiplicative.ofAdd x, 1)) * Complex.exp (s * x)) *
          ideleClassRadialPairing m F χ.toMonoidHom (Multiplicative.ofAdd x)
        Integrable M ∧ (∫ x : ℝ, M x) =
          (((Real.sqrt ((discr K).natAbs : ℝ))⁻¹ : ℝ) : ℂ) * completedHeckeEulerProduct χ hχ s := by
  classical
  -- Reuse the periodization and norm-one measure from the Euler identity.
  obtain ⟨T, _, ν, F, hT, _, _, _, _, hη₁, hmass, _, hF, hperiod, _, _, hEuler⟩ :=
    exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin χ hχ v r hr
  -- The additive transform needs its own cofinal-stage normalization.
  obtain ⟨E, hE⟩ := exists_finiteCompletionIntegerMass_exceptions K
  obtain ⟨μ, hμ, _, hstage, _⟩ := exists_adeleRestrictedProductHaar K E
    (fun w hw ↦ not_not.mp (fun hn ↦ hw ((hE w).mpr hn)))
  let : μ.IsAddHaarMeasure := hμ
  have hcofinal := (hstage μ).mp rfl
  have hentire := ideleHeckeGaussian_correctedRadialMellin_entire χ hχ T μ E hcofinal ν v r hη₁
    hF hperiod
  refine ⟨T, ν, F, E, μ, hT, hμ, hcofinal, hη₁, hmass, hF, hperiod, hentire.2.2.1, ?_⟩
  intro s hs
  obtain ⟨_, hi, heq⟩ := hEuler s hs
  -- `toAdd` pushes `dt/t` in log coordinates to real Lebesgue measure, with no scale factor.
  let M (x : ℝ) := (χ (τ (Multiplicative.ofAdd x, 1)) * Complex.exp (s * x)) *
    ideleClassRadialPairing (η₁ ν v r) F χ.toMonoidHom (Multiplicative.ofAdd x)
  change Integrable M ∧ (∫ x : ℝ, M x) = _
  have hi' : Integrable (M ∘ Multiplicative.toAdd) logVolume := by
    simpa only [M, Function.comp_def, ofAdd_toAdd, mul_comm s] using hi
  let e : Multiplicative ℝ ≃ᵐ ℝ := MeasurableEquiv.multiplicative.symm
  have hm : MeasurePreserving e logVolume volume := ⟨e.measurable, map_toAdd_logVolume⟩
  refine ⟨(hm.integrable_comp_emb e.measurableEmbedding).mp hi', ?_⟩
  calc
    _ = ∫ x : ℝ, M x ∂(logVolume.map e) := by rw [hm.map_eq]
    _ = ∫ u, (M ∘ Multiplicative.toAdd) u ∂logVolume := integral_map_equiv e M
    _ = _ := by simpa only [M, Function.comp_def, ofAdd_toAdd, mul_comm s] using heq

end Masullo
