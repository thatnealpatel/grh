module

public import Theorems.IdeleClassGaussianCorrectedMellin
public import Mathlib.Analysis.Meromorphic.Basic
import all Theorems.IdeleClassGaussianCorrectedMellin -- For unfolding the corrected profile.
import Theorems.IdeleClassMellinZeroModes
import Lemmas.OneParameterCharacter
import Lemmas.LogMellinStripBounds
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Meromorphic continuation of the completed fixed-Gaussian Euler product

Use the section character of (3.2.2.4)–(5), p. 125, in the coordinates
of (3.1.1.1), p. 119. Theorem 3.2.2.1(1a), p. 124, states the poles and
residues of the *zeta integral*, referring to global continuation on p. 126.
Here the entire corrected radial integral and the explicit integrals of the
removed modes give a continuation directly for this Gaussian. The Euler
identity above one carries an inverse square root discriminant, so the
completed product and its polar coefficients are rescaled together.
Source reading: Provisional, from pinned Markdown and numbered PDF layout.

For the growth input to §B.4.2.1, p. 614, we use the absolute Mellin
integrability from the two corrected/averaged tails (2.2.5.9)–(10),
pp. 97–98. Comparing with the two real endpoints gives a bound uniform
in height for the corrected integral, hence quadratic growth for the
pole-cleared numerator. This is an input to a moving-disk argument,
not a logarithmic derivative bound or the residue identity (B.4.2.2).
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

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]
  [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]
  [BorelSpace (ideleNormOne (K := K))]

/-- The entire corrected integral plus the two removed modes, on the same
Gaussian and Haar witnesses, extends the completed Euler product. The
entire pole-cleared numerator encodes at most simple poles and their
residues using only the values of `L` off the possible poles, and grows
at most quadratically in absolute height on each fixed closed vertical strip. -/
public theorem exists_completedHeckeEulerProduct_gaussianContinuation
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ a : C, ‖χ a‖ = 1)
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ (T : Finset V) (ν : Measure I₁) (F : C → ℂ) (E : Finset V) (μ : Measure A) (lam : ℝ),
      let f := adeleHeckeTest χ T (archimedeanHeckeSchwartz χ hχ)
      let m := η₁ ν v r
      let p := ideleClassCorrectedLogProfile m F χ (f 0) (adeleFourier μ f 0)
      let b : ℂ := if ∀ h : C₁, χ (h : C) = 1 then (m.real Set.univ : ℂ) else 0
      let a₁ := adeleFourier μ f 0 * b
      let a₀ := f 0 * b
      let z₀ := -((lam : ℂ) * Complex.I)
      let z₁ := 1 + z₀
      let D₀ : ℂ := (Real.sqrt ((discr K).natAbs : ℝ) : ℝ)
      let L (s : ℂ) := D₀ * ((∫ x : ℝ, p x * Complex.exp (s * x)) +
        a₁ / (s - z₁) - a₀ / (s - z₀))
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
      (∀ x : ℝ, χ (τ (Multiplicative.ofAdd x, 1)) =
        Complex.exp (((lam * x : ℝ) : ℂ) * Complex.I)) ∧
      Meromorphic L ∧
      (∀ s, s ≠ z₁ → s ≠ z₀ → DifferentiableAt ℂ L s) ∧
      ((∃ h : C₁, χ (h : C) ≠ 1) → Differentiable ℂ L) ∧
      (∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ hχ s) ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ H z₁ = D₀ * a₁ ∧ H z₀ = D₀ * a₀ ∧
        (∀ s, s ≠ z₁ → s ≠ z₀ → H s = (s - z₁) * (s - z₀) * L s) ∧
        ∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
          ‖H s‖ ≤ M * (1 + |s.im|)^2 := by
  classical
  let ψ := χ.comp (ideleClassLogSection W)
  have hsection (x : ℝ) : χ (τ (Multiplicative.ofAdd x, 1)) = ψ (Multiplicative.ofAdd x) := by
    rw [ideleClassLogSplit_apply, OneMemClass.coe_one, mul_one]
    rfl
  -- Identify the actual section phase, not just the norm of the phase.
  obtain ⟨lam, hlam, _⟩ := existsUnique_unitary_oneParameterCharacter
    (fun x ↦ ψ (Multiplicative.ofAdd x)) (ψ.continuous.comp continuous_ofAdd)
    (map_one ψ) (fun x y ↦ map_mul ψ (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))
    (fun x ↦ hχ _)
  have hphase (x : ℝ) := (hsection x).trans (hlam x)
  obtain ⟨T, ν, F, E, μ, hT, hμ, hstage, hm, hmass, hF, hperiod, hentire, hEuler⟩ :=
    exists_discriminantNormalizedIdeleHeckeGaussian_correctedRadialMellin χ hχ v r hr
  refine ⟨T, ν, F, E, μ, lam, ?_⟩
  dsimp only
  refine ⟨hT, hμ, hstage, hm, hmass, hF, hperiod, hphase, ?_⟩
  let f := adeleHeckeTest χ T (archimedeanHeckeSchwartz χ hχ)
  let m := η₁ ν v r
  let p := ideleClassCorrectedLogProfile m F χ (f 0) (adeleFourier μ f 0)
  let b : ℂ := if ∀ h : C₁, χ (h : C) = 1 then (m.real Set.univ : ℂ) else 0
  let a₁ := adeleFourier μ f 0 * b
  let a₀ := f 0 * b
  let z₀ := -((lam : ℂ) * Complex.I)
  let z₁ := 1 + z₀
  let D₀ : ℂ := (Real.sqrt ((discr K).natAbs : ℝ) : ℝ)
  let G (s : ℂ) := ∫ x : ℝ, p x * Complex.exp (s * x)
  let L (s : ℂ) := D₀ * (G s + a₁ / (s - z₁) - a₀ / (s - z₀))
  change Meromorphic L ∧ (∀ s, s ≠ z₁ → s ≠ z₀ → DifferentiableAt ℂ L s) ∧
    ((∃ h : C₁, χ (h : C) ≠ 1) → Differentiable ℂ L) ∧
    (∀ s, 1 < s.re → L s = _) ∧
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ H z₁ = D₀ * a₁ ∧ H z₀ = D₀ * a₀ ∧
      (∀ s, s ≠ z₁ → s ≠ z₀ → H s = (s - z₁) * (s - z₀) * L s) ∧
      ∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖H s‖ ≤ M * (1 + |s.im|)^2
  have hG : Differentiable ℂ G := hentire
  let : μ.IsAddHaarMeasure := hμ
  have htail := ideleHeckeGaussian_correctedRadialMellin_entire χ hχ T μ E hstage ν v r
    hm hF hperiod
  have hGp (s : ℂ) : Integrable (fun x : ℝ ↦ p x * Complex.exp (s * x)) := (htail.2.2.2 s).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    have hGm := (hG.analyticAt (z := s)).meromorphicAt
    have h₁ : MeromorphicAt (fun w : ℂ ↦ a₁ / (w - z₁)) s := by fun_prop
    have h₀ : MeromorphicAt (fun w : ℂ ↦ a₀ / (w - z₀)) s := by fun_prop
    exact (MeromorphicAt.const D₀ s).fun_mul ((hGm.fun_add h₁).fun_sub h₀)
  · intro s h₁ h₀
    change DifferentiableAt ℂ (fun w ↦ D₀ * (G w + a₁ / (w - z₁) - a₀ / (w - z₀))) s
    have h := hG s
    have h₁' := sub_ne_zero.mpr h₁
    have h₀' := sub_ne_zero.mpr h₀
    fun_prop
  · rintro ⟨c, hc⟩
    have hb : b = 0 := ite_eq_right (fun h ↦ hc (h c))
    simpa [L, a₁, a₀, hb] using hG.const_mul D₀
  · intro s hs
    -- Add back the integrable removed modes on the original half-plane.
    let Q (x : ℝ) := (if x < 0 then Real.exp (-x) • a₁ - a₀ else 0) *
      (Complex.exp (((lam * x : ℝ) : ℂ) * Complex.I) * Complex.exp (s * x))
    obtain ⟨hQi, hQ⟩ := integral_logMellin_zeroModes a₁ a₀ lam s hs
    change Integrable Q at hQi
    have hz₁ : s + (lam : ℂ) * Complex.I - 1 = s - z₁ := by dsimp [z₁, z₀]; ring
    have hz₀ : s + (lam : ℂ) * Complex.I = s - z₀ := by dsimp [z₀]; ring
    have hsum (x : ℝ) : p x * Complex.exp (s * x) + Q x =
        (χ (τ (Multiplicative.ofAdd x, 1)) * Complex.exp (s * x)) *
          ideleClassRadialPairing m F χ.toMonoidHom (Multiplicative.ofAdd x) := by
      simp only [p, ideleClassCorrectedLogProfile, Q, ← hphase x]
      by_cases hx : x < 0
      · simp only [ite_eq_left hx, a₁, a₀, b, Complex.real_smul]
        ring
      · simp only [ite_eq_right hx, zero_mul, sub_zero, add_zero]
        ring
    have hval := (hEuler s hs).2
    rw [← show (fun x ↦ _) = (fun x ↦ _) from funext hsum] at hval
    rw [integral_add (hGp s) hQi, hQ, hz₁, hz₀] at hval
    have hD : D₀ ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by
      exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K))).ne'
    change G s + (a₁ / (s - z₁) - a₀ / (s - z₀)) = _ at hval
    rw [Complex.ofReal_inv] at hval
    dsimp only [L]
    rw [add_sub_assoc, hval]
    have hinv : D₀ * D₀⁻¹ = 1 := mul_inv_cancel₀ hD
    rw [← mul_assoc, hinv, one_mul]
  · -- Clearing the two distinct linear poles gives an entire numerator.
    let H (s : ℂ) := D₀ * ((s - z₁) * (s - z₀) * G s + (s - z₀) * a₁ - (s - z₁) * a₀)
    refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [H]; fun_prop
    · have hz : z₁ - z₀ = 1 := by dsimp [z₁]; ring
      simp only [H, sub_self, zero_mul, zero_add, sub_zero, hz, one_mul]
    · have hz : z₀ - z₁ = -1 := by dsimp [z₁]; ring
      simp only [H, sub_self, mul_zero, zero_mul, add_zero, hz, neg_one_mul, zero_sub, neg_neg]
    · intro s h₁ h₀
      dsimp only [H, L]
      field_simp [sub_ne_zero.mpr h₁, sub_ne_zero.mpr h₀]
    · intro a b
      -- Use both endpoint integrands as one integrable majorant for the strip.
      let B := ∫ x : ℝ, ‖p x * Complex.exp ((a : ℂ) * x)‖ + ‖p x * Complex.exp ((b : ℂ) * x)‖
      have hB : 0 ≤ B := integral_nonneg fun _ ↦ by positivity
      have hGB (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b) : ‖G s‖ ≤ B :=
        (norm_integral_le_integral_norm _).trans
          (integral_mono (hGp s).norm ((hGp a).norm.add (hGp b).norm)
            (norm_logMellinIntegrand_le_endpoints p ha hb))
      let Cz (z : ℂ) := 1 + |a| + |b| + ‖z‖
      have hC (z : ℂ) : 0 ≤ Cz z := by dsimp [Cz]; positivity
      refine ⟨‖D₀‖ * (Cz z₁ * Cz z₀ * B + Cz z₀ * ‖a₁‖ + Cz z₁ * ‖a₀‖),
        by positivity, ?_⟩
      intro s ha hb
      let Y := 1 + |s.im|
      have hY : Y ≤ Y^2 := by dsimp [Y]; nlinarith [abs_nonneg s.im]
      have hlin (z : ℂ) : ‖s - z‖ ≤ Cz z * Y := norm_sub_le_verticalStrip z ha hb
      -- Estimate the polynomial formula directly, including at both possible poles.
      change ‖D₀ * ((s - z₁) * (s - z₀) * G s + (s - z₀) * a₁ - (s - z₁) * a₀)‖ ≤ _
      rw [Complex.norm_mul]
      calc
        _ ≤ ‖D₀‖ * (‖(s - z₁) * (s - z₀) * G s‖ + ‖(s - z₀) * a₁‖ + ‖(s - z₁) * a₀‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) (norm_nonneg _)
        _ ≤ ‖D₀‖ * (Cz z₁ * Y * (Cz z₀ * Y) * B + Cz z₀ * Y^2 * ‖a₁‖ + Cz z₁ * Y^2 * ‖a₀‖) := by
          simp only [Complex.norm_mul]
          have hlin' (z : ℂ) : ‖s - z‖ ≤ Cz z * Y^2 :=
            (hlin z).trans (mul_le_mul_of_nonneg_left hY (hC z))
          gcongr
          · exact hlin z₁
          · exact hlin z₀
          · exact hGB s ha hb
          · exact hlin' z₀
          · exact hlin' z₁
        _ = _ := by change _ = _ * Y^2; ring

end Masullo
