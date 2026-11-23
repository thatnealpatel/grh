module

public import Theorems.CompletedHeckeOneContour
import Lemmas.TrivialHeckeGammaFactor
import Theorems.FiniteHeckeRightLineInversion
import Props.ArchimedeanGammaRightLine
import Props.HeckeContourReflection
import Mathlib.Tactic.Ring

/-! # The trivial Hecke explicit formula in unshifted log coordinates

This is the compact-log, trivial-character specialization of the assembly
in §B.4.2.4, p. 616, before the half-translation of (B.4.2.17). It uses
one continuation, the corrected conductor reflection of (B.4.2.3)–(4),
the split (B.4.2.5)–(7), and the two finite-place inversions of
(B.4.2.10)–(11), pp. 614–615. At infinity the absolutely integrable Gauss
difference and the Gamma contact replace (B.4.2.15), p. 616. This is
not an identification of the local terms with a global operator trace.
Source readings are provisional (Markdown and numbered PDF layout).
-/

open Complex Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)
local notation "Γ₀" => localHeckeGammaFactor χ₀ (fun _ ↦ norm_one)
local notation "P₀" => completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one)
local notation "F₀" => finiteHeckeCharacterEulerProduct χ₀
local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "κ₀" => (Real.log (Int.natAbs (discr K) : ℝ) : ℂ)

/-- Exponential subtraction on the positive log half-line in the real
(`d = 2`) and complex (`d = 1`) trivial-character terms. -/
@[expose] public noncomputable def trivialHeckeGammaKernel (d : ℝ) (g : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  (2 * g 0 * exp (-(d : ℂ) * (x : ℂ)) - g x - exp (-(x : ℂ)) * g (-x)) /
    (1 - exp (-(d : ℂ) * (x : ℂ)))

/-- The two tested legs of one Archimedean factor, with base `π` and
step `2` at a real place and base `2π` and step `1` at a complex place. -/
@[expose] public noncomputable def trivialHeckeGammaContribution (v : InfinitePlace K)
    (g : ℝ → ℂ) : ℂ := by
  classical
  let d : ℝ := if v.IsReal then 2 else 1
  let B : ℝ := if v.IsReal then Real.pi else 2 * Real.pi
  exact -((Real.log B : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / (d : ℂ) * (2 * g 0) +
    ∫ x in Ioi (0 : ℝ), trivialHeckeGammaKernel d g x

private theorem finiteHeckeCoefficient_one (v : Places) : finiteHeckeCoefficient χ₀ v = 1 := by
  classical
  have h (x : (v.adicCompletion K)ˣ) : HeckeCharacter.restrict χ₀ v x = 1 := by
    simp [HeckeCharacter.restrict]
  have hu : HeckeCharacter.IsUnramifiedAt χ₀ v := HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
    h ((Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom) x)
  obtain ⟨π, hπ⟩ := (Valued.v : Valuation (v.adicCompletion K)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  rw [finiteHeckeCoefficient, ite_eq_left hu, hu.localValue_eq π hπ]
  exact h (Units.mk0 π hπ.ne_zero)

private theorem trivial_pair_gamma (v : InfinitePlace K) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
    let W (t : ℝ) := (compactLogMellin g (s t) + compactLogMellin g (1 - s t)) *
      logDeriv (Γ₀ v) (s t)
    Integrable W ∧
      (∫ t, W t) / (2 * (Real.pi : ℂ)) = trivialHeckeGammaContribution v g := by
  classical
  have h {d B : ℝ} (hd : 0 < d) :=
    compactLogMellin_archimedeanGamma_pair hg hc (a := 2) (by norm_num) hd
      (b := 0) le_rfl B 0
  rcases v.isReal_or_isComplex with hv | hv
  · rw [localHeckeGammaFactor_one_real hv]
    simpa [trivialHeckeGammaContribution, hv, trivialHeckeGammaKernel, add_mul] using
      (h (B := Real.pi) (d := 2) (by norm_num)).imp (fun h ↦ h) (fun h ↦ h.2)
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mpr hv
    rw [localHeckeGammaFactor_one_complex hv]
    simpa [trivialHeckeGammaContribution, hv', trivialHeckeGammaKernel, add_mul] using
      (h (B := 2 * Real.pi) (d := 1) one_pos).imp (fun h ↦ h) (fun h ↦ h.2)

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

/-- The trivial-character formula for every smooth compact log profile.
The pole-cleared numerator indexes the full ordinary zero divisor. Both
infinite series and every positive-log Gamma integral are absolute. -/
public theorem exists_completedHecke_one_explicitFormula
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    ∃ L H : ℂ → ℂ,
      Meromorphic L ∧
      (∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s) ∧
      (∀ s, 1 < s.re → L s = P₀ s) ∧
      Differentiable ℂ H ∧
      (∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) ∧
      (∀ z, H z = 0 → z ≠ 0 ∧ z ≠ 1 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ L z = 0 ∧
        analyticOrderNatAt H z = analyticOrderNatAt L z) ∧
      (∀ z, z ≠ 0 → z ≠ 1 → L z = 0 → H z = 0) ∧
      (∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
        let Φ := compactLogMellin g
        let W := fun (z : {z : ℂ // H z = 0}) ↦ (analyticOrderNatAt H z.val : ℂ) * Φ z.val
        let A := fun p : Places × ℕ ↦
          let l := Real.log (finitePlaceNorm p.1)
          let y : ℝ := (p.2 + 1 : ℕ) * l
          (l : ℂ) * (g y + exp (-y) * g (-y))
        Summable (fun z ↦ ‖W z‖) ∧ Summable (fun p ↦ ‖A p‖) ∧
          IntegrableOn (trivialHeckeGammaKernel 2 g) (Ioi 0) ∧
          IntegrableOn (trivialHeckeGammaKernel 1 g) (Ioi 0) ∧
          (∑' z, W z) - Φ 0 - Φ 1 =
            κ₀ * g 0 - (∑' p, A p) + ∑ w : InfinitePlace K, trivialHeckeGammaContribution w g) := by
  classical
  obtain ⟨L, H, hL, hdiffL, hEuler, hH, hclear, hzeros, hzeros', hcontour⟩ :=
    exists_completedHecke_one_contour_identity v r hr
  refine ⟨L, H, hL, hdiffL, hEuler, hH, hclear, hzeros, hzeros', fun g hg hc ↦ ?_⟩
  obtain ⟨hD₀, _, hzeroSum, hcontour⟩ := hcontour g hg hc
  let c : ℂ := 2 * (Real.pi : ℂ)
  let s (t : ℝ) : ℂ := 2 + (t : ℂ) * I
  let Φ := compactLogMellin g
  let D (t : ℝ) : ℂ := Φ (s t) * logDeriv L (s t)
  let R (t : ℝ) : ℂ := Φ (1 - s t) * logDeriv L (s t)
  let p (t : ℝ) : ℂ := Φ (s t) + Φ (1 - s t)
  have hs (t : ℝ) : 1 < (s t).re := by norm_num [s, Complex.mul_re]
  have hsplit (z : ℂ) (hz : 1 < z.re) :
      logDeriv L z = logDeriv F₀ z + ∑ w : InfinitePlace K, logDeriv (Γ₀ w) z := by
    -- (B.4.2.5): Equality on the open half-plane is equality of germs.
    have heq : L =ᶠ[𝓝 z] P₀ := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with z hz
      exact hEuler z hz
    have h := (completedHeckeEulerProduct_logDeriv χ₀ (fun _ ↦ norm_one) hz).2.2.unique
      (finiteHeckeCharacterEulerProduct_logDeriv χ₀ (fun _ ↦ norm_one) hz).2.2
    rw [(logDeriv_congr_nhds heq).eq_of_nhds]
    linear_combination -h
  -- (B.4.2.10)–(11): Both finite-place legs have trivial coefficients.
  have hχ : heckeConjugate χ₀ = χ₀ := by
    ext x
    exact map_one (starRingEnd ℂ)
  obtain ⟨hFD, hFR, hfiniteSum, hfinite⟩ :=
    finiteHecke_paired_right_line (K := K) (a := 2) (by norm_num) χ₀ (fun _ ↦ norm_one) hg hc
  simp only [hχ, finiteHeckeCoefficient_one, map_one, one_pow, one_mul,
    ofReal_ofNat] at hFD hFR hfiniteSum hfinite
  -- (B.4.2.13): Evaluate each infinite factor in the corrected Gauss form.
  let G (w : InfinitePlace K) (t : ℝ) : ℂ := p t * logDeriv (Γ₀ w) (s t)
  have hG (w : InfinitePlace K) : Integrable (G w) ∧
      (∫ t, G w t) / c = trivialHeckeGammaContribution w g := trivial_pair_gamma w hg hc
  have hright (q : ℝ → ℂ) (hq : Integrable fun t ↦ q t * logDeriv F₀ (s t))
      (hΓ : ∀ w : InfinitePlace K, Integrable fun t ↦ q t * logDeriv (Γ₀ w) (s t)) :
      Integrable fun t ↦ q t * logDeriv L (s t) := by
    refine (hq.add (integrable_finsetSum Finset.univ fun w _ ↦ hΓ w)).congr (Eventually.of_forall fun t ↦ ?_)
    simp only [Pi.add_apply, hsplit _ (hs _), mul_add, Finset.mul_sum]
  have hR : Integrable R := hright (fun t ↦ Φ (1 - s t)) hFR (fun w ↦ by
    rcases w.isReal_or_isComplex with hw | hw
    · rw [localHeckeGammaFactor_one_real hw]
      simpa using (compactLogMellin_archimedeanGamma_reflected hg hc (a := 2) (by norm_num)
        (d := 2) (by norm_num) (b := 0) le_rfl Real.pi 0).1
    · rw [localHeckeGammaFactor_one_complex hw]
      simpa using (compactLogMellin_archimedeanGamma_reflected hg hc (a := 2) (by norm_num)
        (d := 1) one_pos (b := 0) le_rfl (2 * Real.pi) 0).1)
  -- (B.4.2.4): Reflect the left line of this continuation, with +κ₀g(0)
  -- when its upward integral is subtracted.
  have hlog (t : ℝ) : let z : ℂ := -1 + (t : ℂ) * I
      logDeriv L z = -logDeriv L (1 - z) - κ₀ := by
    dsimp only
    let z : ℂ := -1 + (t : ℂ) * I
    have hz : z.re = -1 := by simp [z, Complex.mul_re]
    have hw : (1 - z).re = 2 := by norm_num [hz]
    have hz₀ : z ≠ 0 := fun h ↦ by norm_num [h] at hz
    have hz₁ : z ≠ 1 := fun h ↦ by norm_num [h] at hz
    have hw₀ : 1 - z ≠ 0 := fun h ↦ by norm_num [h] at hw
    have hw₁ : 1 - z ≠ 1 := fun h ↦ by norm_num [h] at hw
    have hFE := completedHecke_one_reflection v r hr hEuler hH hclear z hz₀ hz₁
    have hnz : L z ≠ 0 := by
      intro h
      have hright : L (1 - z) ≠ 0 := by
        have h' : 1 < (1 - z).re := by norm_num [hw]
        rw [hEuler _ h']
        exact (completedHeckeEulerProduct_logDeriv χ₀ (fun _ ↦ norm_one) h').1
      exact hright (by simpa only [h, mul_zero] using hFE.eq_of_nhds)
    exact completed_logDeriv_reflection (C := (1 : ℂ)) one_ne_zero (hdiffL z hz₀ hz₁)
      (hdiffL (1 - z) hw₀ hw₁) hnz (by simpa only [one_mul] using hFE)
  have hzreal : ((1 - 2 : ℝ) : ℂ) = -1 := by norm_num
  have href := (completed_reflect_left_integral (F := L) (G := L) (κ := κ₀) 2 hg hc
    (by simpa only [hzreal] using hlog) (by simpa only [ofReal_ofNat] using hR)).2
  simp only [hzreal, ofReal_ofNat] at href
  have hD : Integrable D := hD₀
  have hpair (t : ℝ) : D t + R t =
      (Φ (s t) * logDeriv F₀ (s t) + Φ (1 - s t) * logDeriv F₀ (s t)) + ∑ w, G w t := by
    simp only [D, R, hsplit _ (hs _), G, p, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
    abel
  have heval := congrArg (fun z : ℂ ↦ z / c) (congrArg (fun f : ℝ → ℂ ↦ ∫ t, f t) (funext hpair))
  change (∫ t, D t + R t) / c = _ at heval
  rw [integral_add hD hR, add_div] at heval
  have hF : Integrable (fun t ↦ Φ (s t) * logDeriv F₀ (s t) +
      Φ (1 - s t) * logDeriv F₀ (s t)) := by
    exact (hFD.add hFR).congr (Eventually.of_forall fun t ↦ rfl)
  rw [integral_add hF (integrable_finsetSum Finset.univ fun w _ ↦ (hG w).1),
    add_div, hfinite, integral_finsetSum _ (fun w _ ↦ (hG w).1), Finset.sum_div] at heval
  simp_rw [(hG _).2] at heval
  refine ⟨hzeroSum, hfiniteSum, ?_, ?_, ?_⟩
  · refine ((compactLogMellin_archimedeanGamma_pair hg hc (a := 2) (by norm_num) (d := 2)
      (by norm_num) (b := 0) le_rfl Real.pi 0).2.1).congr (Eventually.of_forall fun x ↦ ?_)
    simp [trivialHeckeGammaKernel]
  · refine ((compactLogMellin_archimedeanGamma_pair hg hc (a := 2) (by norm_num) (d := 1)
      one_pos (b := 0) le_rfl (2 * Real.pi) 0).2.1).congr (Eventually.of_forall fun x ↦ ?_)
    simp [trivialHeckeGammaKernel]
  dsimp only at hcontour href ⊢
  -- Substitute the tested reflection and the evaluated right-hand pair.
  let V (t : ℝ) : ℂ := Φ (-1 + (t : ℂ) * I) * logDeriv L (-1 + (t : ℂ) * I)
  simp only [ofReal_neg, ofReal_one, ofReal_ofNat] at hcontour
  change ((∫ t, D t) - (∫ t, V t)) / c = _ at hcontour
  change (∫ t, V t) / c = -((∫ t, R t) / c) - κ₀ * g 0 at href
  rw [sub_div] at hcontour
  linear_combination heval - hcontour - href

end Masullo
