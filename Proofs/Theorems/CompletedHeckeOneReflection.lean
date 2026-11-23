module

public import Theorems.IdeleClassGaussianContinuation
public import Theorems.CompletedHeckeRightLineGrowth
import Theorems.IdeleClassGaussianReflection
import all Theorems.IdeleClassRadialMellin -- For unfolding the norm-one pairing.
import Props.HeckeContourReflection
import Lemmas.CenteredLogMellinReflection
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # The discriminant factor for the continued trivial Hecke product

The radial integral (3.2.2.4)–(5), p. 125, uses the norm-one pairing of
(2.2.5.2), p. 95, and the large-norm estimate (2.2.5.9), p. 97. The
checked Gaussian reflection, based on (2.2.3.7), p. 83, centers this pairing
at minus half the log discriminant. Splitting there and retaining both zero
terms gives a symmetric Mellin expression. As in the use of (3.2.2.11),
p. 127, we compare on the right half-plane and use the identity theorem;
comparing entire pole-cleared numerators identifies the same continuation
used on the horizontal edges.

Proposition 3.2.1.3(3), p. 123, states a functional equation with a
nonvanishing entire epsilon factor and cites its local factors. For the
trivial character we instead derive the exact discriminant exponential
needed in (B.4.2.3), p. 614. The reflected logarithmic derivative and
conductor term both carry a minus sign. Source reading: Provisional,
from pinned Markdown and numbered PDF layout.
-/

open Complex Filter IsDedekindDomain MeasureTheory NumberField
open NumberField.InfinitePlace (nrComplexPlaces)
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Masullo.AdeleStage Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I₁" => ideleNormOne (K := K)
local notation "CK" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)
local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)
local notation "W" => (w₀ : InfinitePlace K)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)
local notation "δ" => Real.log (Int.natAbs (discr K) : ℝ)

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

/-- Keep the two numerator values in the centered calculation, before
forgetting the origin and positivity of the zero-mode coefficient. -/
private theorem completedHecke_one_centeredMellin_aux
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {L H : ℂ → ℂ}
    (hEuler : ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) :
    ∃ (J : ℂ → ℂ) (a : ℂ), Differentiable ℂ J ∧ 0 < a.re ∧
      H 0 = exp ((δ : ℂ) / 2) * a ∧ H 1 = a ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      L s = exp ((δ : ℂ) * (1 - s) / 2) * (J s + J (1 - s) + a / (s - 1) - a / s) := by
  classical
  obtain ⟨T, ν, F, E, μ, _, hμ, hstage, hm, _, hF, hperiod, _, hraw⟩ :=
    exists_discriminantNormalizedIdeleHeckeGaussian_correctedRadialMellin
      χ₀ (fun _ ↦ norm_one) v r hr
  let m := ideleClassNormOneQuotientMeasure ν v r
  let : m.IsHaarMeasure := hm
  let : μ.IsAddHaarMeasure := hμ
  let : CompactSpace C₁ := (compactHausdorff_ideleClassNormOne (K := K)).1
  let P (x : ℝ) := ∫ h : C₁, F (τ (Multiplicative.ofAdd x, h)) ∂m
  let a : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ nrComplexPlaces K * (m.real Set.univ : ℂ)
  have hpair (x : ℝ) :
      ideleClassRadialPairing m F (ContinuousMonoidHom.toMonoidHom χ₀) (Multiplicative.ofAdd x) = P x := by
    simp [P, ideleClassRadialPairing]
  have hP : Measurable P := by
    have hprod : Measurable (fun uh : ℝ × C₁ ↦ F (τ (Multiplicative.ofAdd uh.1, uh.2))) :=
      hF.comp ((τ).continuous.measurable.comp
        ((measurable_ofAdd.comp measurable_fst).prodMk measurable_snd))
    exact (hprod.stronglyMeasurable.integral_prod_right' (ν := m)).measurable
  have hdecay (N : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 ≤ x →
      ‖P x‖ ≤ B * Real.exp (-(N : ℝ) * x) := by
    obtain ⟨B, hB, htail⟩ := ideleHeckeGaussian_radialPairing_rapidDecay
      χ₀ (fun _ ↦ norm_one) T ν v r hm hF hperiod N
    refine ⟨B * m.real Set.univ, mul_nonneg hB.le measureReal_nonneg, fun x hx ↦ ?_⟩
    simpa only [← show m = ideleClassNormOneQuotientMeasure ν v r from rfl, hpair, toAdd_ofAdd,
      mul_right_comm B] using (htail (Multiplicative.ofAdd x) hx).2
  have hslice (x : ℝ) : Integrable (fun h : C₁ ↦ F (τ (Multiplicative.ofAdd x, h))) m := by
    have hs := (ideleHeckeGaussian_correctedRadialMellin_entire
      χ₀ (fun _ ↦ norm_one) T μ E hstage ν v r hm hF hperiod).1 (Multiplicative.ofAdd x)
    simpa using hs
  have hreflect := ideleHeckeGaussian_one_radialPairing_reflection T m F hperiod hslice
  have hright (s : ℂ) (hs : 1 < s.re) :
      Integrable (fun x : ℝ ↦ P x * exp (s * x)) ∧
      (∫ x : ℝ, P x * exp (s * x)) =
        ((Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ)⁻¹ * L s := by
    have htriv (a : CK) : χ₀ a = 1 := rfl
    simpa only [← show m = ideleClassNormOneQuotientMeasure ν v r from rfl,
      hpair, htriv, one_mul, mul_comm (exp (s * _)), Complex.ofReal_inv,
      ← hEuler s hs] using hraw s hs
  let J (s : ℂ) := ∫ y in Set.Ici (0 : ℝ), P (y - δ / 2) * exp (s * y)
  obtain ⟨hJ, hsplit⟩ := centeredLogMellin_split hP hdecay hreflect (fun s hs ↦ (hright s hs).1)
  have hD : 0 < ((discr K).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hsqrt : ((Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) = exp ((δ : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hD, Complex.ofReal_exp, Complex.ofReal_mul,
      show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num]
    congr 1
    ring
  let M (s : ℂ) := exp ((δ : ℂ) * (1 - s) / 2) * (J s + J (1 - s) + a / (s - 1) - a / s)
  -- Above one, the raw integral has the inverse square root discriminant.
  have hagree (s : ℂ) (hs : 1 < s.re) : L s = M s := by
    have h := (hright s hs).2.symm.trans (hsplit s hs)
    rw [hsqrt] at h
    have he := exp_ne_zero ((δ : ℂ) / 2)
    have h' := congrArg (exp ((δ : ℂ) / 2) * ·) h
    rw [← mul_assoc, mul_inv_cancel₀ he, one_mul, ← mul_assoc, ← exp_add] at h'
    simpa only [M, show (δ : ℂ) / 2 + -(δ : ℂ) / 2 * s = (δ : ℂ) * (1 - s) / 2 by ring] using h'
  -- Compare entire functions so there is no issue with the assigned pole values.
  let G (s : ℂ) := exp ((δ : ℂ) * (1 - s) / 2) *
    ((s - 1) * s * (J s + J (1 - s)) + s * a - (s - 1) * a)
  have hG : Differentiable ℂ G := by
    change Differentiable ℂ J at hJ
    dsimp only [G]
    fun_prop
  have hpoly (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : G s = (s - 1) * s * M s := by
    dsimp only [G, M]
    field_simp [hs₀, sub_ne_zero.mpr hs₁]
  have hEq : Set.EqOn H G Set.univ := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun s _ ↦ hH.analyticAt s) (fun s _ ↦ hG.analyticAt s) isPreconnected_univ
    (z₀ := (2 : ℂ)) (Set.mem_univ _) (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (by norm_num : 1 < (2 : ℂ).re)] with s hs
      have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
      have hs₁ : s ≠ 1 := by rintro rfl; norm_num at hs
      rw [hclear s hs₀ hs₁, hpoly s hs₀ hs₁, hagree s hs])
  refine ⟨J, a, hJ, ?_, ?_, ?_, fun s hs₀ hs₁ ↦ ?_⟩
  · have hmpos : 0 < m.real Set.univ := ENNReal.toReal_pos
      (isOpen_univ.measure_pos m Set.univ_nonempty).ne'
      (isCompact_univ.measure_lt_top (μ := m)).ne
    rw [show a = (((1 / (2 * Real.pi)) ^ nrComplexPlaces K * m.real Set.univ : ℝ) : ℂ) by
      rw [ofReal_mul, ofReal_pow], ofReal_re]
    positivity
  · rw [hEq (Set.mem_univ (0 : ℂ))]
    simp [G]
  · rw [hEq (Set.mem_univ (1 : ℂ))]
    simp [G]
  · apply mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.mpr hs₁) hs₀)
    exact (hclear s hs₀ hs₁).symm.trans ((hEq (Set.mem_univ s)).trans (hpoly s hs₀ hs₁))

/-- The continued trivial Euler product equals the symmetric centered
Mellin expression away from the two possible poles. The proof takes the
entire pole-cleared numerator of the given `L`, not a new witness. -/
public theorem completedHecke_one_centeredMellin
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {L H : ℂ → ℂ}
    (hEuler : ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) :
    ∃ (J : ℂ → ℂ) (a : ℂ), Differentiable ℂ J ∧ ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      L s = exp ((δ : ℂ) * (1 - s) / 2) * (J s + J (1 - s) + a / (s - 1) - a / s) := by
  obtain ⟨J, a, hJ, _, _, _, hM⟩ := completedHecke_one_centeredMellin_aux v r hr hEuler hH hclear
  exact ⟨J, a, hJ, hM⟩

/-- Theorem 3.2.2.1(1a), p. 124, gives the zeta integral's residues in terms
of its two zero modes. For the completed trivial Euler product used in
(B.4.2.2), p. 614, the centered formula calculates the values after pole
clearing. The value at one is positive by the nonzero Gaussian zero mode
and the positive, finite Haar mass of the compact norm-one quotient. -/
public theorem completedHecke_one_poleCleared_values
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {L H : ℂ → ℂ}
    (hEuler : ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s) :
    0 < (H 1).re ∧ H 0 = exp ((δ : ℂ) / 2) * H 1 := by
  obtain ⟨_, a, _, ha, h₀, h₁, _⟩ := completedHecke_one_centeredMellin_aux v r hr hEuler hH hclear
  exact ⟨h₁ ▸ ha, h₀.trans (congrArg _ h₁.symm)⟩

/-- The conductor reflection as an equality of germs at each ordinary
point, with the same `L` on both sides. -/
public theorem completedHecke_one_reflection
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {L H : ℂ → ℂ}
    (hEuler : ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s)
    (z : ℂ) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) :
    (fun s ↦ L (1 - s)) =ᶠ[𝓝 z] (fun s ↦ exp ((δ : ℂ) * (s - 1 / 2)) * L s) := by
  obtain ⟨J, a, _, hM⟩ := completedHecke_one_centeredMellin v r hr hEuler hH hclear
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({0} : Set ℂ)ᶜ from hz₀),
    isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({1} : Set ℂ)ᶜ from hz₁)] with s hs₀ hs₁
  change s ≠ 0 at hs₀
  change s ≠ 1 at hs₁
  have h₀ : 1 - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  have h₁ : 1 - s ≠ 1 := by intro h; apply hs₀; linear_combination -h
  change L (1 - s) = _
  rw [hM (1 - s) h₀ h₁, hM s hs₀ hs₁, ← mul_assoc, ← exp_add, sub_sub_cancel]
  have hexp : (δ : ℂ) * (s - 1 / 2) + (δ : ℂ) * (1 - s) / 2 = (δ : ℂ) * s / 2 := by ring
  rw [hexp]
  congr 1
  rw [show 1 - s - 1 = -s by ring, show 1 - s = -(s - 1) by ring, div_neg, div_neg]
  ring

/-- Corrected reflection transfers both nonvanishing and the linear
logarithmic-derivative bound from the right line to the actual left line. -/
public theorem completedHecke_one_leftLine_nonzero_logDeriv_bound
    (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) {L H : ℂ → ℂ}
    (hEuler : ∀ s, 1 < s.re → L s = completedHeckeEulerProduct χ₀ (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s)
    (hL : ∀ s, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ L s) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, let z : ℂ := -1 + (t : ℂ) * Complex.I
      L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ B * (1 + |t|) := by
  obtain ⟨B, hB, hright⟩ := completedHecke_rightLine_nonzero_logDeriv_bound
    χ₀ (fun _ ↦ norm_one) hEuler (a := 2) (by norm_num)
  refine ⟨B + ‖(δ : ℂ)‖, by positivity, fun t ↦ ?_⟩
  dsimp only
  let z : ℂ := -1 + (t : ℂ) * Complex.I
  have hre : z.re = -1 := by simp [z, Complex.mul_re]
  have hrre : (1 - z).re = 2 := by norm_num [hre]
  have hz₀ : z ≠ 0 := fun h ↦ by norm_num [h] at hre
  have hz₁ : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have hw₀ : 1 - z ≠ 0 := fun h ↦ by norm_num [h] at hrre
  have hw₁ : 1 - z ≠ 1 := fun h ↦ by norm_num [h] at hrre
  have hw : 1 - z = (2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; dsimp [z]; ring
  have hright' : L (1 - z) ≠ 0 ∧ ‖logDeriv L (1 - z)‖ ≤ B * (1 + |t|) := by
    rw [hw]
    simpa only [abs_neg, Complex.ofReal_ofNat] using hright (-t)
  have hFE := completedHecke_one_reflection v r hr hEuler hH hclear z hz₀ hz₁
  have hnz : L z ≠ 0 := by
    intro hz
    apply hright'.1
    simpa only [hz, mul_zero] using hFE.eq_of_nhds
  have hlog := completed_logDeriv_reflection (C := (1 : ℂ)) (κ := (δ : ℂ))
    one_ne_zero (hL z hz₀ hz₁) (hL (1 - z) hw₀ hw₁) hnz (by simpa only [one_mul] using hFE)
  refine ⟨hnz, ?_⟩
  calc
    ‖logDeriv L z‖ ≤ ‖logDeriv L (1 - z)‖ + ‖(δ : ℂ)‖ := by
      rw [hlog]
      exact (norm_sub_le _ _).trans_eq (by rw [norm_neg])
    _ ≤ (B + ‖(δ : ℂ)‖) * (1 + |t|) := by
      nlinarith [hright'.2, mul_nonneg (norm_nonneg (δ : ℂ)) (abs_nonneg t)]

end Masullo
