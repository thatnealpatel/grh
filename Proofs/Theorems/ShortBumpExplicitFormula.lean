module

public import Theorems.CompletedHeckeOneExplicitFormula
public import Theorems.ComplexRadialClassLocal
import Lemmas.FiniteHeckeMajorant
import Mathlib.Tactic.LinearCombination

/-!
# The short log bump in the trivial Hecke explicit formula

The half-shift of the Mellin exponent is supplied by twisting the profile by
`exp (-x/2)`. Neither leg of any finite-place sample meets its support. When
the only infinite place is complex, its Gamma contribution is the negative
of the positive-log local integral, with no further factor.
-/

open Complex IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff Topology

namespace Masullo
namespace ShortPositiveLogBump

/-- The short positive log profile with the half-shift used by the contour. -/
@[expose] public noncomputable def shiftedProfile (x : ℝ) : ℂ :=
  exp (-(x : ℂ) / 2) * (profile x : ℂ)

private theorem support_shiftedProfile_subset : Function.support shiftedProfile ⊆ Ioo a b :=
  fun _ hx ↦ support_profile_subset (fun h ↦ hx (by simp [shiftedProfile, h]))

private theorem shiftedProfile_eq_zero {x : ℝ} (hx : x ∉ Ioo a b) : shiftedProfile x = 0 :=
  not_not.mp (fun h ↦ hx (support_shiftedProfile_subset h))

private theorem shiftedProfile_zero : shiftedProfile 0 = 0 :=
  shiftedProfile_eq_zero (fun h ↦ a_pos.not_gt h.1)

private theorem contDiff_shiftedProfile : ContDiff ℝ ∞ shiftedProfile :=
  (contDiff_exp.comp (ofRealCLM.contDiff.neg.div_const 2)).mul
    (ofRealCLM.contDiff.comp contDiff_profile)

private theorem hasCompactSupport_shiftedProfile : HasCompactSupport shiftedProfile :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_shiftedProfile_subset.trans Ioo_subset_Icc_self)

/-- The unshifted contour transform of the twisted profile is the Mellin
pairing of the original profile at the centered exponent `s - 1/2`. -/
public theorem compactLogMellin_shiftedProfile (s : ℂ) :
    compactLogMellin shiftedProfile s =
      ∫ x : ℝ, (profile x : ℂ) * exp ((s - 1 / 2) * (x : ℂ)) := by
  unfold compactLogMellin
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only [shiftedProfile]
  rw [mul_comm (exp (-(x : ℂ) / 2)) (profile x : ℂ), mul_assoc, ← exp_add]
  congr 2
  ring

/-- Both sample arguments at each positive power of a finite place are outside
the short bump, including the reflected sample. -/
public theorem shiftedProfile_prime_samples {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    let y : ℝ := (n + 1 : ℕ) * Real.log (finitePlaceNorm v)
    shiftedProfile y = 0 ∧ shiftedProfile (-y) = 0 := by
  let l := Real.log (finitePlaceNorm v)
  have hq := two_le_finitePlaceNorm v
  have hl : Real.log 2 ≤ l :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) (zero_lt_two.trans_le hq) hq
  have hl₀ : 0 < l := Real.log_pos (one_lt_two.trans_le hq)
  have hy : l ≤ (n + 1 : ℕ) * l := by
    exact le_mul_of_one_le_left hl₀.le (by exact_mod_cast (Nat.succ_pos n : 1 ≤ n + 1))
  have hb : b < (n + 1 : ℕ) * l := b_lt_log_two.trans_le (hl.trans hy)
  have hpos : 0 < (n + 1 : ℕ) * l := hl₀.trans_le hy
  exact ⟨shiftedProfile_eq_zero (fun h ↦ hb.not_gt h.2),
    shiftedProfile_eq_zero (fun h ↦ (neg_neg_of_pos hpos).not_gt (a_pos.trans h.1))⟩

/-- The contact and reflected terms vanish at a complex place. Its direct
term has step `1` and is the negative of the existing local Gamma integral. -/
public theorem trivialHeckeGammaContribution_shiftedProfile
    {K : Type*} [Field K] [NumberField K] {v : InfinitePlace K} (hv : v.IsComplex) :
    trivialHeckeGammaContribution v shiftedProfile = -(gammaIntegral : ℂ) := by
  let f (x : ℝ) := profile x * (Real.exp (-x / 2) / (1 - Real.exp (-x)))
  have hout (x : ℝ) (hx : x ∉ Ioo a b) : (f x : ℂ) = 0 := by
    have hp : profile x = 0 := (profile_eq x).trans (ite_eq_right hx)
    simp only [f, hp, zero_mul, ofReal_zero]
  have hIoi (x : ℝ) (hx : x ∉ Ioi (0 : ℝ)) : (f x : ℂ) = 0 :=
    hout x (fun h ↦ hx (a_pos.trans h.1))
  have hreal := InfinitePlace.not_isReal_iff_isComplex.mpr hv
  simp only [trivialHeckeGammaContribution, ite_eq_right hreal, shiftedProfile_zero, mul_zero,
    zero_add]
  calc
    _ = ∫ x in Ioi (0 : ℝ), -(f x : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hneg : shiftedProfile (-x) = 0 := shiftedProfile_eq_zero
        (fun h ↦ (neg_neg_of_pos (mem_Ioi.mp hx)).not_gt (a_pos.trans h.1))
      simp only [trivialHeckeGammaKernel, shiftedProfile_zero, hneg, mul_zero, zero_mul,
        zero_sub, sub_zero, ofReal_one, neg_mul, one_mul]
      simp only [shiftedProfile, f, ofReal_mul, ofReal_div, ofReal_exp, ofReal_neg, ofReal_sub,
        ofReal_one, ofReal_ofNat, neg_div]
      rw [← mul_div_assoc, mul_comm (profile x : ℂ)]
    _ = -(∫ x in Ioo a b, (f x : ℂ)) := by
      rw [integral_neg, setIntegral_eq_integral_of_forall_compl_eq_zero hIoi,
        setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    _ = -(gammaIntegral : ℂ) := by rw [integral_complex_ofReal]; rfl

variable {K : Type*} [Field K] [NumberField K]
  [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
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

local notation "P₀" => completedHeckeEulerProduct (1 : HeckeCharacter (𝓞 K) K) (fun _ ↦ norm_one)

/-- The explicit formula for the short bump when `v` is the only infinite
place and is complex. The absolute zero sum uses the full zero set of `H`
with its analytic orders and no normalization factor. The linked witness
facts also allow transport to the trivial-character strip sum. -/
public theorem exists_completedHecke_one_shortBump_hasSum
    (v : InfinitePlace K) (hv : v.IsComplex) (hunique : ∀ w : InfinitePlace K, w = v)
    (r : ClassGroup (𝓞 K) → ideleNormOne (K := K))
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
      let Φ := compactLogMellin shiftedProfile
      let W := fun (z : {z : ℂ // H z = 0}) ↦ (analyticOrderNatAt H z.val : ℂ) * Φ z.val
      Summable (fun z ↦ ‖W z‖) ∧ HasSum W (Φ 0 + Φ 1 - (gammaIntegral : ℂ)) := by
  classical
  obtain ⟨L, H, hL, hdiffL, hEuler, hH, hclear, hzeros, hzeros', hformula⟩ :=
    exists_completedHecke_one_explicitFormula v r hr
  obtain ⟨habs, _, _, _, hformula⟩ :=
    hformula shiftedProfile contDiff_shiftedProfile hasCompactSupport_shiftedProfile
  refine ⟨L, H, hL, hdiffL, hEuler, hH, hclear, hzeros, hzeros', habs, ?_⟩
  let Φ := compactLogMellin shiftedProfile
  let W := fun (z : {z : ℂ // H z = 0}) ↦ (analyticOrderNatAt H z.val : ℂ) * Φ z.val
  change HasSum W (Φ 0 + Φ 1 - (gammaIntegral : ℂ))
  have hfinite : (∑' p : HeightOneSpectrum (𝓞 K) × ℕ,
      let l := Real.log (finitePlaceNorm p.1)
      let y : ℝ := (p.2 + 1 : ℕ) * l
      (l : ℂ) * (shiftedProfile y + exp (-y) * shiftedProfile (-y))) = 0 := by
    calc
      _ = ∑' _ : HeightOneSpectrum (𝓞 K) × ℕ, (0 : ℂ) := by
        refine tsum_congr fun p ↦ ?_
        obtain ⟨hy, hneg⟩ := shiftedProfile_prime_samples p.1 p.2
        simp only [hy, hneg, mul_zero, add_zero]
      _ = 0 := tsum_zero
  have hGamma : (∑ w : InfinitePlace K, trivialHeckeGammaContribution w shiftedProfile) =
      -(gammaIntegral : ℂ) := by
    rw [Finset.sum_eq_single v (fun w _ hw ↦ (hw (hunique w)).elim) (by simp),
      trivialHeckeGammaContribution_shiftedProfile hv]
  dsimp only at hformula hfinite
  rw [shiftedProfile_zero, mul_zero, hfinite, sub_zero, zero_add, hGamma] at hformula
  have hsum : (∑' z, W z) = Φ 0 + Φ 1 - (gammaIntegral : ℂ) := by
    dsimp only [W, Φ]
    linear_combination hformula
  have hW : Summable fun z ↦ ‖W z‖ := habs
  simpa only [hsum] using hW.of_norm.hasSum

end ShortPositiveLogBump
end Masullo
