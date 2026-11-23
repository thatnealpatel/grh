module

public import Props.IdeleClassStripTrace
import Theorems.ShortBumpFiniteTrace
public import Theorems.QSqrtNegFiveResidue
import Lemmas.RadialClassTest
import Lemmas.TrivialHeckeStripSum
import Lemmas.RawRadialClassMellin
import Theorems.ShortBumpExplicitFormula

/-! # The raw width-one strip identity fails over ℚ(√-5)

The normalized contour sum and the raw idelic sum describe the same
weighted divisor. The two sides of (12.5.1.3) scale its nonzero Gamma
term differently. This tests the stated Haar normalization, not GRH.
-/

open NumberField IsDedekindDomain Complex MeasureTheory
open scoped ContDiff Topology
open NumberField.Units.dirichletUnitTheorem (w₀)

namespace Masullo
open ShortPositiveLogBump
variable {K : Type*} [Field K] [NumberField K]
local notation "G" => IdeleClassGroup (𝓞 K) K
local notation "Ω" => HeckeCharacter (𝓞 K) K
local notation "F" => (fun x : ℝ ↦ (profile x : ℂ))
local notation "V" => (dedekindZeta_residue K : ℂ)
private theorem residue_eq_one_of_shortBump_agreement {L H : ℂ → ℂ} (hL : Meromorphic L)
    (he : ∀ s : ℂ, 1 < s.re → L s = completedHeckeEulerProduct (1 : Ω) (fun _ ↦ norm_one) s)
    (hH : Differentiable ℂ H) (hc : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s)
    (hz : ∀ z, H z = 0 → z ≠ 0 ∧ z ≠ 1 ∧ 0 ≤ z.re ∧ z.re ≤ 1)
    (v : InfinitePlace K) (hv : v.IsComplex) (hu : ∀ w : InfinitePlace K, w = v)
    (hφ : IsIdeleClassTest (classTest (K := K))) (htr : IdeleClassStripTrace K 1)
    (hs : HasSum (fun z : {z : ℂ // H z = 0} ↦ (analyticOrderNatAt H z.val : ℂ) * compactLogMellin F (z.val - 1 / 2))
      (compactLogMellin F (-1 / 2) + compactLogMellin F (1 / 2) - (gammaIntegral : ℂ))) :
    dedekindZeta_residue K = 1 := by
  classical
  let : Subsingleton (InfinitePlace K) := ⟨fun x y ↦ (hu x).trans (hu y).symm⟩
  have hF : Continuous F := Complex.continuous_ofReal.comp contDiff_profile.continuous
  have hm (s : ℂ) : ideleClassMellin (classTest (K := K)) (ideleClassNormPower s) =
      V * compactLogMellin F s := ideleClassMellin_radial_normPower hF s
  let W (χ : Ω) := ideleClassMellin classTest (χ * ideleClassNormPower (-1 / 2))
  have hw (χ : Ω) (hχ : ∃ c : ideleClassNormOne (K := K), χ (c : G) ≠ 1) : W χ = 0 := by
    obtain ⟨c, hc'⟩ := hχ
    exact ideleClassMellin_radial_eq_zero hF _ ⟨c, by
      simpa only [ContinuousMonoidHom.mul_apply, ideleClassNormPower_on_normOne, mul_one] using hc'⟩
  have hp (s : ℂ) : W (ideleClassNormPower s) = V * compactLogMellin F (s - 1 / 2) := by
    rw [← hm]
    unfold W
    congr 1
    ext c
    simp only [ContinuousMonoidHom.mul_apply, ideleClassNormPower_apply]
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleClassNorm_pos c).ne')]
    congr 1
    ring
  obtain ⟨A, hA, _, _, hraw⟩ := htr _ hφ classTest_normOne
  have hfin (w : HeightOneSpectrum (𝓞 K)) := (finiteTraceTerm_eq_zero w).2
  rw [Fintype.sum_subsingleton _ v, (hasArchimedeanTraceValue_iff hv _).mp (hA v), hm, hm] at hraw
  simp only [hfin, tsum_zero, sub_zero] at hraw
  have hs' := (hasSum_trivialHeckeStrip_iff hL he hH hc hz (by norm_num : (1 / 2 : ℝ) < 1) W hw).mp hraw
  have hscaled := hs.mul_left V
  have heq := hs'.unique (hscaled.congr_fun fun z ↦ by rw [hp]; ring)
  have hmul : (V - 1) * (gammaIntegral : ℂ) = 0 := by linear_combination heq
  exact_mod_cast sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (Complex.ofReal_ne_zero.mpr gammaIntegral_pos.ne'))


/-- For the raw quotient Haar pairing of (12.5.1.3), the short positive
bump contradicts the width-one identity over `ℚ(√-5)`. -/
public theorem not_ideleClassStripTrace_qSqrtNegFive : ¬ IdeleClassStripTrace QSqrtNegFive 1 := by
  classical
  intro htr
  let K := QSqrtNegFive
  let : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ := fun _ ↦ borel _
  let : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ := fun _ ↦ ⟨rfl⟩
  let : MeasurableSpace (IdeleClassGroup (𝓞 K) K) := borel _
  let : BorelSpace (IdeleClassGroup (𝓞 K) K) := ⟨rfl⟩
  let : MeasurableSpace (ideleClassNormOne (K := K)) := borel _
  let : BorelSpace (ideleClassNormOne (K := K)) := ⟨rfl⟩
  let : MeasurableSpace (ideleNormOne (K := K)) := borel _
  let : BorelSpace (ideleNormOne (K := K)) := ⟨rfl⟩
  let : MeasurableSpace (IdeleGroup (𝓞 K) K) := borel _
  let : BorelSpace (IdeleGroup (𝓞 K) K) := ⟨rfl⟩
  let : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ := fun _ ↦ borel _
  let : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ := fun _ ↦ ⟨rfl⟩
  let : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ :=
    fun _ ↦ borel _
  let : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ := fun _ ↦ ⟨rfl⟩
  have hr : Function.Surjective (ideleIdealClassNormOne (K := K)) :=
    fun g ↦ by
      obtain ⟨x, hx⟩ := ideleIdealClass_normOne_surjective g
      exact ⟨x, (ideleIdealClassNormOne_apply x).trans hx⟩
  choose r hr using hr
  let v : InfinitePlace K := w₀
  have hv := qSqrtNegFive_infinitePlace_isComplex v
  have hu (w : InfinitePlace K) : w = v := Subsingleton.elim _ _
  obtain ⟨L, H, hL, _, he, hH, hc, hz, _, _, hs⟩ :=
    exists_completedHecke_one_shortBump_hasSum v hv hu r hr
  have hshift (s : ℂ) : compactLogMellin shiftedProfile s = compactLogMellin F (s - 1 / 2) :=
    compactLogMellin_shiftedProfile s
  simp only [hshift, zero_sub, ← neg_div] at hs
  have hone : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hone] at hs
  have hcompact : HasCompactSupport F := HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc (fun _ hx ↦ Set.Ioo_subset_Icc_self (support_profile_subset
      fun h ↦ hx (by simp [h])))
  exact dedekindZeta_residue_qSqrtNegFive_ne_one (residue_eq_one_of_shortBump_agreement
    hL he hH hc (fun z h ↦ ⟨(hz z h).1, (hz z h).2.1, (hz z h).2.2.1, (hz z h).2.2.2.1⟩)
    v hv hu (isIdeleClassTest_radial (ofRealCLM.contDiff.comp contDiff_profile) hcompact) htr hs)

/-- Failure at width one rules out the proposed identity at all positive widths. -/
public theorem not_ideleClassTraceFormula_qSqrtNegFive : ¬ IdeleClassTraceFormula QSqrtNegFive :=
  fun h ↦ not_ideleClassStripTrace_qSqrtNegFive (h 1 zero_lt_one)

end Masullo
