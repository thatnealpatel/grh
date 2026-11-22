module

public import Theorems.AdeleBoxThetaOperator
public import Theorems.AdeleBoxThetaDecay
public import Lemmas.FinitePlaceSupport
import Lemmas.FiniteAdeleDenominators
import Theorems.AdeleRestrictedProductHaar
import Theorems.IdeleClassRapidDecay

/-! # Two-ended theta decay on idele classes

The pointwise estimate of Masullo §1.1.4, fourth bullet (p. 12), and
(2.2.3.6) (p. 83), on the actual adelic box span and idele class group.
This controls the function, not its class derivatives or Schwartz–Bruhat stage.
-/

open IsDedekindDomain MeasureTheory NumberField NumberField.InfinitePlace InfinitePlace.Completion Set
open scoped Classical Masullo.AdeleStage SchwartzMap

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "J" => IdeleGroup (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "E∞" => mixedEmbedding.euclidean.mixedSpace K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "L[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "j[" v "]" => algebraMap (𝓞 K) L[v]
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

-- These two local estimates mirror the private support and radius bounds in
-- `AdeleBoxThetaOperator`; that module stays unchanged as prior receipt evidence.
private theorem box_clearer (a : F) (g : Fˣ) :
    ∃ c : J, ∀ h : J, h.val.2 ∈ finiteAdeleBox a g → ∀ v : V, ‖(c * h).val.2 v‖ ≤ 1 := by
  obtain ⟨r, hr, hra⟩ := exists_finiteAdele_clearDenominator a
  obtain ⟨s, hs, hsg⟩ := exists_finiteAdele_clearDenominator (g : F)
  -- Clear both the translate and the scale using the product of their denominators.
  let c := d (Units.mk0 (algebraMap (𝓞 K) K (r * s))
    (by simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne (mul_ne_zero hr hs)))
  refine ⟨c, fun h hh v ↦ ?_⟩
  have hav : j[v] r * a v ∈ O[v] := hra v
  have hgv : j[v] s * (g : F) v ∈ O[v] := hsg v
  have hint (t : 𝓞 K) : j[v] t ∈ O[v] := by
    change Valued.v (j[v] t) ≤ 1
    change Valued.v ((algebraMap (𝓞 K) K t : K) : L[v]) ≤ 1
    rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
    exact v.intValuation_le_one _
  rcases hh v with ⟨_, ⟨t, ht, rfl⟩, heq⟩
  change a v + (g : F) v * t = h.val.2 v at heq
  apply Valued.toNormedField.norm_le_one_iff.mpr
  change (j[v] (r * s) * h.val.2 v) ∈ O[v]
  rw [← heq, map_mul, mul_add]
  have ha' : j[v] r * j[v] s * a v = j[v] s * (j[v] r * a v) := by ac_rfl
  have hg' : j[v] r * j[v] s * ((g : F) v * t) = (j[v] r * (j[v] s * (g : F) v)) * t := by ac_rfl
  rw [ha', hg']
  exact (O[v]).toSubring.add_mem ((O[v]).toSubring.mul_mem (hint s) hav)
    ((O[v]).toSubring.mul_mem ((O[v]).toSubring.mul_mem (hint r) hgv) ht)

private theorem norm_le_archEuclidean (x : InfiniteAdeleRing K) (v : InfinitePlace K) :
    ‖x v‖ ≤ ‖(archimedeanEuclideanToAdele K).symm x‖ := by
  let y := (archimedeanEuclideanToAdele K).symm x
  have heq : mixedEmbedding.euclidean.toMixed K y = InfiniteAdeleRing.ringEquiv_mixedSpace K x :=
    archimedeanEuclideanToAdele_symm_mixed K x
  by_cases hv : v.IsReal
  · let w : {v : InfinitePlace K // v.IsReal} := ⟨v, hv⟩
    have hw : y.fst w = extensionEmbeddingOfIsReal hv (x v) :=
      congrArg (fun z : mixedEmbedding.mixedSpace K ↦ z.1 w) heq
    rw [← (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (x v), ← hw]
    exact (PiLp.norm_apply_le y.fst w).trans (WithLp.norm_fst_le _ y)
  · let w : {v : InfinitePlace K // v.IsComplex} := ⟨v, not_isReal_iff_isComplex.mp hv⟩
    have hw : y.snd w = extensionEmbedding v (x v) :=
      congrArg (fun z : mixedEmbedding.mixedSpace K ↦ z.2 w) heq
    rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v), ← hw]
    exact (PiLp.norm_apply_le y.snd w).trans (WithLp.norm_snd_le _ y)

private theorem theta_largeNorm_box (φ : 𝓢(E∞, ℂ)) (a : F) (g : Fˣ) (N : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : C, 1 ≤ ideleClassNorm x →
      ‖adeleBoxThetaLinear ⟨adeleBoxTensor φ a g, adeleBoxTensor_mem_adeleBoxSpan φ a g⟩ x‖ ≤
        R * ideleClassNorm x ^ (-(N : ℤ)) := by
  obtain ⟨c, hc⟩ := box_clearer a g
  let t (h : J) := adeleBoxTensor φ a g h.val
  have hsupp (h : J) (ht : t h ≠ 0) : ∀ v : V, ‖(c * h).val.2 v‖ ≤ 1 := by
    apply hc h
    by_contra hn
    exact ht (by simp [t, adeleBoxTensor, indicator_of_notMem hn])
  have hweight (p : ℕ) : ∃ D : ℝ, 0 < D ∧ ∀ (h : J) (v : InfinitePlace K),
      ‖t h‖ * ‖h.val.1 v‖ ^ p ≤ D := by
    obtain ⟨D, hD, hd⟩ := φ.decay p 0
    refine ⟨D, hD, fun h v ↦ ?_⟩
    by_cases hh : h.val.2 ∈ finiteAdeleBox a g
    · simp only [t, adeleBoxTensor, indicator_of_mem hh, mul_one]
      calc
        _ ≤ ‖φ ((archimedeanEuclideanToAdele K).symm h.val.1)‖ *
            ‖(archimedeanEuclideanToAdele K).symm h.val.1‖ ^ p := by
          gcongr
          exact norm_le_archEuclidean _ _
        _ ≤ D := by simpa [mul_comm] using hd ((archimedeanEuclideanToAdele K).symm h.val.1)
    · simpa [t, adeleBoxTensor, indicator_of_notMem hh] using hD.le
  obtain ⟨R, hR, hb⟩ := idele_periodization_rapidDecay_of_support t c hsupp hweight N
  refine ⟨R, hR, fun x hx ↦ ?_⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [ideleClassNorm_mk] at hx
  rw [adeleBoxThetaLinear_apply, ideleClassNorm_mk]
  obtain ⟨hs, hh⟩ := hb h hx
  exact (norm_tsum_le_tsum_norm hs).trans hh

/-- At every idele class of norm at least one, the actual theta of a box-span
test decays uniformly faster than any inverse power of the class norm. -/
public theorem adeleBoxThetaLinear_largeNorm_decay (f : adeleBoxSpan K) (N : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : C, 1 ≤ ideleClassNorm x →
      ‖adeleBoxThetaLinear f x‖ ≤ R * ideleClassNorm x ^ (-(N : ℤ)) := by
  obtain ⟨t, ht⟩ := f
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨φ, a, g, rfl⟩ := ht
    exact theta_largeNorm_box φ a g N
  | zero =>
    refine ⟨1, zero_lt_one, fun x hx ↦ ?_⟩
    change ‖adeleBoxThetaLinear (0 : adeleBoxSpan K) x‖ ≤ _
    simpa using zpow_nonneg (zero_le_one.trans hx) (-(N : ℤ))
  | add t s ht hs iht ihs =>
    obtain ⟨Rt, hRt, hbt⟩ := iht
    obtain ⟨Rs, hRs, hbs⟩ := ihs
    refine ⟨Rt + Rs, add_pos hRt hRs, fun x hx ↦ ?_⟩
    change ‖adeleBoxThetaLinear (⟨t, ht⟩ + ⟨s, hs⟩) x‖ ≤ _
    rw [map_add, ContinuousMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hbt x hx) (hbs x hx))
  | smul c t ht iht =>
    obtain ⟨R, hR, hb⟩ := iht
    refine ⟨‖c‖ * R + 1, by linarith [mul_nonneg (norm_nonneg c) hR.le], fun x hx ↦ ?_⟩
    change ‖adeleBoxThetaLinear (c • ⟨t, ht⟩) x‖ ≤ _
    rw [map_smul, ContinuousMap.smul_apply, norm_smul, add_mul, mul_assoc ‖c‖ R]
    exact (mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg c)).trans
      (le_add_of_nonneg_right (mul_nonneg zero_le_one (zpow_nonneg (zero_le_one.trans hx) _)))

private theorem exists_calibratedThetaHaar (K : Type*) [Field K] [NumberField K] :
    ∃ μ : Measure (AdeleRing (𝓞 K) K), μ.IsAddHaarMeasure ∧
      ∃ E : Finset (HeightOneSpectrum (𝓞 K)), ∀ S, E ⊆ S →
        μ.comap (adeleFiniteStageEmbedding K S) = adeleFiniteStageHaar K S := by
  obtain ⟨E, hE⟩ := exists_finiteCompletionIntegerMass_exceptions K
  obtain ⟨μ, hμ, _, hstage, _⟩ := exists_adeleRestrictedProductHaar K E
    (fun v hv ↦ not_not.mp (fun hn ↦ hv ((hE v).mpr hn)))
  exact ⟨μ, hμ, E, (hstage μ).mp rfl⟩

/-- The additive adelic Haar measure calibrated to the trace Fourier products. -/
public noncomputable def adeleBoxThetaHaar (K : Type*) [Field K] [NumberField K] :
    Measure (AdeleRing (𝓞 K) K) := (exists_calibratedThetaHaar K).choose

public instance instIsAddHaarMeasure_adeleBoxThetaHaar : (adeleBoxThetaHaar K).IsAddHaarMeasure :=
  (exists_calibratedThetaHaar K).choose_spec.1

/-- The zero frequency of the adelic trace Fourier integral is the integral of the test. -/
public theorem adeleFourier_zero_eq_integral (μ : Measure A) (f : A → ℂ) :
    adeleFourier μ f 0 = ∫ x, f x ∂μ := by
  simp [adeleFourier]

private theorem theta_smallNorm (f : adeleBoxSpan K) (N : ℕ) (h₀ : (f : A → ℂ) 0 = 0)
    (hF₀ : adeleFourier (adeleBoxThetaHaar K) (f : A → ℂ) 0 = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : C, ideleClassNorm x ≤ 1 →
      ‖adeleBoxThetaLinear f x‖ ≤ R * ideleClassNorm x ^ N := by
  obtain ⟨E, hE⟩ := (exists_calibratedThetaHaar K).choose_spec.2
  obtain ⟨R, hR, hb⟩ := adeleBoxSpan_theta_smallNorm_decay (adeleBoxThetaHaar K) E hE f.property N
  refine ⟨R, hR, fun x hx ↦ ?_⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [ideleClassNorm_mk] at hx
  rw [adeleBoxThetaLinear_apply, ideleClassNorm_mk]
  have hsample (b : Kˣ) : (d b * h).val = (h : A) * algebraMap K A (b : K) := by
    change algebraMap K A (b : K) * (h : A) = _
    exact mul_comm _ _
  simpa only [hsample, h₀, hF₀, smul_zero, sub_zero, add_zero] using hb h hx

/-- With both zero modes absent, the actual theta function of an adelic box-span
 test decays exponentially in the absolute log norm, with one constant valid
 on all idele classes, including at norm one. -/
public theorem adeleBoxThetaLinear_exp_decay (f : adeleBoxSpan K) (N : ℕ)
    (h₀ : (f : A → ℂ) 0 = 0) (hF₀ : adeleFourier (adeleBoxThetaHaar K) (f : A → ℂ) 0 = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : C,
      ‖adeleBoxThetaLinear f x‖ ≤ R * Real.exp (-(N : ℝ) * |Real.log (ideleClassNorm x)|) := by
  obtain ⟨L, hL, hl⟩ := adeleBoxThetaLinear_largeNorm_decay f N
  obtain ⟨S, _, hs⟩ := theta_smallNorm f N h₀ hF₀
  refine ⟨max L S, hL.trans_le (le_max_left ..), fun x ↦ ?_⟩
  have hp := ideleClassNorm_pos x
  have hpow : Real.exp ((N : ℝ) * Real.log (ideleClassNorm x)) = ideleClassNorm x ^ N := by
    rw [Real.exp_nat_mul, Real.exp_log hp]
  by_cases hx : 1 ≤ ideleClassNorm x
  · rw [abs_of_nonneg (Real.log_nonneg hx), neg_mul, Real.exp_neg, hpow, ← zpow_natCast, ← zpow_neg]
    exact (hl x hx).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (zpow_nonneg hp.le _))
  · have hx' := le_of_not_ge hx
    rw [abs_of_nonpos (Real.log_nonpos hp.le hx'), neg_mul_neg, hpow]
    exact (hs x hx').trans (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg hp.le _))

end Masullo
