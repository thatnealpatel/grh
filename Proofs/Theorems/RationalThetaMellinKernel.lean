module

public import Lemmas.RationalThetaMellin
public import Theorems.RationalAdeleClassThetaInversion
public import Theorems.RationalIdeleHaarComparison
import Theorems.RationalIdeleLogSection
import Theorems.RationalThetaNormFiber
import Theorems.IdeleZetaIntegral
import Theorems.RationalIdeleRestrictedProductHaar
import Theorems.RationalArchimedeanSchwartzMellin
import Lemmas.IdeleFullPeriodization
import all Lemmas.IdeleStageNormCoordinates
import Lemmas.FundamentalDomainQuotientMeasure
import Theorems.RationalIdeleFundamentalDomain
import Theorems.RationalAdeleUnramifiedPeriodization
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Fourier.Inversion

/-! # The rational unramified theta–Mellin kernel

This is the restriction of Masullo's (5.1.2.1), PDF pp. 224–225, to tests
`b ⊗ 𝟙_{∏ₚ ℤₚ}` with `b` a complex Schwartz function on `ℝ`. On this
space the nonzero orbit sum itself factors through the idelic norm. Thus one
radial convergence line detects its entire kernel, without an argument about
completeness of compact characters. No continuation or full LF-space claim
is made here.
-/

open MeasureTheory NumberField Set IsDedekindDomain HeightOneSpectrum InfinitePlace.Completion
open scoped Classical FourierTransform SchwartzMap Masullo

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "Cq" => IdeleClassGroup (𝓞 ℚ) ℚ

private theorem classTheta_eq_norm (b : 𝓢(ℝ, ℂ)) (c : Cq) :
    rationalAdeleClassTheta (rationalAdeleUnramified b) c = rationalTheta b (ideleClassNorm c) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  rw [rationalAdeleClassTheta_mk, ideleClassNorm_mk, ← (rationalTheta_eq_unramified_idele_sum b a).2]
  unfold rationalAdeleTheta
  congr 1
  funext q
  rw [rationalThetaIdeleTerm, rationalAdeleUnramified, Set.indicator_apply, rationalAdeleReal_apply]
  rfl

private theorem theta_exp_eq_zero_iff (b : 𝓢(ℝ, ℂ)) :
    (∀ x : ℝ, rationalTheta b (Real.exp x) = 0) ↔
      rationalAdeleClassTheta (rationalAdeleUnramified b) = 0 := by
  constructor
  · intro h
    funext c
    rw [classTheta_eq_norm, ← Real.exp_log (ideleClassNorm_pos c)]
    exact h _
  · intro h x
    have hx := congrFun h
      (QuotientGroup.mk (rationalIdeleLogSection (Multiplicative.ofAdd x)))
    rw [classTheta_eq_norm, ideleClassNorm_mk, ideleNorm_logSection, Pi.zero_apply] at hx
    exact hx

-- Fourier inversion applies pointwise to the continuous weighted log profile.
private theorem thetaMellin_line_eq_zero_iff (b : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 1 < σ) :
    (∀ y : ℝ, (∫ x : ℝ, rationalTheta b (Real.exp x) *
      Complex.exp (((σ : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ))) = 0) ↔
      (∀ x : ℝ, rationalTheta b (Real.exp x) = 0) := by
  let f (x : ℝ) := rationalTheta b (Real.exp x) * Complex.exp ((σ : ℂ) * (x : ℂ))
  have hcont : Continuous f :=
    ((rationalTheta_continuousOn b).comp_continuous Real.continuous_exp Real.exp_pos).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hi : Integrable f := (rationalTheta_mellin_hasSum b (z := (σ : ℂ)) (by simpa)).1
  constructor
  · intro h
    -- The Fourier convention uses the opposite sign and a factor of `2π`.
    have hfour : 𝓕 f = 0 := by
      funext w
      change 𝓕 f w = 0
      rw [Real.fourier_real_eq_integral_exp_smul]
      rw [← h (-2 * Real.pi * w)]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      dsimp only [f]
      rw [smul_eq_mul, mul_comm, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have hInv : 𝓕⁻ (𝓕 f) = f := hcont.fourierInv_fourier_eq hi (hfour.symm ▸ integrable_zero _ _ _)
    rw [hfour] at hInv
    have hzero : 𝓕⁻ (0 : ℝ → ℂ) = (0 : ℝ → ℂ) := by
      funext w
      rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
      simp
    rw [hzero] at hInv
    intro x
    exact (mul_eq_zero.mp (congrFun hInv.symm x)).resolve_right (Complex.exp_ne_zero _)
  · intro h y
    simp [h]

private theorem positive_cpow_eq_exp_log {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (r : ℂ) ^ z = Complex.exp (z * (Real.log r : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.ofReal_log hr.le, mul_comm]

private theorem integrable_schwartz_logRay (b : 𝓢(ℝ, ℂ)) {z : ℂ} (hz : 0 < z.re)
    (r : ℝ) (hr : ‖r‖ = 1) :
    Integrable (fun x : ℝ ↦ b (r * Real.exp x) * Complex.exp (z * (x : ℂ))) := by
  let f (x : ℝ) := b (r * Real.exp x) * Complex.exp (z * (x : ℂ))
  have hf : Continuous f := (b.continuous.comp (continuous_const.mul Real.continuous_exp)).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hbound (n : ℕ) (x : ℝ) :
      ‖f x‖ ≤ SchwartzMap.seminorm ℂ n 0 b * Real.exp ((z.re - (n : ℝ)) * x) := by
    have hnorm : ‖r * Real.exp x‖ = Real.exp x := by
      rw [norm_mul, hr, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h := b.le_seminorm ℂ n 0 (r * Real.exp x)
    rw [norm_iteratedFDeriv_zero, hnorm, ← Real.exp_nat_mul, mul_comm,
      ← le_div_iff₀ (Real.exp_pos _)] at h
    simp only [f, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ (SchwartzMap.seminorm ℂ n 0 b / Real.exp ((n : ℝ) * x)) * Real.exp (z.re * x) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by rw [sub_mul, Real.exp_sub]; ring
  -- At the negative end boundedness of `b` suffices; at the positive end use decay.
  obtain ⟨n, hn⟩ := exists_nat_gt z.re
  have hlo : IntegrableOn f (Iic 0) :=
    ((integrableOn_exp_mul_Iic hz 0).const_mul _).mono' hf.aestronglyMeasurable
      (.of_forall fun x ↦ by simpa using hbound 0 x)
  have hhi : IntegrableOn f (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (sub_neg.mpr hn) 0).const_mul _).mono' hf.aestronglyMeasurable
      (.of_forall (hbound n))
  simpa using hhi.union hlo

local notation "w" => Rat.infinitePlace
local notation "U" => Rat.infinitePlace.Completionˣ
local notation "vReal" => extensionEmbeddingOfIsReal Rat.isReal_infinitePlace

set_option linter.concreteInstances false in
private theorem integrable_unramified_archimedean [MeasurableSpace U] [BorelSpace U]
    (b : 𝓢(ℝ, ℂ)) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun u : U ↦ b (vReal u.val) * ((‖u.val‖ : ℝ) : ℂ) ^ z)
      (realCompletionHaar Rat.isReal_infinitePlace) := by
  let r (q : Bool) : ℝ := if q then 1 else -1
  let G (p : ℝ × Bool) := b (r p.2 * Real.exp p.1) * Complex.exp (z * (p.1 : ℂ))
  have hG : Measurable G := by
    have hm : Measurable r := Measurable.of_discrete
    exact (b.continuous.measurable.comp ((hm.comp measurable_snd).mul
      (Real.measurable_exp.comp measurable_fst))).mul
      (Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.continuous_ofReal.measurable.comp measurable_fst)))
  have hr (q : Bool) : ‖r q‖ = 1 := by cases q <;> simp [r]
  have hi (q : Bool) : Integrable (fun t ↦ G (t, q)) :=
    integrable_schwartz_logRay b hz (r q) (hr q)
  have hGi : Integrable G ((volume : Measure ℝ).prod (Measure.count : Measure Bool)) := by
    refine (integrable_prod_iff hG.aestronglyMeasurable).mpr ⟨.of_forall fun _ ↦
      Integrable.of_finite, ?_⟩
    refine ((hi false).norm.add (hi true).norm).congr (.of_forall fun _ ↦ ?_)
    simp [integral_count, add_comm]
  let L (u : U) := (Real.log ‖u.val‖, if 0 < vReal u.val then true else false)
  have hL : Measurable L :=
    (Real.measurable_log.comp (continuous_norm.comp Units.continuous_val).measurable).prodMk
      ((Measurable.ite measurableSet_Ioi measurable_const measurable_const).comp
        (realCompletionEmbedding Rat.isReal_infinitePlace).measurable)
  have hmap : Measure.map L (realCompletionHaar Rat.isReal_infinitePlace) = _ :=
    realCompletionHaar_map_logSign Rat.isReal_infinitePlace
  have heq (u : U) : b (vReal u.val) * ((‖u.val‖ : ℝ) : ℂ) ^ z = G (L u) := by
    have hnorm : |vReal u.val| = ‖u.val‖ :=
      (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
        (map_zero _) _
    have hpos : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
    rw [positive_cpow_eq_exp_log hpos]
    dsimp only [G, L]
    rw [Real.exp_log hpos, ← hnorm]
    by_cases hp : 0 < vReal u.val
    · simp [r, hp, abs_of_pos hp]
    · simp [r, hp, abs_of_nonpos (le_of_not_gt hp)]
  simp_rw [heq]
  exact (hmap.symm ▸ hGi).comp_measurable hL

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "F" v => HeightOneSpectrum.adicCompletion ℚ v
set_option quotPrecheck false in
local notation "Arch" => ((v : InfinitePlace ℚ) → v.Completionˣ)
local notation "μa" => (fun v : InfinitePlace ℚ ↦ archimedeanCompletionHaar v)
local notation "μf" => (fun v : V ↦ rationalLocalMultiplicativeHaar v)

set_option linter.concreteInstances false

section Mellin

variable [MeasurableSpace J] [BorelSpace J]

/-- The raw idelic Mellin density of the unramified tensor is absolutely
integrable in the convergence half-plane. No flatness at the real origin is needed. -/
public theorem integrable_rationalUnramifiedZetaIntegrand (b : 𝓢(ℝ, ℂ)) {z : ℂ} (hz : 1 < z.re) :
    Integrable (fun a : J ↦ rationalAdeleUnramified b (a : A) * ((ideleNorm a : ℝ) : ℂ) ^ z)
      rationalIdeleHaar := by
  -- Local completion measures use their canonical Borel structures.
  let : ∀ v : InfinitePlace ℚ, MeasurableSpace v.Completionˣ := fun _ ↦ borel _
  let : ∀ v : V, MeasurableSpace (F v)ˣ := fun _ ↦ borel _
  let : ∀ v : V, MeasurableSpace (v.adicCompletionIntegers ℚ)ˣ := fun _ ↦ borel _
  let : ∀ v : InfinitePlace ℚ, BorelSpace v.Completionˣ := fun _ ↦ ⟨rfl⟩
  let : ∀ v : V, BorelSpace (F v)ˣ := fun _ ↦ ⟨rfl⟩
  let : ∀ v : V, BorelSpace (v.adicCompletionIntegers ℚ)ˣ := fun _ ↦ ⟨rfl⟩
  let arch (x : Arch) := b (vReal (x w).val)
  let f : (v : V) → (F v)ˣ → ℂ := fun _ _ ↦ 0
  let χ : HeckeCharacter (𝓞 ℚ) ℚ := 1
  have hχ (c : Cq) : ‖χ c‖ = 1 := by simp [χ]
  have hu (p : V) : χ.IsUnramifiedAt p := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    simp [χ]
  have hA : Integrable (fun x : Arch ↦ arch x *
      (∏ v : InfinitePlace ℚ, χ (IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ v (x v))) *
      ((∏ v : InfinitePlace ℚ, ‖(x v : v.Completion)‖ ^ v.mult : ℝ) : ℂ) ^ z)
      (Measure.pi μa) := by
    have hh := rationalArchimedeanEval_measurePreserving.integrable_comp_of_integrable
      (integrable_unramified_archimedean b (zero_lt_one.trans hz))
    refine hh.congr (.of_forall fun x ↦ ?_)
    dsimp only [Function.comp_apply]
    have hN : (∏ v : InfinitePlace ℚ, ‖(x v : v.Completion)‖ ^ v.mult) = ‖(x w).val‖ := by
      rw [Fintype.prod_subsingleton _ w, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
    rw [hN]
    simp [arch, χ]
  -- The distinguished finite-place set is empty: every finite factor is integral.
  have hI := (ideleZetaIntegral_rightHalfPlane ℚ μa μf ∅ ∅ Subset.rfl
    (fun v _ ↦ rationalLocalMultiplicativeHaar_unitMass v) rationalIdeleHaar
    (fun S _ ↦ comap_rationalIdeleHaar_ideleFiniteStage S)
    χ (fun v _ ↦ hu v) hχ z hz arch f hA
    (by simp)).1
  have htest (a : J) : ideleZetaTest ℚ ∅ arch f a = rationalAdeleUnramified b (a : A) := by
    rw [ideleZetaTest, rationalAdeleUnramified, Set.indicator_apply, rationalAdeleReal_apply]
    have h (v : V) : ‖(a : A).2 v‖ ≤ 1 ↔ (a : A).2 v ∈ v.adicCompletionIntegers ℚ := by
      rw [Valued.toNormedField.norm_le_one_iff, mem_adicCompletionIntegers]
    simp only [Finset.notMem_empty, not_false_eq_true, true_implies, Finset.prod_empty, mul_one, h,
      ringEquivRealOfIsReal_apply]
    unfold arch ideleInfiniteCoordinates
    rfl
  refine hI.congr (.of_forall fun a ↦ ?_)
  simp [htest, χ, ideleNorm_apply]

/-- In the convergence half-plane the actual rational idele integral unfolds to
the log-norm Mellin integral of the nonzero rational orbit sum, with Lebesgue
measure and no additional scalar. -/
public theorem rationalUnramifiedZetaIntegral_eq_thetaMellin (b : 𝓢(ℝ, ℂ)) {z : ℂ}
    (hz : 1 < z.re) :
    (∫ a : J, rationalAdeleUnramified b (a : A) * ((ideleNorm a : ℝ) : ℂ) ^ z
      ∂rationalIdeleHaar) =
      ∫ x : ℝ, rationalTheta b (Real.exp x) * Complex.exp (z * (x : ℂ)) := by
  let : MeasurableSpace Cq := borel _
  let : BorelSpace Cq := ⟨rfl⟩
  let g (x : ℝ) := rationalTheta b (Real.exp x) * Complex.exp (z * (x : ℂ))
  let G (c : Cq) := g (Real.log (ideleClassNorm c))
  let f (a : J) := rationalAdeleUnramified b (a : A) * ((ideleNorm a : ℝ) : ℂ) ^ z
  have hcont : Continuous g :=
    ((rationalTheta_continuousOn b).comp_continuous Real.continuous_exp Real.exp_pos).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hG : Measurable G := hcont.measurable.comp
    (Real.measurable_log.comp continuous_ideleClassNorm.measurable)
  have hpos (a : J) : 0 < ideleNorm a :=
    ideleClassNorm_mk a ▸ ideleClassNorm_pos (QuotientGroup.mk a)
  have hf : Measurable f := by
    have hpow (a : J) : ((ideleNorm a : ℝ) : ℂ) ^ z =
        Complex.exp (z * (Real.log (ideleNorm a) : ℂ)) :=
      positive_cpow_eq_exp_log (hpos a) z
    dsimp only [f]
    simp_rw [hpow]
    exact ((continuous_rationalAdeleUnramified b).comp Units.continuous_val).measurable.mul
      (Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.continuous_ofReal.measurable.comp
          (Real.measurable_log.comp continuous_ideleNorm.measurable))))
  let Γ := (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ).op
  have : Countable ℚˣ := (Units.val_injective (α := ℚ)).countable
  have : Countable Γ := (ideleFullPrincipalIndex (K := ℚ)).surjective.countable
  let q : J →* Cq := QuotientGroup.mk' _
  have hperiod (a : J) : G (q a) = ∑' s : Γ, f (s • a) := by
    rw [← ideleFullPrincipalIndex_tsum f a]
    have hnorm (r : ℚˣ) : ideleNorm (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r * a) = ideleNorm a := by
      rw [map_mul, ideleNorm_apply (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r)]
      change ‖algebraMap ℚ A (r : ℚ)‖ * ideleNorm a = ideleNorm a
      rw [AdeleRing.norm_algebraMap_eq_one_of_ne_zero r.ne_zero, one_mul]
    simp only [f, hnorm, tsum_mul_right]
    change G (q a) = rationalAdeleTheta (rationalAdeleUnramified b) a * _
    rw [← rationalAdeleClassTheta_mk, classTheta_eq_norm, ideleClassNorm_mk]
    dsimp only [G, g, q]
    rw [QuotientGroup.mk'_apply, ideleClassNorm_mk, Real.exp_log (hpos a),
      positive_cpow_eq_exp_log (hpos a)]
  have h := (integral_periodization q (rationalIdeleUnitWindow_isFundamentalDomain rationalIdeleHaar)
    QuotientGroup.continuous_mk.measurable hf (integrable_rationalUnramifiedZetaIntegrand b hz) hG hperiod).2
  change (∫ c, G c ∂(rationalIdeleHaar.restrict rationalIdeleUnitWindow).map QuotientGroup.mk) = _ at h
  rw [map_restrict_rationalIdeleHaar] at h
  exact h.symm.trans (integral_rationalIdeleClass_logNorm (rationalTheta_mellin_hasSum b hz).1)

/-- The unramified rational case of (5.1.2.1): the raw idelic Mellin integral
vanishes all along any one line `σ + iℝ`, `σ > 1`, if and only if the nonzero
adelic theta sum vanishes on every rational idele class. -/
public theorem rationalUnramifiedMellinLine_eq_zero_iff_classTheta_eq_zero
    (b : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 1 < σ) :
    (∀ y : ℝ, (∫ a : J, rationalAdeleUnramified b (a : A) *
      ((ideleNorm a : ℝ) : ℂ) ^ ((σ : ℂ) + (y : ℂ) * Complex.I) ∂rationalIdeleHaar) = 0) ↔
      rationalAdeleClassTheta (rationalAdeleUnramified b) = 0 := by
  have hunfold (y : ℝ) := rationalUnramifiedZetaIntegral_eq_thetaMellin b
    (z := (σ : ℂ) + (y : ℂ) * Complex.I) (by simpa using hσ)
  simp_rw [hunfold]
  exact (thetaMellin_line_eq_zero_iff b hσ).trans (theta_exp_eq_zero_iff b)

/-- Equality of the two vanishing kernels on the same unramified test space,
using the entire convergence half-plane for the Mellin operator. -/
public theorem rationalUnramifiedMellin_eq_zero_iff_classTheta_eq_zero (b : 𝓢(ℝ, ℂ)) :
    (∀ z : ℂ, 1 < z.re → (∫ a : J, rationalAdeleUnramified b (a : A) *
      ((ideleNorm a : ℝ) : ℂ) ^ z ∂rationalIdeleHaar) = 0) ↔
      rationalAdeleClassTheta (rationalAdeleUnramified b) = 0 := by
  constructor
  · intro h
    refine (rationalUnramifiedMellinLine_eq_zero_iff_classTheta_eq_zero b
      (σ := 2) (by norm_num)).mp fun y ↦ h _ ?_
    norm_num
  · intro h z hz
    rw [rationalUnramifiedZetaIntegral_eq_thetaMellin b hz]
    simp [(theta_exp_eq_zero_iff b).mpr h]

end Mellin

end Masullo
