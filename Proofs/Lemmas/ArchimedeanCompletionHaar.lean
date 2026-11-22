module

public import Theorems.RealMultiplicativeHaar
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Archimedean multiplicative measures in completion coordinates

Definition A.3.1.2(1)–(2), p. 556, uses `dx` and `2 dx dy`, respectively.
Definition A.3.2.2(1), p. 560, divides by the normalized local norm off zero.
For complex multiplication the real determinant is `‖a‖²`, exactly the
factor canceled by the inverse squared norm in the density.
-/

open Complex MeasureTheory NumberField InfinitePlace.Completion Set
open scoped ENNReal

namespace Masullo

/-- Complex multiplicative Tamagawa density extended by zero at the origin. -/
@[expose] public noncomputable def complexTamagawaDensity : Measure ℂ :=
  (volume : Measure ℂ).withDensity (fun z ↦ ENNReal.ofReal (2 / ‖z‖ ^ 2))

private theorem det_complex_mul (a : ℂ) :
    LinearMap.det (LinearMap.mulLeft ℝ a) = ‖a‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix basisOneI, Matrix.det_fin_two, ← normSq_eq_norm_sq]
  simp only [LinearMap.toMatrix_apply, coe_basisOneI, LinearMap.mulLeft_apply,
    coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_re, mul_im, I_re, I_im, mul_zero, zero_sub, add_zero,
    normSq_apply]
  ring

/-- The complex dilation Jacobian cancels the inverse squared norm. -/
public theorem complexTamagawaDensity_map_mul {a : ℂ} (ha : a ≠ 0) :
    complexTamagawaDensity.map (a * ·) = complexTamagawaDensity := by
  let d (z : ℂ) := ENNReal.ofReal (2 / ‖z‖ ^ 2)
  let c := ENNReal.ofReal ((‖a‖ ^ 2)⁻¹)
  have ha' : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hdm : Measurable (fun z ↦ d (a⁻¹ * z)) :=
    hd.comp (continuous_const_mul _).measurable
  have hm : Measurable (a * ·) := (continuous_const_mul a).measurable
  have hvol : (volume : Measure ℂ).map (a * ·) = c • volume := by
    have hdet : LinearMap.det (LinearMap.mulLeft ℝ a) ≠ 0 := by
      rw [det_complex_mul]; exact ha'.ne'
    have hlin : ((LinearMap.mulLeft ℝ a : ℂ →ₗ[ℝ] ℂ) : ℂ → ℂ) = (a * ·) :=
      funext (LinearMap.mulLeft_apply ℝ a)
    rw [← hlin, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, det_complex_mul,
      abs_of_nonneg (inv_nonneg.mpr ha'.le)]
  have hdil (z : ℂ) : c * d (a⁻¹ * z) = d z := by
    change ENNReal.ofReal ((‖a‖ ^ 2)⁻¹) * ENNReal.ofReal (2 / ‖a⁻¹ * z‖ ^ 2) = _
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha'.le)]
    change ENNReal.ofReal (((‖a‖ ^ 2)⁻¹) * (2 / ‖a⁻¹ * z‖ ^ 2)) =
      ENNReal.ofReal (2 / ‖z‖ ^ 2)
    congr 1
    by_cases hz : z = 0
    · simp [hz]
    · rw [norm_mul, norm_inv, mul_pow, inv_pow]
      field_simp [ha'.ne', (norm_pos_iff.mpr hz).ne']
  change ((volume : Measure ℂ).withDensity d).map (a * ·) = volume.withDensity d
  ext s hs
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs]
  calc
    (∫⁻ z in (a * ·) ⁻¹' s, d z) = ∫⁻ z in s, d (a⁻¹ * z) ∂(volume : Measure ℂ).map (a * ·) := by
      rw [setLIntegral_map hs hdm hm]
      simp only [inv_mul_cancel_left₀ ha]
    _ = ∫⁻ z in s, d z := by
      rw [hvol, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
        ← lintegral_const_mul c hdm]
      simp only [hdil]

private theorem map_comap_unit_density {F L : Type*} [Field F] [Field L]
    [MeasurableSpace Fˣ] [MeasurableSpace L] [MeasurableSingletonClass L] (e : F ≃+* L)
    (j : MeasurableEmbedding (fun u : Fˣ ↦ e (u : F)))
    (ν : Measure L) [NullSingletonClass ν] (d : L → ℝ≥0∞) :
    ((ν.withDensity d).comap (fun u : Fˣ ↦ e (u : F))).map (fun u : Fˣ ↦ e (u : F)) =
      ν.withDensity d := by
  have hrange : range (fun u : Fˣ ↦ e (u : F)) = ({0}ᶜ : Set L) := by
    ext y
    change (∃ u : Fˣ, e (u : F) = y) ↔ y ≠ 0
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ (map_ne_zero e).mpr u.ne_zero,
      fun hy ↦ ⟨Units.mk0 (e.symm y) ((map_ne_zero e.symm).mpr hy), e.apply_symm_apply y⟩⟩
  rw [j.map_comap, hrange, restrict_withDensity (measurableSet_singleton 0).compl,
    restrict_compl_singleton]

public theorem pullback_integral {U A : Type*} [MeasurableSpace U] [MeasurableSpace A]
    {j : U → A} (hj : MeasurableEmbedding j) {μ : Measure U} {ν : Measure A}
    {d : A → ℝ} (hd : Measurable d) (hd₀ : ∀ x, 0 ≤ d x)
    (hmap : μ.map j = ν.withDensity (fun x ↦ ENNReal.ofReal (d x)))
    {f g : A → ℂ} (hfg : ∀ x, g x = f x * (d x : ℂ))
    (hi : Integrable g ν) :
    Integrable (fun u ↦ f (j u)) μ ∧ (∫ u, f (j u) ∂μ) = ∫ x, g x ∂ν := by
  have hd' := hd.ennreal_ofReal
  have hfin : ∀ᵐ x ∂ν, ENNReal.ofReal (d x) < ∞ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have heq : (fun x ↦ (ENNReal.ofReal (d x)).toReal • f x) = g := by
    funext x
    rw [ENNReal.toReal_ofReal (hd₀ x), Complex.real_smul, mul_comm, hfg]
  constructor
  · apply hj.integrable_map_iff.mp
    rw [hmap, integrable_withDensity_iff_integrable_smul' hd' hfin, heq]
    exact hi
  · rw [← hj.integral_map, hmap, integral_withDensity_eq_integral_toReal_smul hd' hfin, heq]

public theorem positive_cpow_add_radial {r : ℝ} (hr : 0 < r) (τ : ℝ) (s : ℂ) :
    exp (((τ * Real.log r : ℝ) : ℂ) * I) * (r : ℂ) ^ s =
      (r : ℂ) ^ (s + (τ : ℂ) * I) := by
  conv_rhs => rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le]
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le, ← exp_add, ofReal_mul]
  congr 1
  ring

variable {K : Type*} [Field K] {v : InfinitePlace K}
variable [MeasurableSpace v.Completionˣ] [BorelSpace v.Completionˣ]

/-- Real completion-unit measure in the additive coordinate. -/
@[expose] public noncomputable def realCompletionHaar (hv : v.IsReal) : Measure v.Completionˣ :=
  realMultiplicativeDensity.comap (fun u : v.Completionˣ ↦ extensionEmbeddingOfIsReal hv u.val)

/-- Complex completion-unit measure in the additive coordinate. The density
is totalized by zero at the origin, which is not in the image of the units. -/
@[expose] public noncomputable def complexCompletionHaar (_hv : v.IsComplex) : Measure v.Completionˣ :=
  complexTamagawaDensity.comap
    (fun u : v.Completionˣ ↦ extensionEmbedding v u.val)

public theorem realCompletionEmbedding (hv : v.IsReal) :
    MeasurableEmbedding (fun u : v.Completionˣ ↦ extensionEmbeddingOfIsReal hv u.val) :=
  ((isometryEquivRealOfIsReal hv).toHomeomorph.isOpenEmbedding.comp
    Units.isOpenEmbedding_val).measurableEmbedding

public theorem complexCompletionEmbedding (hv : v.IsComplex) :
    MeasurableEmbedding (fun u : v.Completionˣ ↦ extensionEmbedding v u.val) :=
  ((isometryEquivComplexOfIsComplex hv).toHomeomorph.isOpenEmbedding.comp
    Units.isOpenEmbedding_val).measurableEmbedding

public theorem realCompletionHaar_map (hv : v.IsReal) :
    (realCompletionHaar hv).map (fun u : v.Completionˣ ↦ extensionEmbeddingOfIsReal hv u.val) =
      (volume : Measure ℝ).withDensity (fun y ↦ ENNReal.ofReal |y|⁻¹) := by
  unfold realCompletionHaar realMultiplicativeDensity
  rw [restrict_compl_singleton]
  exact map_comap_unit_density (ringEquivRealOfIsReal hv) (realCompletionEmbedding hv) volume _

public theorem complexCompletionHaar_map (hv : v.IsComplex) :
    (complexCompletionHaar hv).map (fun u : v.Completionˣ ↦ extensionEmbedding v u.val) =
      complexTamagawaDensity :=
  map_comap_unit_density (ringEquivComplexOfIsComplex hv) (complexCompletionEmbedding hv) volume _

public instance realCompletionHaar_isHaarMeasure (hv : v.IsReal) :
    (realCompletionHaar hv).IsHaarMeasure := by
  let e : v.Completion ≃ₜ* ℝ :=
    { (ringEquivRealOfIsReal hv).toMulEquiv with
      continuous_toFun := (isometryEquivRealOfIsReal hv).continuous
      continuous_invFun := (isometryEquivRealOfIsReal hv).symm.continuous }
  let j := Units.mapContinuousMulEquiv e
  have hj : realCompletionHaar hv = realMultiplicativeHaar.map j.symm := by
    apply (realCompletionEmbedding hv).map_injective
    have hm : Measurable (j.symm : ℝˣ → v.Completionˣ) := j.symm.continuous.measurable
    rw [realCompletionHaar_map hv, Measure.map_map (realCompletionEmbedding hv).measurable hm]
    have heq : (fun u : v.Completionˣ ↦ extensionEmbeddingOfIsReal hv u.val) ∘ j.symm =
        (Units.val : ℝˣ → ℝ) := by
      funext u
      exact congrArg Units.val (j.apply_symm_apply u)
    rw [heq, map_realMultiplicativeHaar_val, restrict_compl_singleton]
  rw [hj]
  exact j.symm.isHaarMeasure_map realMultiplicativeHaar

private theorem complexTamagawaDensity_ball :
    complexTamagawaDensity (Metric.closedBall (1 : ℂ) (1 / 2)) ∈ Ioo 0 ∞ := by
  let B := Metric.closedBall (1 : ℂ) (1 / 2)
  let d (z : ℂ) := ENNReal.ofReal (2 / ‖z‖ ^ 2)
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hn (z : ℂ) (hz : z ∈ B) : 1 / 2 ≤ ‖z‖ := by
    have h := (norm_sub_norm_le (1 : ℂ) z).trans (by
      simpa only [← dist_eq_norm, dist_comm (1 : ℂ) z] using Metric.mem_closedBall.mp hz)
    rw [norm_one] at h
    linarith
  change (volume.withDensity d) B ∈ Ioo 0 ∞
  rw [withDensity_apply _ hB]
  constructor
  · rw [setLIntegral_pos_iff hd, inter_eq_right.mpr (fun z hz ↦ ?_)]
    · exact Metric.isOpen_ball.measure_pos volume
        ⟨1, Metric.mem_ball_self (by norm_num)⟩ |>.trans_le
        (measure_mono Metric.ball_subset_closedBall)
    · exact (ENNReal.ofReal_pos.mpr (by have := hn z hz; positivity)).ne'
  · calc
      (∫⁻ z in B, d z) ≤ ∫⁻ _ in B, ENNReal.ofReal 8 :=
        setLIntegral_mono' hB (fun z hz ↦ ENNReal.ofReal_le_ofReal (by
          have h := hn z hz
          have hz' : 0 < ‖z‖ ^ 2 := by positivity
          apply (div_le_iff₀ hz').mpr
          nlinarith))
      _ < ∞ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (isCompact_closedBall (1 : ℂ) (1 / 2)).measure_lt_top

public instance complexCompletionHaar_isHaarMeasure (hv : v.IsComplex) :
    (complexCompletionHaar hv).IsHaarMeasure := by
  let j (u : v.Completionˣ) : ℂ := extensionEmbedding v u.val
  have hj := complexCompletionEmbedding hv
  let μ := complexCompletionHaar hv
  let : μ.IsMulLeftInvariant := by
    constructor
    intro a
    apply hj.map_injective
    have hm : Measurable (a * ·) := (continuous_const_mul a).measurable
    have hm' : Measurable (j a * ·) := (continuous_const_mul (j a)).measurable
    have ha : j a ≠ 0 := (map_ne_zero (extensionEmbedding v)).mpr a.ne_zero
    have hcomp : j ∘ (a * ·) = (j a * ·) ∘ j := funext fun u ↦
      (extensionEmbedding v).map_mul a.val u.val
    rw [Measure.map_map hj.measurable hm, hcomp, ← Measure.map_map hm' hj.measurable,
      complexCompletionHaar_map hv, complexTamagawaDensity_map_mul ha]
  let B := Metric.closedBall (1 : ℂ) (1 / 2)
  let S := j ⁻¹' B
  have hjOpen : Topology.IsOpenEmbedding j :=
    (isometryEquivComplexOfIsComplex hv).toHomeomorph.isOpenEmbedding.comp Units.isOpenEmbedding_val
  have hB : B ⊆ range j := by
    intro z hz
    have hz' : z ≠ 0 := by
      intro he
      subst z
      have h := Metric.mem_closedBall.mp hz
      norm_num [dist_eq_norm] at h
    let e := ringEquivComplexOfIsComplex hv
    exact ⟨Units.mk0 (e.symm z) ((map_ne_zero e.symm).mpr hz'), e.apply_symm_apply z⟩
  have hS : IsCompact S := hjOpen.isCompact_iff.mpr (by
    rw [image_preimage_eq_of_subset hB]; exact isCompact_closedBall _ _)
  have hSint : (interior S).Nonempty := by
    refine ⟨1, interior_maximal (t := j ⁻¹' Metric.ball 1 (1 / 2))
      (preimage_mono Metric.ball_subset_closedBall) (Metric.isOpen_ball.preimage hjOpen.continuous)
      ?_⟩
    change dist (extensionEmbedding v 1) 1 < _
    rw [map_one, dist_self]
    norm_num
  have hmass : μ S = complexTamagawaDensity B := by
    rw [← Measure.map_apply hj.measurable Metric.isClosed_closedBall.measurableSet,
      complexCompletionHaar_map hv]
  exact Measure.isHaarMeasure_of_isCompact_nonempty_interior μ S hS hSint
    (ne_of_gt (hmass ▸ complexTamagawaDensity_ball.1))
    (ne_of_lt (hmass ▸ complexTamagawaDensity_ball.2))

end Masullo
