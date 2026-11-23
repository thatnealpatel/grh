module

public import Props.IdeleClassStripTrace

import Lemmas.FinitePlaceSupport
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Archimedean single-place restrictions of idele-class tests

The real and complex terms of Masullo's Theorem 12.5.1.1, (12.5.1.1),
pp. 519–520, use the test restricted along the insertion of completion units.
The restriction has compact support and is smooth in its additive coordinate
when extended by zero at the origin.
-/

open Filter NumberField InfinitePlace InfinitePlace.Completion Set Topology
open scoped Classical ContDiff

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "j(" v ")" => IdeleClassGroup.ofCompletion (𝓞 K) K v

private theorem continuous_archimedeanIdeleInsertion (v : InfinitePlace K) :
    Continuous (IdeleGroup.ofCompletion (𝓞 K) K v) := by
  have h : Continuous (InfiniteAdeleRing.ofCompletion v) := by
    change Continuous (Pi.mulSingle (M := fun w : InfinitePlace K ↦ w.Completion) v)
    exact continuous_mulSingle v
  exact Units.continuous_map (h.prodMk continuous_const)

/-- On a single Archimedean place the idelic norm is its normalized local norm. -/
public theorem ideleClassNorm_ofCompletion (v : InfinitePlace K) (u : v.Completionˣ) :
    ideleClassNorm (j(v) u) = ‖(u : v.Completion)‖ ^ v.mult := by
  rw [IdeleClassGroup.ofCompletion, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    ideleClassNorm_mk, ideleNorm_apply,
    AdeleRing.norm_apply_of_isUnit (IdeleGroup.ofCompletion (𝓞 K) K v u).isUnit]
  change (∏ w : InfinitePlace K, ‖Pi.mulSingle v (u : v.Completion) w‖ ^ w.mult) *
    (∏ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(1 : w.adicCompletion K)‖) = _
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single v]
  · rw [Pi.mulSingle_eq_same]
  · intro w _ hw
    rw [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow]
  · simp

/-- The Archimedean summand's test has compact support on the actual completion units. -/
public theorem hasCompactSupport_archimedeanRestriction (φ : C → ℂ)
    (hφ : IsIdeleClassTest φ) (v : InfinitePlace K) :
    HasCompactSupport (fun u ↦ φ (j(v) u)) := by
  obtain ⟨T, hT, hband⟩ := exists_ideleClassNorm_band_of_hasCompactSupport φ hφ.1
  have hT₀ : 0 < T := zero_lt_one.trans hT
  let B : Set v.Completion := {z | ‖z‖ ∈ Icc T⁻¹ T}
  have hB : IsCompact B := by
    let e := extensionEmbedding v
    have he := isometry_extensionEmbedding v
    have hnorm (z : v.Completion) : ‖e z‖ = ‖z‖ := he.norm_map_of_map_zero (map_zero _) z
    have hclosed : IsClosed {z : ℂ | ‖z‖ ∈ Icc T⁻¹ T} := isClosed_Icc.preimage continuous_norm
    have hcompact : IsCompact {z : ℂ | ‖z‖ ∈ Icc T⁻¹ T} :=
      (isCompact_closedBall 0 T).of_isClosed_subset hclosed fun z hz ↦
        Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hz.2)
    convert he.isClosedEmbedding.isCompact_preimage hcompact using 1
    ext z
    change ‖z‖ ∈ Icc T⁻¹ T ↔ ‖e z‖ ∈ Icc T⁻¹ T
    rw [hnorm]
  have hrange : B ⊆ range (Units.val : v.Completionˣ → v.Completion) := by
    intro z hz
    have hne : z ≠ 0 := norm_pos_iff.mp ((inv_pos.mpr hT₀).trans_le hz.1)
    exact ⟨Units.mk0 z hne, rfl⟩
  have hann : IsCompact ((Units.val : v.Completionˣ → v.Completion) ⁻¹' B) := by
    apply Units.isEmbedding_val₀.isCompact_iff.mpr
    rwa [image_preimage_eq_of_subset hrange]
  refine HasCompactSupport.of_support_subset_isCompact hann ?_
  intro u hu
  have hpow := hband (j(v) u) (subset_tsupport φ hu)
  rw [ideleClassNorm_ofCompletion] at hpow
  change T⁻¹ ≤ ‖(u : v.Completion)‖ ∧ ‖(u : v.Completion)‖ ≤ T
  have hm : 1 ≤ v.mult := InfinitePlace.mult_pos
  constructor
  · by_contra! h
    have hn : ‖(u : v.Completion)‖ ≤ 1 :=
      h.le.trans (inv_le_one_of_one_le₀ hT.le)
    have hp := pow_le_pow_of_le_one (norm_nonneg (u : v.Completion)) hn hm
    exact (not_le_of_gt (h.trans hpow.1)) (by simpa only [pow_one] using hp)
  · by_contra! h
    have hn : 1 ≤ ‖(u : v.Completion)‖ := hT.le.trans h.le
    have hp := pow_le_pow_right₀ hn hm
    exact (not_le_of_gt (hpow.2.trans h)) (by simpa only [pow_one] using hp)

/-- Norm-one vanishing of the idele-class test restricts to the local norm-one units. -/
public theorem archimedeanRestriction_eq_zero_of_norm_eq_one (φ : C → ℂ)
    (hunit : ∀ x : ideleClassNormOne (K := K), φ x = 0)
    (v : InfinitePlace K) (u : v.Completionˣ) (hu : ‖(u : v.Completion)‖ = 1) :
    φ (j(v) u) = 0 := by
  apply hunit ⟨j(v) u, (mem_ideleClassNormOne _).2 ?_⟩
  rw [ideleClassNorm_ofCompletion, hu, one_pow]

section Coordinates

variable {F : Type*} [NormedField F]

/-- The completion-unit restriction in an additive coordinate, extended by zero at the origin. -/
@[expose] public noncomputable def archimedeanRestrictionInCoordinates {v : InfinitePlace K}
    (e : v.Completion ≃+* F) (φ : C → ℂ) (z : F) : ℂ :=
  if hz : e.symm z = 0 then 0 else φ (j(v) (Units.mk0 (e.symm z) hz))

/-- In a coordinate coming from a completion unit, the zero extension is
exactly the idele-class restriction that occurs in `HasArchimedeanTraceValue`. -/
public theorem archimedeanRestrictionInCoordinates_apply_unit {v : InfinitePlace K}
    (e : v.Completion ≃+* F) (φ : C → ℂ) (u : v.Completionˣ) :
    archimedeanRestrictionInCoordinates e φ (e (u : v.Completion)) = φ (j(v) u) := by
  have h : e.symm (e (u : v.Completion)) ≠ 0 := by
    rw [RingEquiv.symm_apply_apply]
    exact u.ne_zero
  rw [archimedeanRestrictionInCoordinates, dite_eq_right h]
  congr 2
  exact Units.ext (e.symm_apply_apply _)

private theorem support_archimedeanRestrictionInCoordinates_subset {v : InfinitePlace K}
    (e : v.Completion ≃+* F) (φ : C → ℂ) :
    Function.support (archimedeanRestrictionInCoordinates e φ) ⊆
      (fun u : v.Completionˣ ↦ e (u : v.Completion)) '' tsupport (fun u ↦ φ (j(v) u)) := by
  intro z hz
  change archimedeanRestrictionInCoordinates e φ z ≠ 0 at hz
  rw [archimedeanRestrictionInCoordinates] at hz
  split_ifs at hz with h
  · exact (hz rfl).elim
  · exact ⟨Units.mk0 (e.symm z) h, subset_tsupport _ hz, e.apply_symm_apply z⟩

/-- A continuous additive coordinate gives compact support also for the zero extension. -/
public theorem hasCompactSupport_archimedeanRestrictionInCoordinates {v : InfinitePlace K}
    (e : v.Completion ≃+* F) (he : Continuous e) (φ : C → ℂ) (hφ : IsIdeleClassTest φ) :
    HasCompactSupport (archimedeanRestrictionInCoordinates e φ) :=
  HasCompactSupport.of_support_subset_isCompact
    ((hasCompactSupport_archimedeanRestriction φ hφ v).image (he.comp Units.continuous_val))
    (support_archimedeanRestrictionInCoordinates_subset e φ)

private theorem contDiff_archimedeanRestrictionInCoordinates [NormedAlgebra ℝ F]
    {v : InfinitePlace K} (e : v.Completion ≃+* F) (he : Continuous e)
    (he' : Continuous e.symm) (φ : C → ℂ) (hφ : IsIdeleClassTest φ)
    (hcoord : ∀ a : v.Completion, ContDiff ℝ ∞ (fun z : F ↦
      InfiniteAdeleRing.ringEquiv_mixedSpace K (InfiniteAdeleRing.ofCompletion v (a * e.symm z)))) :
    ContDiff ℝ ∞ (archimedeanRestrictionInCoordinates e φ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    let A := (fun u : v.Completionˣ ↦ e (u : v.Completion)) '' tsupport (fun u ↦ φ (j(v) u))
    have hA : IsCompact A :=
      (hasCompactSupport_archimedeanRestriction φ hφ v).image (he.comp Units.continuous_val)
    have hzero : (0 : F) ∉ A := by
      rintro ⟨u, _, hu⟩
      exact u.ne_zero ((map_eq_zero e).mp hu)
    have hout := hA.isClosed.isOpen_compl.mem_nhds hzero
    apply (contDiff_const (c := (0 : ℂ))).contDiffAt.congr_of_eventuallyEq
    filter_upwards [hout] with x hx
    exact not_not.mp fun hx₀ ↦ hx (support_archimedeanRestrictionInCoordinates_subset e φ hx₀)
  · let i := IdeleGroup.ofCompletion (𝓞 K) K v
    let lift (x : F) : v.Completionˣ :=
      if hx : e.symm x = 0 then 1 else Units.mk0 (e.symm x) hx
    have hne : ∀ᶠ x in 𝓝 z, e.symm x ≠ 0 := by
      filter_upwards [isOpen_ne.mem_nhds hz] with x hx
      exact fun h ↦ hx ((map_eq_zero e.symm).1 h)
    have hval : (fun x ↦ (lift x : v.Completion)) =ᶠ[𝓝 z] e.symm :=
      hne.mono (fun x hx ↦ by simp only [lift, dite_eq_right hx, Units.val_mk0])
    have hlift : ContinuousAt lift z := by
      apply Units.isEmbedding_val₀.isInducing.continuousAt_iff.mpr
      exact he'.continuousAt.congr hval.symm
    let u := lift z
    obtain ⟨f, hf, hloc⟩ := hφ.2 (j(v) u)
    have ht : Tendsto (fun x ↦ i (u⁻¹ * lift x)) (𝓝 z) (𝓝 1) := by
      have hc : ContinuousAt (fun x ↦ i (u⁻¹ * lift x)) z :=
        (continuous_archimedeanIdeleInsertion v).continuousAt.comp (continuousAt_const.mul hlift)
      simpa only [show lift z = u from rfl, inv_mul_cancel, map_one] using hc.tendsto
    refine (hf.comp (hcoord (↑u⁻¹ : v.Completion))).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [ht.eventually hloc, hne, hval] with x hx hx₀ hvalx
    have hmul : j(v) u * QuotientGroup.mk (i (u⁻¹ * lift x)) = j(v) (lift x) := by
      change j(v) u * j(v) (u⁻¹ * lift x) = j(v) (lift x)
      rw [← map_mul, mul_inv_cancel_left]
    have harch : (i (u⁻¹ * lift x)).val.1 =
        InfiniteAdeleRing.ofCompletion v ((↑u⁻¹ : v.Completion) * e.symm x) := by
      change InfiniteAdeleRing.ofCompletion v ((↑u⁻¹ : v.Completion) * ↑(lift x)) = _
      rw [hvalx]
    rw [hmul, harch] at hx
    simpa only [archimedeanRestrictionInCoordinates, lift, dite_eq_right hx₀,
      Function.comp_apply] using hx

/-- At a real place the restriction of the idele-class test is smooth in its real coordinate. -/
public theorem contDiff_archimedeanRestriction_real {v : InfinitePlace K} (hv : v.IsReal)
    (φ : C → ℂ) (hφ : IsIdeleClassTest φ) :
    ContDiff ℝ ∞ (archimedeanRestrictionInCoordinates (ringEquivRealOfIsReal hv) φ) := by
  let e := ringEquivRealOfIsReal hv
  apply contDiff_archimedeanRestrictionInCoordinates e (isometryEquivRealOfIsReal hv).continuous
    (isometryEquivRealOfIsReal hv).symm.continuous φ hφ
  intro a
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply ContDiff.prodMk <;> apply contDiff_pi'
  · rintro ⟨w, hw⟩
    by_cases h : w = v
    · subst w
      change ContDiff ℝ ∞ (fun x : ℝ ↦ e (Pi.mulSingle v (a * e.symm x) v))
      simp only [Pi.mulSingle_eq_same, map_mul, RingEquiv.apply_symm_apply]
      exact (contDiff_const (c := e a)).mul contDiff_id
    · change ContDiff ℝ ∞ (fun x : ℝ ↦ (extensionEmbeddingOfIsReal hw) (Pi.mulSingle v (a * e.symm x) w))
      simp only [Pi.mulSingle_eq_of_ne h, map_one]
      exact contDiff_const
  · rintro ⟨w, hw⟩
    have h : w ≠ v := fun h ↦ (not_isComplex_iff_isReal.mpr hv) (h ▸ hw)
    change ContDiff ℝ ∞ (fun x : ℝ ↦ (extensionEmbedding w) (Pi.mulSingle v (a * e.symm x) w))
    simp only [Pi.mulSingle_eq_of_ne h, map_one]
    exact contDiff_const

/-- At a complex place the restriction of the idele-class test is real-smooth
in its complex coordinate. -/
public theorem contDiff_archimedeanRestriction_complex {v : InfinitePlace K} (hv : v.IsComplex)
    (φ : C → ℂ) (hφ : IsIdeleClassTest φ) :
    ContDiff ℝ ∞ (archimedeanRestrictionInCoordinates (ringEquivComplexOfIsComplex hv) φ) := by
  let e := ringEquivComplexOfIsComplex hv
  apply contDiff_archimedeanRestrictionInCoordinates e (isometryEquivComplexOfIsComplex hv).continuous
    (isometryEquivComplexOfIsComplex hv).symm.continuous φ hφ
  intro a
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply ContDiff.prodMk <;> apply contDiff_pi'
  · rintro ⟨w, hw⟩
    have h : w ≠ v := fun h ↦ (not_isReal_iff_isComplex.mpr hv) (h ▸ hw)
    change ContDiff ℝ ∞ (fun x : ℂ ↦ (extensionEmbeddingOfIsReal hw) (Pi.mulSingle v (a * e.symm x) w))
    simp only [Pi.mulSingle_eq_of_ne h, map_one]
    exact contDiff_const
  · rintro ⟨w, hw⟩
    by_cases h : w = v
    · subst w
      change ContDiff ℝ ∞ (fun x : ℂ ↦ e (Pi.mulSingle v (a * e.symm x) v))
      simp only [Pi.mulSingle_eq_same, map_mul, RingEquiv.apply_symm_apply]
      exact (contDiff_const (c := e a)).mul contDiff_id
    · change ContDiff ℝ ∞ (fun x : ℂ ↦ (extensionEmbedding w) (Pi.mulSingle v (a * e.symm x) w))
      simp only [Pi.mulSingle_eq_of_ne h, map_one]
      exact contDiff_const

end Coordinates

end Masullo
