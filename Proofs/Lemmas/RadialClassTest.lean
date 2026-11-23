module

public import Props.IdeleClassStripTrace

import Theorems.IdeleIdealClassStrict
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Radial Bruhat tests on idèle classes of a number field -/

open Filter NumberField Set
open InfinitePlace InfinitePlace.Completion
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Classical ContDiff Topology

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "M" => mixedEmbedding.mixedSpace K
local notation "logNorm" => (fun c : C ↦ Real.log (ideleClassNorm c))

private theorem hasCompactSupport_radial {F : ℝ → ℂ} (hc : HasCompactSupport F) :
    HasCompactSupport (F ∘ logNorm) := by
  let : CompactSpace C₁ := compactHausdorff_ideleClassNormOne.1
  let s := ideleClassLogSection (w₀ : InfinitePlace K)
  let hs := ideleClassLogNorm_section (w₀ : InfinitePlace K)
  let τ := ideleClassLogSplit s hs
  have hcompact := ((hc.image continuous_ofAdd).prod (isCompact_univ (X := C₁))).image
    (map_continuous τ)
  have hlog : Continuous logNorm := by
    simpa only [Function.comp_def, ideleClassLogNorm_apply] using
      continuous_toAdd.comp (map_continuous (ideleClassLogNorm (K := K)))
  apply hcompact.of_isClosed_subset (isClosed_tsupport _)
  intro c hc'
  have hm := tsupport_comp_subset_preimage F hlog hc'
  refine ⟨τ.symm c, ⟨⟨logNorm c, hm, ?_⟩, mem_univ _⟩, τ.apply_symm_apply c⟩
  change Multiplicative.ofAdd (Real.log (ideleClassNorm c)) = ((ideleClassLogSplit s hs).symm c).1
  rw [ideleClassLogSplit_symm, ← ideleClassLogNorm_apply, ofAdd_toAdd]

/-- Extend the profile by zero at nonpositive norms. Compact support makes
this extension identically zero on a neighborhood of zero. -/
private noncomputable def positiveLogProfile (F : ℝ → ℂ) (y : ℝ) : ℂ :=
  if 0 < y then F (Real.log y) else 0

private theorem contDiff_positiveLogProfile {F : ℝ → ℂ} (hf : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : ContDiff ℝ ∞ (positiveLogProfile F) := by
  obtain ⟨a, ha⟩ := hc.bddBelow
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · have hlog : ContDiffAt ℝ ∞ Real.log y := Real.contDiffAt_log.mpr hy.ne'
    apply (hf.contDiffAt.comp y hlog).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact ite_eq_left (show 0 < t from ht)
  · have hy' : y < Real.exp a := (le_of_not_gt hy).trans_lt (Real.exp_pos a)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hy'] with t ht
    by_cases ht' : 0 < t
    · rw [positiveLogProfile, ite_eq_left ht']
      by_contra hF
      exact (not_lt_of_ge (ha (subset_tsupport F hF)))
        ((Real.log_lt_iff_lt_exp ht').mpr ht)
    · exact ite_eq_right ht'

/-- The normalized Archimedean product with a signed factor at each real
place. It is polynomial, and agrees with the norm near the identity. -/
private noncomputable def archimedeanProduct (z : M) : ℝ :=
  (∏ v : {w : InfinitePlace K // w.IsReal}, z.1 v) *
    ∏ v : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (z.2 v)

private theorem contDiff_archimedeanProduct : ContDiff ℝ ∞ (archimedeanProduct (K := K)) := by
  unfold archimedeanProduct
  apply ContDiff.mul
  · exact contDiff_prod fun v _ ↦ (contDiff_apply ℝ (fun _ ↦ ℝ) v).comp contDiff_fst
  · apply contDiff_prod
    intro v _
    have hz : ContDiff ℝ ∞ (fun z : M ↦ z.2 v) :=
      (contDiff_apply ℝ (fun _ ↦ ℂ) v).comp contDiff_snd
    have hr := Complex.reCLM.contDiff.comp hz
    have hi := Complex.imCLM.contDiff.comp hz
    exact (hr.mul hr).add (hi.mul hi)

private theorem abs_archimedeanProduct_mixed (a : InfiniteAdeleRing K) :
    |archimedeanProduct (InfiniteAdeleRing.ringEquiv_mixedSpace K a)| =
      ∏ w : InfinitePlace K, ‖a w‖ ^ w.mult := by
  rw [archimedeanProduct, abs_mul, Finset.abs_prod, Finset.abs_prod, prod_eq_prod_mul_prod]
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply congrArg₂ (· * ·) <;> apply Finset.prod_congr rfl <;> intro v _
  · rw [mult_isReal v, pow_one, ← Real.norm_eq_abs]
    exact (isometry_extensionEmbeddingOfIsReal v.property).norm_map_of_map_zero (map_zero _) _
  · rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, mult_isComplex v]
    congr 1
    exact (isometry_extensionEmbedding v.val).norm_map_of_map_zero (map_zero _) _

private theorem continuous_mixedInfinite :
    Continuous (fun x : I ↦ InfiniteAdeleRing.ringEquiv_mixedSpace K x.val.1) := by
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  have h (v : InfinitePlace K) : Continuous (fun x : I ↦ x.val.1 v) :=
    (continuous_apply v).comp (continuous_fst.comp Units.continuous_val)
  exact (continuous_pi fun v ↦ (isometry_extensionEmbeddingOfIsReal v.property).continuous.comp
    (h v.val)).prodMk (continuous_pi fun v ↦ (isometry_extensionEmbedding v.val).continuous.comp
    (h v.val))

/-- A smooth compactly supported profile of the log norm is a Bruhat test on
idèle classes over any number field. -/
public theorem isIdeleClassTest_radial {F : ℝ → ℂ} (hf : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : IsIdeleClassTest (fun c : C ↦ F (Real.log (ideleClassNorm c))) := by
  refine ⟨hasCompactSupport_radial hc, fun c ↦ ?_⟩
  refine ⟨fun z ↦ positiveLogProfile F (ideleClassNorm c * archimedeanProduct z),
    (contDiff_positiveLogProfile hf hc).comp (contDiff_const.mul contDiff_archimedeanProduct), ?_⟩
  have hfin : ∀ᶠ x : I in 𝓝 1, x ∈ ideleFiniteUnits := by
    have hopen : IsOpen (ideleFiniteUnits (K := K) : Set I) := by
      rw [← range_ideleFiniteStageEmbedding_empty]
      exact (isOpenEmbedding_ideleFiniteStageEmbedding K ∅).isOpen_range
    exact hopen.mem_nhds ideleFiniteUnits.one_mem
  let P (x : I) := archimedeanProduct (InfiniteAdeleRing.ringEquiv_mixedSpace K x.val.1)
  have hP : Continuous P := contDiff_archimedeanProduct.continuous.comp continuous_mixedInfinite
  have hpos : ∀ᶠ x in 𝓝 1, 0 < P x := by
    apply hP.continuousAt (Ioi_mem_nhds _)
    change 0 < archimedeanProduct (InfiniteAdeleRing.ringEquiv_mixedSpace K 1)
    rw [map_one]
    simp [archimedeanProduct]
  filter_upwards [hfin, hpos] with x hx hxpos
  have hnorm : ideleNorm x = P x := by
    rw [ideleNorm_of_mem_ideleFiniteUnits hx, ← abs_archimedeanProduct_mixed]
    exact abs_of_pos hxpos
  change F (Real.log (ideleClassNorm (c * QuotientGroup.mk x))) =
    positiveLogProfile F (ideleClassNorm c * P x)
  rw [map_mul, ideleClassNorm_mk, hnorm, positiveLogProfile,
    ite_eq_left (mul_pos (ideleClassNorm_pos c) hxpos)]

end Masullo
