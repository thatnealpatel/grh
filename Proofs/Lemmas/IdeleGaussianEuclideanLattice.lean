module

public import Lemmas.IdeleGaussianIdeal
public import Lemmas.IdeleMixedScale
public import Lemmas.LatticeFourierCoordinates
public import Theorems.ArchimedeanIdealDual
import Lemmas.FiniteIdeleIdealNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The idele-dilated Euclidean ideal lattice

Dilation transports the accepted unscaled ideal dual by the inverse adjoint and
multiplies the ordinary Euclidean covolume by the absolute determinant.
-/

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical InnerProductSpace nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "I" => IdeleGroup (𝓞 K) K
local notation "F" => FractionalIdeal (𝓞 K)⁰ K
local notation "M" => mixedSpace K
local notation "E" => euclidean.mixedSpace K
local notation "c" => euclidean.toMixed K
local notation "J" => archimedeanTraceFrequency K

private noncomputable def mixedDilation (g : I) : M ≃ₗ[ℝ] M where
  __ := ideleMixedScale g
  invFun := ideleMixedScale g⁻¹
  left_inv x := by
    change ideleMixedScale g⁻¹ (ideleMixedScale g x) = x
    rw [ideleMixedScale_apply, ideleMixedScale_apply, ← mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, one_mul]
  right_inv x := by
    change ideleMixedScale g (ideleMixedScale g⁻¹ x) = x
    rw [ideleMixedScale_apply, ideleMixedScale_apply, ← mul_assoc, ← map_mul,
      mul_inv_cancel, map_one, one_mul]

private noncomputable def euclideanDilation (g : I) : E ≃L[ℝ] E :=
  (c).trans ((mixedDilation g).toContinuousLinearEquiv.trans (c).symm)

local notation "A" => euclideanDilation

private theorem coords_dilate (g : I) (x : E) : c (A g x) = ideleMixedScale g (c x) :=
  (c).apply_symm_apply _

private theorem coords_dilate_symm (g : I) (x : E) :
    c ((A g).symm x) = ideleMixedScale g⁻¹ (c x) :=
  (c).apply_symm_apply _

/-- The archimedean dilation of the lattice of the inverse finite ideal. -/
public noncomputable def ideleGaussianEuclideanLattice (g : I) : Submodule ℤ E :=
  ZLattice.comap ℝ (archimedeanIdealLattice K (ideleGaussianIdeal g)) (A g).symm.toLinearMap

local notation "L" => ideleGaussianEuclideanLattice

public instance (g : I) : DiscreteTopology (L g) := by
  unfold ideleGaussianEuclideanLattice
  infer_instance

public instance (g : I) : IsZLattice ℝ (L g) := by
  unfold ideleGaussianEuclideanLattice
  infer_instance

private theorem mem_scaled (g : I) (u : E) : u ∈ L g ↔
    ∃ x ∈ (ideleGaussianIdeal g : F), A g (archimedeanEuclideanEmbedding K x) = u := by
  change (A g).symm u ∈ archimedeanIdealLattice K (ideleGaussianIdeal g) ↔ _
  rw [mem_archimedeanIdealLattice]
  exact exists_congr fun x ↦ and_congr_right fun _ ↦ (A g).eq_symm_apply

/-- Reindex the lattice sum by the field elements of the inverse finite ideal. -/
public noncomputable def ideleGaussianEuclideanLatticeEquiv (g : I) :
    ↥(ideleGaussianIdeal g : F) ≃ L g := by
  let f (x : ↥(ideleGaussianIdeal g : F)) : L g :=
    ⟨A g (archimedeanEuclideanEmbedding K x), (mem_scaled g _).2 ⟨x, x.2, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext ((mixedEmbedding K).injective ((c).symm.injective
      ((A g).injective (congrArg Subtype.val h))))
  · intro u
    obtain ⟨x, hx, hu⟩ := (mem_scaled g u).1 u.2
    exact ⟨⟨x, hx⟩, Subtype.ext hu⟩

public theorem ideleGaussianEuclideanLatticeEquiv_apply (g : I)
    (x : ↥(ideleGaussianIdeal g : F)) :
    (ideleGaussianEuclideanLatticeEquiv g x : E) =
      (c).symm (ideleMixedScale g (mixedEmbedding K x)) := by
  rfl

private theorem inner_dilate_traceFrequency (g : I) (x y : E) :
    ⟪A g x, J ((A g).symm y)⟫_ℝ = ⟪x, J y⟫_ℝ := by
  have h : ideleMixedPart g * ideleMixedPart g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [inner_archimedeanTraceFrequency, inner_archimedeanTraceFrequency,
    coords_dilate, coords_dilate_symm, ideleMixedScale_apply, ideleMixedScale_apply]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro w _
  · have hw := congrArg (fun z : M ↦ z.1 w) h
    change (ideleMixedPart g).1 w * (ideleMixedPart g⁻¹).1 w = 1 at hw
    change ((ideleMixedPart g).1 w * _) * ((ideleMixedPart g⁻¹).1 w * _) = _
    rw [mul_mul_mul_comm, hw, one_mul]
  · have hw := congrArg (fun z : M ↦ z.2 w) h
    change (ideleMixedPart g).2 w * (ideleMixedPart g⁻¹).2 w = 1 at hw
    change 2 * (((ideleMixedPart g).2 w * _) * ((ideleMixedPart g⁻¹).2 w * _) : ℂ).re = _
    rw [mul_mul_mul_comm, hw, one_mul]

-- The inverse transpose of the dilation, composed with the trace frequency,
-- is the trace frequency composed with inverse dilation (in that order).
private theorem inverse_adjoint_traceFrequency (g : I) (y : E) :
    (A g).symm.toLinearMap.adjoint (J y) = J ((A g).symm y) := by
  apply ext_inner_left ℝ
  intro x
  rw [LinearMap.adjoint_inner_right]
  change ⟪(A g).symm x, J y⟫_ℝ = _
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (inner_dilate_traceFrequency g ((A g).symm x) y).symm

private theorem mem_scaled_dual (g : I) (v : E) : v ∈ ZLattice.euclideanDual (L g) ↔
    ∃ y ∈ FractionalIdeal.dual ℤ ℚ (ideleGaussianIdeal g : F),
      J ((A g).symm (archimedeanEuclideanEmbedding K y)) = v := by
  rw [ZLattice.mem_euclideanDual_iff]
  constructor
  · intro hv
    obtain ⟨y, hy, hfreq⟩ := (mem_archimedeanIdealLattice_euclideanDual K (ideleGaussianIdeal g)
      ((A g).toLinearMap.adjoint v)).mp (by
        intro u hu
        obtain ⟨n, hn⟩ := hv ⟨A g u, by
          change (A g).symm (A g u) ∈ archimedeanIdealLattice K (ideleGaussianIdeal g)
          rwa [ContinuousLinearEquiv.symm_apply_apply]⟩
        exact ⟨n, (LinearMap.adjoint_inner_right (A g).toLinearMap u v).trans hn.symm⟩)
    refine ⟨y, hy, ?_⟩
    rw [← inverse_adjoint_traceFrequency, hfreq]
    apply ext_inner_left ℝ
    intro x
    rw [LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    change ⟪A g ((A g).symm x), v⟫_ℝ = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩ ⟨u, hu⟩
    change (A g).symm u ∈ archimedeanIdealLattice K (ideleGaussianIdeal g) at hu
    obtain ⟨n, hn⟩ := (mem_archimedeanIdealLattice_euclideanDual K (ideleGaussianIdeal g)
      (J (archimedeanEuclideanEmbedding K y))).mpr ⟨y, hy, rfl⟩ _ hu
    exact ⟨n, hn.symm.trans (by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        (inner_dilate_traceFrequency g ((A g).symm u) (archimedeanEuclideanEmbedding K y)).symm)⟩

private theorem traceFrequency_injective : Function.Injective (J : E → E) := by
  intro x y h
  have h' : (c x).1 = (c y).1 ∧
      (fun w ↦ 2 * star ((c x).2 w)) = (fun w ↦ 2 * star ((c y).2 w)) :=
    Prod.mk.inj ((c).symm.injective h)
  apply (c).injective
  refine Prod.ext h'.1 (funext fun w ↦ ?_)
  exact star_injective (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (congrFun h'.2 w))

/-- Reindex the Euclidean dual by the trace-dual ideal, at inverse-dilated trace frequencies. -/
public noncomputable def ideleGaussianEuclideanDualEquiv (g : I) :
    ↥(FractionalIdeal.dual ℤ ℚ (ideleGaussianIdeal g : F)) ≃ ZLattice.euclideanDual (L g) := by
  let f (y : ↥(FractionalIdeal.dual ℤ ℚ (ideleGaussianIdeal g : F))) : ZLattice.euclideanDual (L g) :=
    ⟨J ((A g).symm (archimedeanEuclideanEmbedding K y)), (mem_scaled_dual g _).2 ⟨y, y.2, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro y z h
    exact Subtype.ext ((mixedEmbedding K).injective ((c).symm.injective
      ((A g).symm.injective (traceFrequency_injective (congrArg Subtype.val h)))))
  · intro v
    obtain ⟨y, hy, hv⟩ := (mem_scaled_dual g v).1 v.2
    exact ⟨⟨y, hy⟩, Subtype.ext hv⟩

public theorem ideleGaussianEuclideanDualEquiv_apply (g : I)
    (y : ↥(FractionalIdeal.dual ℤ ℚ (ideleGaussianIdeal g : F))) :
    (ideleGaussianEuclideanDualEquiv g y : E) =
      J ((c).symm (ideleMixedScale g⁻¹ (mixedEmbedding K y))) := by
  rfl

/-- In ordinary Euclidean volume the covolume is `2⁻ʳ² √|disc K| |g|`. -/
public theorem ideleGaussianEuclideanLattice_covolume (g : I) :
    ZLattice.covolume (L g) volume =
      (2⁻¹ : ℝ) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * ideleNorm g := by
  let U := archimedeanIdealLattice K (ideleGaussianIdeal g)
  let b := Module.Free.chooseBasis ℤ U
  have hdet : |(A g).toLinearMap.det| = ∏ w : InfinitePlace K, ‖g.val.1 w‖ ^ w.mult := by
    change |LinearMap.det ((c).symm.toLinearMap ∘ₗ ideleMixedScale g ∘ₗ (c).toLinearMap)| = _
    exact (congrArg abs (LinearMap.det_conj (ideleMixedScale g) (c).symm.toLinearEquiv)).trans
      (abs_det_ideleMixedScale g)
  rw [ideleGaussianEuclideanLattice,
    ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (ZLattice.isAddFundamentalDomain (b.ofZLatticeComap ℝ U (A g).symm.toLinearEquiv) _),
    Module.Basis.ofZLatticeBasis_comap, ContinuousLinearEquiv.symm_symm, ← ZSpan.map_fundamentalDomain]
  change volume.real ((A g).toLinearMap '' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ U)) = _
  rw [measureReal_def, Measure.addHaar_image_linearMap, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), hdet, ← measureReal_def,
    ← ZLattice.covolume_eq_measure_fundamentalDomain U _ (ZLattice.isAddFundamentalDomain b _),
    show ZLattice.covolume U volume = _ from covolume_archimedeanIdealLattice K (ideleGaussianIdeal g),
    ideleNorm_eq_archimedean_mul_absNorm_inv_finiteIdeleIdeal]
  rw [ideleGaussianIdeal, Units.val_inv_eq_inv_val]
  ring

end Masullo
