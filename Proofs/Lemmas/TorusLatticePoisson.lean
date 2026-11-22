module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Poisson summation on the coordinate lattice

We unfold the Fourier coefficients of a continuous periodization over the unit box.
Integrability on the real vector space supplies the bound for exchanging integration and
summation; no pointwise absolute convergence hypothesis is needed for this step.
-/

open MeasureTheory Set UnitAddTorus

namespace Masullo

variable {d : Type*}

/-- Reduction modulo the integer lattice in each real coordinate. -/
@[expose] public def torusReduce (x : d → ℝ) : UnitAddTorus d := fun i ↦ x i

/-- The real vector corresponding to an integer vector. -/
@[expose] public def torusLatticePoint (k : d → ℤ) : d → ℝ := fun i ↦ k i

private theorem torusReduce_add_lattice (x : d → ℝ) (k : d → ℤ) :
    torusReduce (x + torusLatticePoint k) = torusReduce x := by
  funext i
  change ((x i + (k i : ℝ) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  have h : ((k i : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k i, by simp [zsmul_eq_mul]⟩
  rw [AddCircle.coe_add, h, add_zero]

variable [Fintype d]

/-- The ordinary Fourier integral at integer frequency `n`, with the negative phase. -/
@[expose] public noncomputable def torusFourierSample (f : (d → ℝ) → ℂ) (n : d → ℤ) : ℂ :=
  ∫ x, mFourier (-n) (torusReduce x) * f x

private theorem norm_mFourier_apply (n : d → ℤ) (t : UnitAddTorus d) :
    ‖mFourier n t‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
    Finset.prod_const_one]

private noncomputable abbrev CoordinateLattice (d : Type*) [Fintype d] :=
  (Submodule.span ℤ (range (Pi.basisFun ℝ d))).toAddSubgroup

private noncomputable def coordinateLatticeEquiv : (d → ℤ) ≃ CoordinateLattice d := by
  have mem_iff (x : d → ℝ) : x ∈ CoordinateLattice d ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = x i := by
    change x ∈ Submodule.span ℤ (range (Pi.basisFun ℝ d)) ↔ _
    simpa only [Pi.basisFun_repr, mem_range, algebraMap_int_eq, Int.coe_castRingHom] using
      (Pi.basisFun ℝ d).mem_span_iff_repr_mem ℤ x
  refine Equiv.ofBijective (fun k ↦ ⟨torusLatticePoint k, (mem_iff _).2 fun i ↦ ⟨k i, rfl⟩⟩)
    ⟨?_, ?_⟩
  · intro k l h
    funext i
    have hi : (k i : ℝ) = (l i : ℝ) := congrArg (fun v : CoordinateLattice d ↦ v.val i) h
    exact_mod_cast hi
  · intro x
    choose k hk using (mem_iff x.val).1 x.property
    exact ⟨k, Subtype.ext (funext hk)⟩

private theorem coordinateLatticeEquiv_vadd (k : d → ℤ) (x : d → ℝ) :
    coordinateLatticeEquiv k +ᵥ x = x + torusLatticePoint k := by
  change torusLatticePoint k + x = _
  exact add_comm _ _

private def unitBox (d : Type*) : Set (d → ℝ) := {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}

private theorem unitBox_fundamentalDomain :
    IsAddFundamentalDomain (CoordinateLattice d) (unitBox d) volume := by
  let e : (d → ℝ) ≃ (d → ℝ) :=
    ⟨fun x ↦ 1 - x, fun x ↦ 1 - x, sub_sub_cancel 1, sub_sub_cancel 1⟩
  have he : e '' ZSpan.fundamentalDomain (Pi.basisFun ℝ d) = unitBox d := by
    rw [e.image_eq_preimage_symm, ZSpan.fundamentalDomain_pi_basisFun]
    ext x
    simp only [unitBox, mem_preimage, mem_ofPred_eq, mem_pi, mem_univ, forall_true_left]
    apply forall_congr'
    intro i
    change 1 - x i ∈ Ico (0 : ℝ) 1 ↔ x i ∈ Ioc (0 : ℝ) 1
    simp [sub_nonneg, sub_lt_self_iff, and_comm]
  rw [← he]
  refine (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ d) volume).image_of_equiv e
    (volume.measurePreserving_sub_left (1 : d → ℝ)).quasiMeasurePreserving
    (Equiv.neg (CoordinateLattice d)) ?_
  intro g x
  change 1 - (-(g : d → ℝ) + x) = (g : d → ℝ) + (1 - x)
  abel

private theorem integral_torus_lattice_translates {g : (d → ℝ) → ℂ} (hg : Integrable g) :
    (∫ x in unitBox d, ∑' k : d → ℤ, g (x + torusLatticePoint k)) = ∫ x, g x := by
  have : Countable (CoordinateLattice d) := Countable.of_equiv _ coordinateLatticeEquiv
  let F (k : CoordinateLattice d) (x : d → ℝ) := g (k +ᵥ x)
  have hF (k : CoordinateLattice d) :
      AEStronglyMeasurable (F k) (volume.restrict (unitBox d)) :=
    (hg.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_vadd k volume).quasiMeasurePreserving).restrict
  have hfin : (∑' k : CoordinateLattice d, ∫⁻ x in unitBox d, ‖F k x‖ₑ) ≠ ⊤ := by
    rw [← unitBox_fundamentalDomain.lintegral_eq_tsum'' (fun x ↦ ‖g x‖ₑ)]
    exact hg.hasFiniteIntegral.ne
  calc
    (∫ x in unitBox d, ∑' k : d → ℤ, g (x + torusLatticePoint k)) =
        ∫ x in unitBox d, ∑' k : CoordinateLattice d, F k x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        simpa only [F, coordinateLatticeEquiv_vadd] using
          coordinateLatticeEquiv.tsum_eq (fun k : CoordinateLattice d ↦ F k x)
    _ = ∑' k : CoordinateLattice d, ∫ x in unitBox d, F k x := integral_tsum hF hfin
    _ = ∫ x, g x := (unitBox_fundamentalDomain.integral_eq_tsum'' g hg).symm

/-- An integrable function's periodization has the ordinary Fourier samples as its torus
coefficients. Agreement with the periodization is needed only almost everywhere in the unit box. -/
public theorem torus_mFourierCoeff_eq_sample {f : (d → ℝ) → ℂ} (hf : Integrable f)
    {G : C(UnitAddTorus d, ℂ)}
    (hG : ∀ᵐ x ∂volume.restrict {x : d → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1},
      G (torusReduce x) = ∑' k : d → ℤ, f (x + torusLatticePoint k)) (n : d → ℤ) :
    mFourierCoeff G n = torusFourierSample f n := by
  let phase (x : d → ℝ) := mFourier (-n) (torusReduce x)
  have hphase : Continuous phase :=
    (mFourier (-n)).continuous.comp (continuous_pi fun i ↦
      (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i))
  have hint : Integrable (fun x ↦ phase x * f x) := by
    refine hf.norm.mono' (hphase.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun x ↦ by simp [phase, norm_mFourier_apply]
  calc
    mFourierCoeff G n = ∫ x in unitBox d, phase x * G (torusReduce x) := by
      simpa only [Pi.zero_apply, zero_add, smul_eq_mul] using!
        mFourierCoeff_eq_integral G n (0 : d → ℝ)
    _ = ∫ x in unitBox d, ∑' k : d → ℤ, phase (x + torusLatticePoint k) *
        f (x + torusLatticePoint k) := by
      apply integral_congr_ae
      filter_upwards [hG] with x hx
      simp only [phase, torusReduce_add_lattice, tsum_mul_left, hx]
    _ = torusFourierSample f n := integral_torus_lattice_translates hint

/-- The Fourier series of the periodization sums at every real vector, with the usual
positive phase on the Fourier series side. The lattice side is stated as a `tsum`, so this
conclusion does not by itself assert pointwise summability of the spatial samples. -/
public theorem hasSum_torus_lattice_poisson {f : (d → ℝ) → ℂ} (hf : Integrable f)
    {G : C(UnitAddTorus d, ℂ)}
    (hG : ∀ x : d → ℝ, G (torusReduce x) = ∑' k : d → ℤ, f (x + torusLatticePoint k))
    (hs : Summable (torusFourierSample f)) (x : d → ℝ) :
    HasSum (fun n ↦ torusFourierSample f n * mFourier n (torusReduce x))
      (∑' k : d → ℤ, f (x + torusLatticePoint k)) := by
  have hcoeff : mFourierCoeff G = torusFourierSample f :=
    funext (torus_mFourierCoeff_eq_sample hf (Filter.Eventually.of_forall hG))
  have hsum := hasSum_mFourier_series_apply_of_summable (f := G)
    (hcoeff.symm ▸ hs) (torusReduce x)
  simpa only [hcoeff, smul_eq_mul, hG x] using hsum

/-- Coordinate Poisson summation at the origin. -/
public theorem torus_lattice_poisson {f : (d → ℝ) → ℂ} (hf : Integrable f)
    {G : C(UnitAddTorus d, ℂ)}
    (hG : ∀ x : d → ℝ, G (torusReduce x) = ∑' k : d → ℤ, f (x + torusLatticePoint k))
    (hs : Summable (torusFourierSample f)) :
    (∑' k : d → ℤ, f (torusLatticePoint k)) = ∑' n : d → ℤ, torusFourierSample f n := by
  have hzero (n : d → ℤ) : mFourier n (torusReduce (0 : d → ℝ)) = 1 := by
    simp only [mFourier, ContinuousMap.coe_mk, torusReduce, Pi.zero_apply, AddCircle.coe_zero,
      fourier_eval_zero, Finset.prod_const_one]
  simpa only [zero_add, hzero, mul_one] using
    (hasSum_torus_lattice_poisson hf hG hs 0).tsum_eq.symm

end Masullo
