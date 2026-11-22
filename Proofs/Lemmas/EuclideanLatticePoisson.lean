module

public import Lemmas.LatticeFourierCoordinates
import Lemmas.MixedLatticeGaussianPoisson
import Lemmas.TorusGaussianPeriodization
import Lemmas.TorusLatticePoisson

/-!
# Poisson summation on a Euclidean lattice

A lattice basis transfers continuous periodization to the coordinate torus. The negative
coordinate characters become ordinary Euclidean Fourier phases on the Euclidean dual;
changing variables contributes the inverse covolume.
-/

open MeasureTheory Module
open scoped FourierTransform

namespace ZLattice

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Poisson summation for a continuous, integrable, rapidly decaying function on a finite-dimensional
Euclidean space. Only summability of the sampled transform is required on the dual side. -/
public theorem tsum_eq_covolume_inv_smul_tsum_fourier (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ) (hf : Continuous f) (hfi : Integrable f)
    (hdecay : ∀ p : ℕ, ∃ A ≥ (0 : ℝ), ∀ x, ‖x‖ ^ p * ‖f x‖ ≤ A)
    (hs : Summable (fun y : euclideanDual L ↦ 𝓕 f (y : V))) :
    (∑' x : L, f (x : V)) = (covolume L volume)⁻¹ • ∑' y : euclideanDual L, 𝓕 f (y : V) := by
  classical
  let d := Free.ChooseBasisIndex ℤ L
  let b : Basis d ℤ L := Free.chooseBasis ℤ L
  let B := basisSynthesis b
  let g : (d → ℝ) → ℂ := f ∘ B
  have hg : Continuous g := hf.comp B.continuous
  have hgi : Integrable g := by
    have hmap : Integrable f (Measure.map B volume) := by
      rw [map_volume_basisSynthesis b]
      exact hfi.smul_measure ENNReal.ofReal_ne_top
    exact hmap.comp_measurable B.continuous.measurable
  obtain ⟨A, _, hA⟩ := Masullo.rapidDecay_comp_continuousLinearEquiv B f
    (Fintype.card d + 1) (hdecay (Fintype.card d + 1))
  let G := Masullo.torusPeriodizationOfDecay g hg (Nat.lt_succ_self _) hA
  have hG (x : d → ℝ) : G (Masullo.torusReduce x) =
      ∑' k : d → ℤ, g (x + Masullo.torusLatticePoint k) :=
    Masullo.torusPeriodizationOfDecay_apply_coe g hg (Nat.lt_succ_self _) hA x
  have hsample (n : d → ℤ) : Masullo.torusFourierSample g n =
      (covolume L volume)⁻¹ • 𝓕 f (dualFrequencyEquiv b n : V) := by
    change (∫ x : d → ℝ, UnitAddTorus.mFourier (-n) (fun i ↦ (x i : UnitAddCircle)) *
      f (basisSynthesis b x)) = _
    simpa only [smul_eq_mul, coe_dualFrequencyEquiv_apply] using
      integral_mFourier_basisSynthesis b f n
  have hs' : Summable (fun n : d → ℤ ↦ 𝓕 f (dualFrequencyEquiv b n : V)) :=
    (dualFrequencyEquiv b).summable_iff.mpr hs
  have hsg : Summable (Masullo.torusFourierSample g) := by
    rw [funext hsample]
    exact hs'.const_smul (covolume L volume)⁻¹
  have hcoord (k : d → ℤ) : B (Masullo.torusLatticePoint k) = (b.equivFun.symm k : V) := by
    change basisSynthesis b (Masullo.torusLatticePoint k) = _
    rw [basisSynthesis_apply, Basis.equivFun_symm_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Masullo.torusLatticePoint,
      Int.cast_smul_eq_zsmul]
  calc
    (∑' x : L, f (x : V)) = ∑' k : d → ℤ, g (Masullo.torusLatticePoint k) := by
      rw [show (fun k : d → ℤ ↦ g (Masullo.torusLatticePoint k)) =
        (fun k ↦ f (b.equivFun.symm k : V)) from funext fun k ↦ congrArg f (hcoord k)]
      exact (b.equivFun.symm.toEquiv.tsum_eq (fun x : L ↦ f (x : V))).symm
    _ = ∑' n : d → ℤ, Masullo.torusFourierSample g n := Masullo.torus_lattice_poisson hgi hG hsg
    _ = (covolume L volume)⁻¹ • ∑' n : d → ℤ, 𝓕 f (dualFrequencyEquiv b n : V) := by
      simp only [hsample, hs'.tsum_const_smul]
    _ = _ := congrArg ((covolume L volume)⁻¹ • ·)
      ((dualFrequencyEquiv b).tsum_eq (fun y : euclideanDual L ↦ 𝓕 f (y : V)))

end ZLattice
