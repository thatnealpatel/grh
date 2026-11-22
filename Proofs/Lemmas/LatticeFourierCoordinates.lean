module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# Fourier coordinates of a Euclidean lattice

Real coordinates in a lattice basis transport product Lebesgue measure to Euclidean volume
scaled by the inverse covolume. The negative product character on the coordinates modulo `1`
then becomes the ordinary Fourier kernel at the corresponding integer dual-basis frequency.
-/

open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace

namespace ZLattice

variable {V d : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The dual submodule for the Euclidean inner product. -/
@[expose] public noncomputable def euclideanDual (L : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) L

/-- The Euclidean dual pairs integrally with every vector of the original lattice. -/
public theorem mem_euclideanDual_iff {L : Submodule ℤ V} {y : V} :
    y ∈ euclideanDual L ↔ ∀ v : L, ∃ m : ℤ, (m : ℝ) = ⟪(v : V), y⟫ := by
  simp only [euclideanDual, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    algebraMap_int_eq, innerₗ_apply_apply]
  exact ⟨fun h v ↦ by rw [real_inner_comm]; exact h v v.property,
    fun h v hv ↦ by rw [real_inner_comm]; exact h ⟨v, hv⟩⟩

private theorem inner_nondegenerate : LinearMap.BilinForm.Nondegenerate (innerₗ V) :=
  ⟨fun v h ↦ inner_self_eq_zero.mp (h v), fun v h ↦ inner_self_eq_zero.mp (h v)⟩

variable [FiniteDimensional ℝ V] [Fintype d]
  {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]

/-- Synthesize a Euclidean vector from its real coordinates in the lattice basis. -/
@[expose] public noncomputable def basisSynthesis (b : Basis d ℤ L) : (d → ℝ) ≃L[ℝ] V :=
  (b.ofZLatticeBasis ℝ L).equivFun.symm.toContinuousLinearEquiv

public theorem basisSynthesis_apply (b : Basis d ℤ L) (x : d → ℝ) :
    basisSynthesis b x = ∑ i, x i • (b i : V) := by
  change (b.ofZLatticeBasis ℝ L).equivFun.symm x = _
  simp only [Basis.equivFun_symm_apply, Basis.ofZLatticeBasis_apply]

/-- The basis Euclidean-dual to the real extension of a lattice basis. -/
public noncomputable def euclideanDualBasis (b : Basis d ℤ L) : Basis d ℝ V := by
  classical
  exact LinearMap.BilinForm.dualBasis (innerₗ V) inner_nondegenerate (b.ofZLatticeBasis ℝ L)

public theorem euclideanDualBasis_equivFun (b : Basis d ℤ L) (y : V) (i : d) :
    (euclideanDualBasis b).equivFun y i = ⟪(b i : V), y⟫ := by
  classical
  rw [Basis.equivFun_apply, euclideanDualBasis, LinearMap.BilinForm.dualBasis_repr_apply,
    innerₗ_apply_apply, Basis.ofZLatticeBasis_apply, real_inner_comm]

/-- The Euclidean frequency with integer coordinates in the dual basis. -/
@[expose] public noncomputable def dualFrequency (b : Basis d ℤ L) (n : d → ℤ) : V :=
  (euclideanDualBasis b).equivFun.symm (fun i ↦ (n i : ℝ))

@[simp] public theorem inner_basis_dualFrequency (b : Basis d ℤ L) (n : d → ℤ) (i : d) :
    ⟪(b i : V), dualFrequency b n⟫ = (n i : ℝ) := by
  rw [← euclideanDualBasis_equivFun b, dualFrequency, LinearEquiv.apply_symm_apply]

public theorem dualFrequency_eq_iff (b : Basis d ℤ L) (n : d → ℤ) (y : V) :
    dualFrequency b n = y ↔ ∀ i, ⟪(b i : V), y⟫ = (n i : ℝ) := by
  constructor
  · rintro rfl i
    exact inner_basis_dualFrequency b n i
  · intro h
    apply (euclideanDualBasis b).equivFun.injective
    funext i
    rw [euclideanDualBasis_equivFun, euclideanDualBasis_equivFun, inner_basis_dualFrequency, h]

omit [FiniteDimensional ℝ V] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Testing integrality against a lattice basis is sufficient to test the full Euclidean dual. -/
public theorem mem_euclideanDual_iff_basis (b : Basis d ℤ L) (y : V) :
    y ∈ euclideanDual L ↔ ∀ i, ∃ m : ℤ, (m : ℝ) = ⟪(b i : V), y⟫ := by
  rw [mem_euclideanDual_iff]
  refine ⟨fun h i ↦ h (b i), fun h v ↦ ?_⟩
  classical
  choose n hn using h
  refine ⟨∑ i, b.equivFun v i * n i, ?_⟩
  have hv : (v : V) = ∑ i, b.equivFun v i • (b i : V) := by
    simpa only [map_sum, map_smul, Submodule.coe_subtype] using
      congrArg L.subtype (b.sum_equivFun v).symm
  rw [hv, sum_inner]
  push_cast
  simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hn]

/-- Integer tuples index the Euclidean dual lattice without omissions or repetitions. -/
@[expose] public noncomputable def dualFrequencyEquiv (b : Basis d ℤ L) : (d → ℤ) ≃ euclideanDual L :=
  Equiv.ofBijective
    (fun n ↦ ⟨dualFrequency b n, (mem_euclideanDual_iff_basis b _).2 fun i ↦
      ⟨n i, (inner_basis_dualFrequency b n i).symm⟩⟩) (by
    constructor
    · intro n m h
      have he := congrArg Subtype.val h
      have hn := (dualFrequency_eq_iff b n (dualFrequency b m)).1 he
      funext i
      have hi := hn i
      rw [inner_basis_dualFrequency] at hi
      exact (Int.cast_inj.mp hi).symm
    · intro y
      choose n hn using (mem_euclideanDual_iff_basis b (y : V)).1 y.property
      exact ⟨n, Subtype.ext ((dualFrequency_eq_iff b n (y : V)).2 fun i ↦ (hn i).symm)⟩)

@[simp] public theorem coe_dualFrequencyEquiv_apply (b : Basis d ℤ L) (n : d → ℤ) :
    (dualFrequencyEquiv b n : V) = dualFrequency b n := rfl

private theorem inner_basisSynthesis_dualFrequency (b : Basis d ℤ L) (x : d → ℝ) (n : d → ℤ) :
    ⟪basisSynthesis b x, dualFrequency b n⟫ = ∑ i, x i * (n i : ℝ) := by
  simp only [basisSynthesis_apply, sum_inner, real_inner_smul_left, inner_basis_dualFrequency]

/-- The product character of the coordinates modulo `1` is the Euclidean Fourier kernel
at the corresponding dual-basis frequency, with the negative Fourier sign. -/
public theorem mFourier_neg_eq_fourierChar (b : Basis d ℤ L) (n : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier (-n) (fun i ↦ (x i : UnitAddCircle)) =
      (𝐞 (-⟪basisSynthesis b x, dualFrequency b n⟫) : ℂ) := by
  rw [inner_basisSynthesis_dualFrequency, Real.fourierChar_apply]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply,
    Complex.ofReal_one, div_one, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [MeasurableSpace V] [BorelSpace V]

/-- Product Lebesgue measure in lattice coordinates pushes forward to Euclidean volume
scaled by the inverse covolume. -/
public theorem map_volume_basisSynthesis (b : Basis d ℤ L) :
    Measure.map (basisSynthesis b) volume = ENNReal.ofReal (covolume L volume)⁻¹ • volume := by
  ext s hs
  rw [Measure.map_apply (basisSynthesis b).continuous.measurable hs, smul_apply,
    smul_eq_mul]
  change volume ((b.ofZLatticeBasis ℝ L).equivFun.symm ⁻¹' s) = _
  rw [← LinearEquiv.image_eq_preimage_symm, volume_image_eq_volume_div_covolume' L b
    hs.nullMeasurableSet, div_eq_mul_inv, ENNReal.ofReal_inv_of_pos (covolume_pos L volume),
    mul_comm]

/-- Integrating over all real lattice coordinates against the negative product character
is the ordinary Euclidean Fourier transform at the corresponding dual-lattice point,
scaled by the inverse covolume. Only the character is evaluated modulo `1`. -/
public theorem integral_mFourier_basisSynthesis (b : Basis d ℤ L) (f : V → ℂ) (n : d → ℤ) :
    (∫ x : d → ℝ, UnitAddTorus.mFourier (-n) (fun i ↦ (x i : UnitAddCircle)) •
        f (basisSynthesis b x)) = (covolume L volume)⁻¹ • 𝓕 f (dualFrequency b n) := by
  let g : V → ℂ := fun v ↦ 𝐞 (-⟪v, dualFrequency b n⟫) • f v
  have h : MeasurableEmbedding (basisSynthesis b) :=
    (basisSynthesis b).toHomeomorph.measurableEmbedding
  calc
    _ = ∫ x : d → ℝ, g (basisSynthesis b x) := by
      simp only [mFourier_neg_eq_fourierChar b n, g, Circle.smul_def]
    _ = ∫ v, g v ∂Measure.map (basisSynthesis b) volume := (h.integral_map g).symm
    _ = _ := by
      rw [map_volume_basisSynthesis, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (covolume_pos L volume).le), Real.fourier_eq]

end ZLattice
