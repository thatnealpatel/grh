module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Integral coordinates of the Euclidean dual of a lattice -/

open Module
open scoped InnerProductSpace

namespace Masullo

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- The frequency coordinates of a vector are its inner products with the lattice basis. -/
@[expose] public def latticeFrequencyCoordinates (b : Basis ι ℤ L) : E ≃L[ℝ] (ι → ℝ) :=
  let A : E →ₗ[ℝ] (ι → ℝ) := LinearMap.pi fun i ↦ innerₗ E (b i)
  let hA : Function.Injective A := by
    intro v w h
    apply InnerProductSpace.ext_inner_left_basis (b.ofZLatticeBasis ℝ)
    intro i
    rw [Basis.ofZLatticeBasis_apply]
    exact congrFun h i
  (A.linearEquivOfInjective hA (b.ofZLatticeBasis ℝ).equivFun.finrank_eq).toContinuousLinearEquiv

@[simp] public theorem latticeFrequencyCoordinates_apply (b : Basis ι ℤ L) (v : E) (i : ι) :
    latticeFrequencyCoordinates b v i = ⟪(b i : E), v⟫_ℝ := rfl

/-- The Euclidean dual in basis coordinates is the inverse image of the full integer lattice. -/
@[expose] public def latticeEuclideanDual (b : Basis ι ℤ L) : Submodule ℤ E :=
  ZLattice.comap ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))
    (latticeFrequencyCoordinates b).toLinearMap

public instance (b : Basis ι ℤ L) : DiscreteTopology (latticeEuclideanDual b) :=
  inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ _ (latticeFrequencyCoordinates b).toLinearMap))

public instance (b : Basis ι ℤ L) : IsZLattice ℝ (latticeEuclideanDual b) :=
  inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ _ (latticeFrequencyCoordinates b).toLinearMap))

private theorem mem_latticeEuclideanDual_iff_basis (b : Basis ι ℤ L) (v : E) :
    v ∈ latticeEuclideanDual b ↔ ∀ i, ∃ n : ℤ, ⟪(b i : E), v⟫_ℝ = (n : ℝ) := by
  change latticeFrequencyCoordinates b v ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ _
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ]
  simp only [Pi.basisFun_repr, latticeFrequencyCoordinates_apply, Set.mem_range,
    eq_comm (a := ((algebraMap ℤ ℝ) _))]
  rfl

/-- Basis integrality extends to every lattice point; the converse tests the basis vectors. -/
public theorem mem_latticeEuclideanDual (b : Basis ι ℤ L) (v : E) :
    v ∈ latticeEuclideanDual b ↔ ∀ u ∈ L, ∃ n : ℤ, ⟪u, v⟫_ℝ = (n : ℝ) := by
  classical
  rw [mem_latticeEuclideanDual_iff_basis]
  constructor
  · intro h u hu
    choose n hn using h
    let c : ι → ℤ := b.equivFun ⟨u, hu⟩
    have hc : (∑ i, (c i : ℝ) • (b.ofZLatticeBasis ℝ) i) = u := by
      have hx := (b.ofZLatticeBasis ℝ).sum_repr (⟨u, hu⟩ : L)
      convert hx using 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [b.ofZLatticeBasis_repr_apply ℝ L (⟨u, hu⟩ : L) i]
      rfl
    refine ⟨∑ i, c i * n i, ?_⟩
    rw [← hc, sum_inner]
    simp only [real_inner_smul_left, Basis.ofZLatticeBasis_apply, hn, Int.cast_sum, Int.cast_mul]
  · intro h i
    exact h (b i) (b i).property

/-- All integer Fourier indices, including zero, enumerate the Euclidean dual without repetition. -/
public def latticeEuclideanDualIndex (b : Basis ι ℤ L) :
    (ι → ℤ) ≃ latticeEuclideanDual b := by
  let e := latticeFrequencyCoordinates b
  let f (n : ι → ℤ) : latticeEuclideanDual b := ⟨e.symm (fun i ↦ (n i : ℝ)), by
    apply (mem_latticeEuclideanDual_iff_basis b _).2
    intro i
    exact ⟨n i, congrFun (e.apply_symm_apply _) i⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro n m h
    have hnm := e.symm.injective (congrArg Subtype.val h)
    exact funext fun i ↦ Int.cast_injective (congrFun hnm i)
  · intro v
    choose n hn using (mem_latticeEuclideanDual_iff_basis b v).1 v.property
    refine ⟨n, Subtype.ext (e.injective ?_)⟩
    exact (e.apply_symm_apply _).trans (funext hn).symm

public theorem inner_latticeEuclideanDualIndex (b : Basis ι ℤ L) (n : ι → ℤ) (i : ι) :
    ⟪(b i : E), (latticeEuclideanDualIndex b n : E)⟫_ℝ = (n i : ℝ) :=
  congrFun ((latticeFrequencyCoordinates b).apply_symm_apply (fun j ↦ (n j : ℝ))) i

end

end Masullo
