module

public import Lemmas.ArchimedeanTracePairing
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # The Euclidean dual of a fractional ideal lattice

The repair toward Masullo, PDF p. 82, Theorem 2.2.3.2, is to apply ordinary
Euclidean lattice Poisson summation to the lattice cut out by the finite
support. The manuscript cites adelic Riemann–Roch and normalizes the additive
adelic quotient to mass one; neither identifies this Euclidean lattice's dual
or its covolume. In the unscaled mixed coordinates the dual is the image of
the trace dual at *trace frequencies*. The archimedean additive measure has a
factor of two per complex place (PDF pp. 556–557, Definition A.3.1.2 and Example
A.3.1.5; provisional text reading), not a mass-one normalization.
-/

open NumberField NumberField.InfinitePlace MeasureTheory
open scoped Classical InnerProductSpace ENNReal nonZeroDivisors

namespace Masullo

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

local notation "Eucl" => NumberField.mixedEmbedding.euclidean.mixedSpace K
local notation "coords" => NumberField.mixedEmbedding.euclidean.toMixed K
local notation "Frac" => FractionalIdeal (𝓞 K)⁰ K

/-- Pull back the mixed embedding of a nonzero fractional ideal to Euclidean coordinates. -/
public abbrev archimedeanIdealLattice (I : Fracˣ) : Submodule ℤ Eucl :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (coords).toLinearMap

public theorem mem_archimedeanIdealLattice (I : Fracˣ) (u : Eucl) :
    u ∈ archimedeanIdealLattice K I ↔
      ∃ x ∈ (I : Set K), archimedeanEuclideanEmbedding K x = u := by
  change (coords) u ∈ mixedEmbedding.idealLattice K I ↔ _
  rw [mixedEmbedding.mem_idealLattice]
  simp only [archimedeanEuclideanEmbedding, ContinuousLinearEquiv.symm_apply_eq]

/-- The codifferent times the inverse ideal is the rational trace dual. -/
public theorem fractionalIdeal_traceDual_eq (I : Frac) :
    FractionalIdeal.dual ℤ ℚ I =
      (↑(differentIdeal ℤ (𝓞 K)) : Frac)⁻¹ * I⁻¹ := by
  rw [FractionalIdeal.dual_eq_mul_inv, coeIdeal_differentIdeal ℤ ℚ K, inv_inv]

/-- An arbitrary ambient Euclidean frequency is integral on the lattice exactly when it
is the trace frequency of a field element in the fractional ideal's trace dual. -/
public theorem mem_archimedeanIdealLattice_euclideanDual (I : Fracˣ) (v : Eucl) :
    (∀ u ∈ archimedeanIdealLattice K I, ∃ n : ℤ, ⟪u, v⟫_ℝ = (n : ℝ)) ↔
      ∃ y ∈ FractionalIdeal.dual ℤ ℚ I.val,
        archimedeanTraceFrequency K (archimedeanEuclideanEmbedding K y) = v := by
  constructor
  · intro hv
    let b := basisOfFractionalIdeal K I
    let d := b.traceDual
    have hb (i : _) : archimedeanEuclideanEmbedding K (b i) ∈ archimedeanIdealLattice K I :=
      (mem_archimedeanIdealLattice K I _).2 ⟨b i,
        (mem_span_basisOfFractionalIdeal K).1 (Submodule.subset_span ⟨i, rfl⟩), rfl⟩
    choose n hn using fun i ↦ hv _ (hb i)
    let y : K := ∑ i, (n i : ℚ) • d i
    have hy : y ∈ FractionalIdeal.dual ℤ ℚ I.val := by
      change y ∈ (FractionalIdeal.dual ℤ ℚ I.val : Submodule (𝓞 K) K).restrictScalars ℤ
      rw [FractionalIdeal.coeToSubmodule_dual ℤ ℚ I.ne_zero,
        Submodule.traceDual_span_of_basis ℤ _ b]
      · exact (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨n, by
          simp [y, d, Rat.smul_def, zsmul_eq_mul]⟩
      · ext x
        exact (mem_span_basisOfFractionalIdeal K).symm
    refine ⟨y, hy, ?_⟩
    -- The embedded rational basis is a real basis; the inner products determine `v`.
    apply InnerProductSpace.ext_inner_left_basis
      ((mixedEmbedding.fractionalIdealLatticeBasis K I).map (coords).symm.toLinearEquiv)
    intro i
    simp only [Module.Basis.map_apply, mixedEmbedding.fractionalIdealLatticeBasis_apply]
    change ⟪archimedeanEuclideanEmbedding K (b i), _⟫_ℝ =
      ⟪archimedeanEuclideanEmbedding K (b i), v⟫_ℝ
    rw [inner_archimedeanEuclideanEmbedding_traceFrequency, hn i, mul_comm (b i) y,
      ← Algebra.traceForm_apply, ← LinearMap.BilinForm.dualBasis_repr_apply
        (traceForm_nondegenerate ℚ K) b]
    change (d.repr y i : ℝ) = _
    rw [Module.Basis.repr_sum_self]
    exact Rat.cast_intCast _
  · rintro ⟨y, hy, rfl⟩ u hu
    obtain ⟨x, hx, rfl⟩ := (mem_archimedeanIdealLattice K I u).1 hu
    obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual I.ne_zero).1 hy x hx
    refine ⟨n, ?_⟩
    rw [inner_archimedeanEuclideanEmbedding_traceFrequency, mul_comm x y,
      ← Algebra.traceForm_apply, ← hn]
    exact Rat.cast_intCast _

/-- The Poisson covolume for ordinary Euclidean Lebesgue measure. -/
public theorem covolume_archimedeanIdealLattice (I : Fracˣ) :
    ZLattice.covolume (archimedeanIdealLattice K I) =
      (FractionalIdeal.absNorm I.val : ℝ) * (2⁻¹) ^ nrComplexPlaces K * √|discr K| := by
  rw [archimedeanIdealLattice, ZLattice.covolume_comap _ _ _
    (mixedEmbedding.euclidean.volumePreserving_toMixed K), mixedEmbedding.covolume_idealLattice]

/-- The measure with `dx` at each real place and `2 dx dy` at each complex place. -/
@[expose] public def archimedeanTraceMeasure : Measure Eucl :=
  (2 : ℝ≥0∞) ^ nrComplexPlaces K • (volume : Measure Eucl)

/-- In the additive trace normalization the powers of two in the covolume cancel. -/
public theorem covolume_archimedeanIdealLattice_traceMeasure (I : Fracˣ) :
    ZLattice.covolume (archimedeanIdealLattice K I) (archimedeanTraceMeasure K) =
      (FractionalIdeal.absNorm I.val : ℝ) * √|discr K| := by
  have hμ : (archimedeanTraceMeasure K).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume (by simp) (by finiteness)
  let b := Module.Free.chooseBasis ℤ (archimedeanIdealLattice K I)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZLattice.isAddFundamentalDomain b _),
    archimedeanTraceMeasure, measureReal_ennreal_smul_apply,
    ← ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZLattice.isAddFundamentalDomain b volume),
    covolume_archimedeanIdealLattice, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  rw [← mul_assoc, mul_left_comm, mul_assoc, ← mul_pow]
  norm_num

end

end Masullo
