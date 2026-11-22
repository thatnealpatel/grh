module

public import Lemmas.LatticeFrequency
public import Lemmas.LatticePeriodizationCoefficient
public import Lemmas.LatticeSchwartzPeriodization
public import Theorems.ArchimedeanIdealDual

/-! # Shifted Poisson summation for fractional-ideal lattices

On PDF p. 82, Theorem 2.2.3.2 invokes adelic Riemann–Roch; Remark 2.2.3.3
normalizes the additive adelic quotient to mass one (provisional reading of
pinned Markdown and PDF text). Neither passage gives the shifted Euclidean
identity needed to treat finite support cosets by a lattice proof.

We prove that input here: periodize on the basis torus, unfold its normalized
coefficient integral, and reconstruct at the shift. The reciprocal covolume
comes from ordinary Euclidean volume in `mFourierCoeff_latticePeriodization`.
The already checked ambient dual bridge then identifies the frequencies with
the trace dual of the fractional ideal. This is not yet adelic inversion:
the finite character and Haar factors still have to be matched.
-/

open MeasureTheory Module NumberField
open scoped Classical FourierTransform InnerProductSpace SchwartzMap nonZeroDivisors

namespace Masullo

noncomputable section

section Lattice

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Shifted Poisson summation on a full Euclidean lattice. The measure in the covolume
and in the Fourier integral is ordinary Euclidean volume. Both series include zero. -/
public theorem schwartz_lattice_poisson (b : Basis ι ℤ L) (φ : 𝓢(E, ℂ)) (a : E) :
    let p (u : L) := φ (a + u)
    let q (v : latticeEuclideanDual b) :=
      Complex.exp ((↑(2 * Real.pi * ⟪a, (v : E)⟫_ℝ) : ℂ) * Complex.I) * 𝓕 (⇑φ) v
    Summable (fun u ↦ ‖p u‖) ∧ Summable (fun v ↦ ‖q v‖) ∧
      ∑' u, p u = ((↑(ZLattice.covolume L volume) : ℂ)⁻¹) * ∑' v, q v := by
  -- Periodize in real basis coordinates and unfold the torus coefficients.
  let F := latticeSchwartzPeriodization L b φ
  let e := latticeEuclideanDualIndex b
  let c := ((↑(ZLattice.covolume L volume) : ℂ)⁻¹)
  have hCoeff (n : ι → ℤ) : UnitAddTorus.mFourierCoeff F n = c * 𝓕 (⇑φ) (e n : E) :=
    mFourierCoeff_latticePeriodization b φ F (latticeSchwartzPeriodization_apply L b φ)
      n (e n) (inner_latticeEuclideanDualIndex b n)
  -- Schwartz decay on the full dual lattice makes its Fourier samples absolutely summable.
  have hDual : Summable (fun v : latticeEuclideanDual b ↦ ‖𝓕 (⇑φ) (v : E)‖) := by
    simpa only [zero_add, SchwartzMap.fourier_coe] using
      summable_norm_schwartz_lattice_add (latticeEuclideanDual b) (𝓕 φ) 0
  have hSeries : Summable (UnitAddTorus.mFourierCoeff F) := by
    refine Summable.of_norm ?_
    simp_rw [hCoeff, norm_mul]
    exact (e.summable_iff.2 hDual).mul_left ‖c‖
  -- Reconstruct at the shift; the reconstruction character has the positive phase.
  let t : UnitAddTorus ι := fun i ↦ ((b.ofZLatticeBasis ℝ).repr a i : UnitAddCircle)
  have hPhase (n : ι → ℤ) : UnitAddTorus.mFourier n t =
      Complex.exp ((↑(2 * Real.pi * ⟪a, (e n : E)⟫_ℝ) : ℂ) * Complex.I) :=
    mFourier_eq_exp_inner b n (e n) (inner_latticeEuclideanDualIndex b n) a
  dsimp only
  refine ⟨summable_norm_schwartz_lattice_add L φ a, ?_, ?_⟩
  · simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] using hDual
  · calc
      ∑' u : L, φ (a + u) = F t := (latticeSchwartzPeriodization_apply L b φ a).symm
      _ = ∑' n, UnitAddTorus.mFourierCoeff F n • UnitAddTorus.mFourier n t :=
        (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hSeries t).tsum_eq.symm
      _ = c * ∑' n : ι → ℤ,
          Complex.exp ((↑(2 * Real.pi * ⟪a, (e n : E)⟫_ℝ) : ℂ) * Complex.I) * 𝓕 (⇑φ) (e n : E) := by
        simp_rw [hCoeff, hPhase, smul_eq_mul, mul_assoc, mul_comm (𝓕 (⇑φ) (e _ : E))]
        rw [tsum_mul_left]
      _ = _ := congrArg (c * ·) (e.tsum_eq (fun v : latticeEuclideanDual b ↦
        Complex.exp ((↑(2 * Real.pi * ⟪a, (v : E)⟫_ℝ) : ℂ) * Complex.I) * 𝓕 (⇑φ) (v : E)))

end Lattice

section NumberField

variable (K : Type*) [Field K] [NumberField K]

local notation "Eucl" => mixedEmbedding.euclidean.mixedSpace K
local notation "Frac" => FractionalIdeal (𝓞 K)⁰ K

private theorem traceFrequency_injective : Function.Injective (archimedeanTraceFrequency K) := by
  intro x y h
  have h' := (mixedEmbedding.euclidean.toMixed K).symm.injective h
  have h₁ := congrArg Prod.fst h'
  have h₂ := congrArg Prod.snd h'
  apply (mixedEmbedding.euclidean.toMixed K).injective
  refine Prod.ext h₁ (funext fun w ↦ ?_)
  apply star_injective
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (congrFun h₂ w)

private theorem traceEmbedding_injective :
    Function.Injective (archimedeanTraceFrequency K ∘ archimedeanEuclideanEmbedding K) :=
  (traceFrequency_injective K).comp
    ((mixedEmbedding.euclidean.toMixed K).symm.injective.comp (mixedEmbedding_injective K))

/-- Shifted ordinary-volume Poisson summation for a nonzero fractional ideal of any number
field. The dual series uses every element of the rational trace dual at its actual Euclidean
trace frequency. In particular, neither series has its zero term removed. -/
public theorem archimedeanIdeal_poisson (I : Fracˣ) (φ : 𝓢(Eucl, ℂ)) (a : Eucl) :
    let p (u : archimedeanIdealLattice K I) := φ (a + u)
    let q (y : ↥(FractionalIdeal.dual ℤ ℚ I.val)) :=
      let v := archimedeanTraceFrequency K (archimedeanEuclideanEmbedding K y)
      Complex.exp ((↑(2 * Real.pi * ⟪a, v⟫_ℝ) : ℂ) * Complex.I) * 𝓕 (⇑φ) v
    Summable (fun u ↦ ‖p u‖) ∧ Summable (fun y ↦ ‖q y‖) ∧
      ∑' u, p u = ((↑(ZLattice.covolume (archimedeanIdealLattice K I) volume) : ℂ)⁻¹) * ∑' y, q y := by
  let L := archimedeanIdealLattice K I
  let b := Module.Free.chooseBasis ℤ L
  let e₀ (y : ↥(FractionalIdeal.dual ℤ ℚ I.val)) : latticeEuclideanDual b :=
    ⟨archimedeanTraceFrequency K (archimedeanEuclideanEmbedding K y),
      (mem_latticeEuclideanDual b _).2 ((mem_archimedeanIdealLattice_euclideanDual K I _).2
        ⟨y, y.property, rfl⟩)⟩
  -- The checked trace-dual bridge gives all ambient frequencies; injectivity rules out
  -- repetitions when the reconstructed Fourier series is reindexed by field elements.
  let e := Equiv.ofBijective e₀ ⟨fun _ _ h ↦
      Subtype.ext (traceEmbedding_injective K (congrArg Subtype.val h)), fun v ↦ by
    obtain ⟨y, hy, hv⟩ := (mem_archimedeanIdealLattice_euclideanDual K I v).1
      ((mem_latticeEuclideanDual b v).1 v.property)
    exact ⟨⟨y, hy⟩, Subtype.ext hv⟩⟩
  obtain ⟨hp, hq, hP⟩ := schwartz_lattice_poisson L b φ a
  dsimp only
  exact ⟨hp, e.summable_iff.2 hq, hP.trans (congrArg (_ * ·) (e.tsum_eq _).symm)⟩

end NumberField

end

end Masullo
