module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Fourier coefficients of lattice periodizations

The unit torus has Haar probability measure. Pulling its coefficient integral back to a basis
fundamental domain introduces the reciprocal of the lattice covolume, with respect to the same
volume as the Euclidean Fourier transform. This is an unfolding argument for the lattice
step towards shifted Schwartz Poisson summation (Masullo, p. 82, Theorem 2.2.3.2 and
Remark 2.2.3.3).
-/

open MeasureTheory Set
open scoped ENNReal FourierTransform InnerProductSpace SchwartzMap

namespace Masullo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι]

/-- The torus monomial is the positive Euclidean phase at the corresponding dual vector. -/
public theorem mFourier_eq_exp_inner (b : Module.Basis ι ℤ L) (n : ι → ℤ) (v : E)
    (hv : ∀ i, ⟪(b i : E), v⟫_ℝ = (n i : ℝ)) (x : E) :
    UnitAddTorus.mFourier n (fun i ↦ ((b.ofZLatticeBasis ℝ).repr x i : UnitAddCircle)) =
      Complex.exp ((↑(2 * Real.pi * ⟪x, v⟫_ℝ) : ℂ) * Complex.I) := by
  classical
  let B := b.ofZLatticeBasis ℝ
  change UnitAddTorus.mFourier n (fun i ↦ (B.repr x i : UnitAddCircle)) = _
  have hinner : ⟪x, v⟫_ℝ = ∑ i, B.repr x i * (n i : ℝ) := by
    calc
      ⟪x, v⟫_ℝ = ⟪∑ i, B.repr x i • B i, v⟫_ℝ := by rw [B.sum_repr]
      _ = _ := by simp [B, sum_inner, real_inner_smul_left, hv]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one, ← Complex.exp_sum, hinner, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_intCast, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype ι] in
private theorem lattice_torus_translate (b : Module.Basis ι ℤ L) (x : E) (u : L) :
    (fun i ↦ ((b.ofZLatticeBasis ℝ).repr (x + u) i : UnitAddCircle)) =
      (fun i ↦ ((b.ofZLatticeBasis ℝ).repr x i : UnitAddCircle)) := by
  funext i
  rw [map_add, Finsupp.add_apply, AddCircle.coe_add, b.ofZLatticeBasis_repr_apply ℝ L]
  have hz : (((b.repr u i : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨b.repr u i, by simp [zsmul_eq_mul]⟩
  rw [hz, add_zero]

variable [MeasurableSpace E] [BorelSpace E]

/-- Under the basis coordinates, ambient volume becomes covolume times coordinate volume.
Calibrate the scalar on the unit box and then replace `Ico` with `Ioc` off the null boundary. -/
private theorem integral_lattice_basis (b : Module.Basis ι ℤ L) (g : (ι → ℝ) → ℂ) :
    (∫ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ),
      g (fun i ↦ (b.ofZLatticeBasis ℝ).repr x i)) =
      (↑(ZLattice.covolume L volume) : ℂ) *
        ∫ y in {y : ι → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1}, g y := by
  classical
  let B := b.ofZLatticeBasis ℝ
  let e : E ≃L[ℝ] (ι → ℝ) := B.equivFun.toContinuousLinearEquiv
  have he : ∀ x, e x = ⇑(B.repr x) := B.equivFun_apply
  let s := Set.pi (Set.univ : Set ι) (fun _ ↦ Ico (0 : ℝ) 1)
  have hs : MeasurableSet s := MeasurableSet.pi countable_univ (fun _ _ ↦ measurableSet_Ico)
  have hpre : e ⁻¹' s = ZSpan.fundamentalDomain B := by
    ext x
    simp [s, he, ZSpan.mem_fundamentalDomain]
  let μ : Measure (ι → ℝ) := Measure.map e (volume : Measure E)
  have : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let c := μ.addHaarScalarFactor (volume : Measure (ι → ℝ))
  have hμ : μ = c • (volume : Measure (ι → ℝ)) :=
    Measure.isAddLeftInvariant_eq_smul μ volume
  have hbox : (volume : Measure (ι → ℝ)) s = 1 := by
    simp [s, volume_pi_pi, Real.volume_Ico]
  have hc : (c : ℝ) = ZLattice.covolume L volume := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume), measureReal_def, ← hpre,
      ← Measure.map_apply e.continuous.measurable hs]
    change (c : ℝ) = (μ s).toReal
    rw [hμ, smul_apply, hbox, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]
  have hboundary : s =ᵐ[(volume : Measure (ι → ℝ))]
      {y : ι → ℝ | ∀ i, y i ∈ Ioc (0 : ℝ) 1} := by
    rw [volume_pi]
    change s =ᵐ[Measure.pi (fun _ : ι ↦ volume)] _
    have h := (Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ : ι ↦ (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ ↦ 0) (g := fun _ ↦ 1)).trans
      (Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : ι ↦ (volume : Measure ℝ))).symm
    simpa [s, Set.pi] using h
  let ee := e.toHomeomorph.toMeasurableEquiv
  calc
    (∫ x in ZSpan.fundamentalDomain B, g (fun i ↦ B.repr x i)) =
        ∫ y in s, g y ∂μ := by
      rw [show μ = Measure.map ee (volume : Measure E) from rfl, ee.restrict_map,
        ee.measurableEmbedding.integral_map]
      change (∫ x in ZSpan.fundamentalDomain B, g (fun i ↦ B.repr x i)) =
        ∫ x in e ⁻¹' s, g (e x)
      simp only [hpre, he]
    _ = _ := by
      rw [hμ, Measure.restrict_smul, integral_smul_nnreal_measure,
        Measure.restrict_congr_set hboundary, ← hc]
      rfl

/-- A full lattice periodization has coefficient equal to the ambient Fourier transform at the
corresponding dual vector, divided by the covolume. The absolute integral needed for unfolding
comes from the Schwartz function's global `L¹` bound; no separate convergence hypothesis is used. -/
public theorem mFourierCoeff_latticePeriodization (b : Module.Basis ι ℤ L) (φ : 𝓢(E, ℂ))
    (F : UnitAddTorus ι → ℂ)
    (hF : ∀ x : E, F (fun i ↦ ((b.ofZLatticeBasis ℝ).repr x i : UnitAddCircle)) =
      ∑' u : L, φ (x + u))
    (n : ι → ℤ) (v : E) (hv : ∀ i, ⟪(b i : E), v⟫_ℝ = (n i : ℝ)) :
    UnitAddTorus.mFourierCoeff F n = (↑(ZLattice.covolume L volume) : ℂ)⁻¹ * 𝓕 (⇑φ) v := by
  classical
  let q : E → UnitAddTorus ι := fun x i ↦ ((b.ofZLatticeBasis ℝ).repr x i : UnitAddCircle)
  let g : (ι → ℝ) → ℂ := fun y ↦ UnitAddTorus.mFourier (-n) (fun i ↦ y i) • F (fun i ↦ y i)
  let f : E → ℂ := fun x ↦ 𝐞 (-⟪x, v⟫_ℝ) • φ x
  have hf : Integrable f volume := (Real.fourierIntegral_convergent_iff v).mpr φ.integrable
  let D := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have hD : IsAddFundamentalDomain L D (volume : Measure E) :=
    ZLattice.isAddFundamentalDomain b volume
  have hcoeff := UnitAddTorus.mFourierCoeff_eq_integral F n 0
  simp only [Pi.zero_apply, zero_add] at hcoeff
  have hbox := integral_lattice_basis b g
  rw [← hcoeff] at hbox
  have hphase (x : E) : UnitAddTorus.mFourier (-n) (q x) =
      (𝐞 (-⟪x, v⟫_ℝ) : ℂ) := by
    have hv' (i : ι) : ⟪(b i : E), -v⟫_ℝ = ((-n) i : ℝ) := by
      simp [hv]
    rw [mFourier_eq_exp_inner b (-n) (-v) hv' x, Real.fourierChar_apply, inner_neg_right]
  have hunfold (x : E) : g (fun i ↦ (b.ofZLatticeBasis ℝ).repr x i) =
      ∑' u : L, f ((u : E) + x) := by
    change UnitAddTorus.mFourier (-n) (q x) • F (q x) = _
    rw [hF x, smul_eq_mul, ← tsum_mul_left]
    refine tsum_congr fun u ↦ ?_
    rw [add_comm (u : E) x]
    change UnitAddTorus.mFourier (-n) (q x) * φ (x + u) =
      (𝐞 (-⟪x + u, v⟫_ℝ) : ℂ) * φ (x + u)
    rw [← hphase, show q (x + u) = q x from lattice_torus_translate b x u]
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E (volume : Measure E) :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  have hsum : (∫ x in D, ∑' u : L, f ((u : E) + x)) = 𝓕 (⇑φ) v := by
    change (∫ x in D, ∑' u : L, f (u +ᵥ x)) = ∫ x, f x
    rw [hD.integral_eq_tsum'' f hf]
    apply integral_tsum
    · intro u
      exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (measurePreserving_vadd u (volume : Measure E)).quasiMeasurePreserving).restrict
    · -- Unfold the nonnegative norm first; this is the absolute integral bound for `integral_tsum`.
      rw [← hD.lintegral_eq_tsum'' (fun x ↦ ‖f x‖ₑ)]
      exact hf.2.ne
  have hscaled : 𝓕 (⇑φ) v = (↑(ZLattice.covolume L volume) : ℂ) *
      UnitAddTorus.mFourierCoeff F n := by
    refine hsum.symm.trans ?_
    simpa only [hunfold] using hbox
  have hne : (↑(ZLattice.covolume L volume) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ZLattice.covolume_ne_zero L volume)
  rw [hscaled, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Masullo
