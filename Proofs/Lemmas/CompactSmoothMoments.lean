module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Moment functionals on compactly supported smooth real tests

Weights need only be continuous on the test domain. A product with a test is
continuous on the whole line because it is locally zero off the test support.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Masullo

/-- Multiplying an interior compactly supported continuous test by a locally
continuous weight gives an integrable product on the whole line. -/
public theorem integrable_mul_of_tsupport_subset {I : Set ℝ} (hI : IsOpen I)
    {f w : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ I) (hw : ContinuousOn w I) :
    Integrable (fun x ↦ f x * w x) :=
  ((hf.continuousOn.mul hw).continuous_of_tsupport_subset hI
    (tsupport_mul_subset_left.trans hfs)).integrable_of_hasCompactSupport hfc.mul_right

private def interiorSmoothTests (I : Set ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ I}
  zero_mem' := ⟨contDiff_const (c := (0 : ℝ)), HasCompactSupport.zero, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfc, hfs⟩ ⟨hg, hgc, hgs⟩
    refine ⟨hf.add hg, hfc.add hgc, ?_⟩
    exact (tsupport_binop_subset (· + ·) (zero_add (0 : ℝ)) f g).trans (union_subset hfs hgs)
  smul_mem' := by
    rintro c f ⟨hf, hfc, hfs⟩
    exact ⟨hf.const_smul c, hfc.smul_left, (tsupport_smul_subset_right (fun _ ↦ c) f).trans hfs⟩

private noncomputable def interiorMoment {I : Set ℝ} (hI : IsOpen I)
    {w : ℝ → ℝ} (hw : ContinuousOn w I) : interiorSmoothTests I →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f.val x * w x
  map_add' f g := by
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add
      (integrable_mul_of_tsupport_subset hI f.2.1.continuous f.2.2.1 f.2.2.2 hw)
      (integrable_mul_of_tsupport_subset hI g.2.1.continuous g.2.2.1 g.2.2.2 hw)
  map_smul' c f := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply,
      integral_const_mul]

/-- If the target moment vanishes on the common kernel of finitely many
moments, it is a linear combination of those moments on the test space. -/
public theorem compactSmooth_moment_relation {ι : Type*} [Fintype ι]
    {I : Set ℝ} (hI : IsOpen I) {w : ι → ℝ → ℝ} {u : ℝ → ℝ}
    (hw : ∀ i, ContinuousOn (w i) I) (hu : ContinuousOn u I)
    (h : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ I →
      (∀ i, (∫ x, f x * w i x) = 0) → (∫ x, f x * u x) = 0) :
    ∃ c : ι → ℝ, ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ I →
      (∫ x, f x * u x) = ∑ i, c i * (∫ x, f x * w i x) := by
  let L i := interiorMoment hI (hw i)
  let K := interiorMoment hI hu
  have hk : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker K := by
    intro f hf
    rw [Submodule.mem_iInf] at hf
    exact LinearMap.mem_ker.mpr (h f.val f.2.1 f.2.2.1 f.2.2.2
      fun i ↦ LinearMap.mem_ker.mp (hf i))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (mem_span_of_iInf_ker_le_ker hk)
  refine ⟨c, fun f hd hcpt hs ↦ ?_⟩
  let g : interiorSmoothTests I := ⟨f, hd, hcpt, hs⟩
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, L, K, interiorMoment,
    LinearMap.coe_mk, AddHom.coe_mk, g] using congrArg (fun (l : interiorSmoothTests I →ₗ[ℝ] ℝ) ↦ l g) hc.symm

/-- A continuous density on an open real set is determined pointwise there by
its integrals against smooth tests with compact support inside the set. -/
public theorem eqOn_of_compactSmooth_moments_eq {I : Set ℝ} (hI : IsOpen I)
    {u v : ℝ → ℝ} (hu : ContinuousOn u I) (hv : ContinuousOn v I)
    (h : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ I →
      (∫ x, f x * u x) = ∫ x, f x * v x) : EqOn u v I := by
  have hz := hI.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hu.sub hv).locallyIntegrableOn (μ := volume) hI.measurableSet) (fun f hf hfc hfs ↦ by
      simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
      rw [integral_sub (integrable_mul_of_tsupport_subset hI hf.continuous hfc hfs hu)
        (integrable_mul_of_tsupport_subset hI hf.continuous hfc hfs hv), h f hf hfc hfs, sub_self])
  apply volume.eqOn_open_of_ae_eq _ hI hu hv
  rw [Filter.EventuallyEq, ae_restrict_iff' hI.measurableSet]
  simpa only [Pi.sub_apply, sub_eq_zero] using hz

end Masullo
