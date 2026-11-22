module

public import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Set
namespace Masullo

/-- Rearrange a finite product of measures on dependent pairs. -/
public theorem measurePreserving_piProd (ι : Type*) [Fintype ι] (X Y : ι → Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : (i : ι) → Measure (X i)) (ν : (i : ι) → Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (fun p : (i : ι) → X i × Y i ↦ (fun i ↦ (p i).1, fun i ↦ (p i).2))
      (Measure.pi fun i ↦ (μ i).prod (ν i)) ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (measurable_pi_iff.mpr fun i ↦ measurable_fst.comp (measurable_pi_apply i)).prodMk
    (measurable_pi_iff.mpr fun i ↦ measurable_snd.comp (measurable_pi_apply i))
  map_eq := by
    refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (Measure.FiniteSpanningSetsIn.pi fun i ↦ (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (Measure.FiniteSpanningSetsIn.pi fun i ↦ (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, hs, rfl⟩, ⟨_, ⟨t, ht, rfl⟩, rfl⟩⟩
      have h : Measurable
          (fun p : (i : ι) → X i × Y i ↦ (fun i ↦ (p i).1, fun i ↦ (p i).2)) :=
        (measurable_pi_iff.mpr fun i ↦ measurable_fst.comp (measurable_pi_apply i)).prodMk
          (measurable_pi_iff.mpr fun i ↦ measurable_snd.comp (measurable_pi_apply i))
      rw [Measure.map_apply h
        ((MeasurableSet.univ_pi fun i ↦ hs i (mem_univ i)).prod
          (MeasurableSet.univ_pi fun i ↦ ht i (mem_univ i)))]
      rw [show (fun p : (i : ι) → X i × Y i ↦ (fun i ↦ (p i).1, fun i ↦ (p i).2)) ⁻¹'
          (univ.pi s ×ˢ univ.pi t) = univ.pi (fun i ↦ s i ×ˢ t i) by
        ext; simp [forall_and]]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

end Masullo
