module

public import Theorems.ArchimedeanHaarCoordinates
public import Theorems.ArchimedeanTorsionOrbit

/-!
# Angular mass of the torsion slice

Definition A.2.3.6, (A.2.3.13), p. 549, restricts the angle at one place
and leaves the others alone. We compute in the checked angular product
measure for (A.3.2.5), p. 560, the angular factor of the normalization
(A.3.2.1), pp. 559–560. Source reading: Pinned Markdown and numbered PDF
text, not rendered pages.
-/

open MeasureTheory NumberField Set
open InfinitePlace.Completion
open scoped Classical ENNReal

namespace Masullo

variable {K : Type*} [Field K]

private noncomputable def realChart (v : InfinitePlace K) (hv : v.IsReal) :
    AngularChart v.Completionˣ :=
  ⟨Bool, inferInstance, Measure.count,
    fun u ↦ if 0 < extensionEmbeddingOfIsReal hv u.val then true else false, inferInstance⟩

private noncomputable def complexChart (v : InfinitePlace K) : AngularChart v.Completionˣ :=
  ⟨ℝ, inferInstance, volume.restrict (Ioo (-Real.pi) Real.pi),
    fun u ↦ Complex.arg (extensionEmbedding v u.val), inferInstance⟩

private theorem eq_realChart (v : InfinitePlace K) (hv : v.IsReal) :
    archimedeanAngularChart v = realChart v hv := by
  rw [archimedeanAngularChart, dite_eq_left hv, realChart]

private theorem eq_complexChart (v : InfinitePlace K) (hv : ¬v.IsReal) :
    archimedeanAngularChart v = complexChart v := by
  rw [archimedeanAngularChart, dite_eq_right hv, complexChart]

private noncomputable def angularTorsionSector (v : InfinitePlace K) :
    Set (ArchimedeanAngle v) :=
  if hv : v.IsReal then cast (congrArg (fun c ↦ Set c.Angle) (eq_realChart v hv).symm)
    ({true} : Set (realChart v hv).Angle)
  else cast (congrArg (fun c ↦ Set c.Angle) (eq_complexChart v hv).symm)
    (Ico (0 : ℝ) (2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ)) : Set ℝ)

-- Rewrite the chart and its sector together, since the type of angles changes.
private theorem angularTorsionSector_cases (v : InfinitePlace K)
    (P : (c : AngularChart v.Completionˣ) → Set c.Angle → Prop)
    (hr : ∀ hv : v.IsReal, P (realChart v hv) {true})
    (hc : ¬v.IsReal → P (complexChart v)
      (Ico (0 : ℝ) (2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ)) : Set ℝ)) :
    P (archimedeanAngularChart v) (angularTorsionSector v) := by
  have transport {a b : AngularChart v.Completionˣ} (e : a = b) (s : Set a.Angle) :
      P a s → P b (cast (congrArg (fun c ↦ Set c.Angle) e) s) := by
    cases e
    exact id
  by_cases hv : v.IsReal
  · unfold angularTorsionSector
    rw [dite_eq_left hv]
    exact transport (eq_realChart v hv).symm _ (hr hv)
  · unfold angularTorsionSector
    rw [dite_eq_right hv]
    exact transport (eq_complexChart v hv).symm _ (hc hv)

/-- The angular cylinder of (A.2.3.13): Fix the positive sign at a real
place or the half-open sector of width `2π / w_F` at a complex place. -/
public noncomputable def archimedeanAngularTorsionSlice (v : InfinitePlace K) :
    Set ((w : InfinitePlace K) → ArchimedeanAngle w) :=
  Function.eval v ⁻¹' angularTorsionSector v

/-- On actual completion units, the angular cylinder imposes exactly the
local sign or principal-argument condition, even on the branch ray. -/
public theorem mem_archimedeanAngularTorsionSlice_iff (v : InfinitePlace K)
    (u : (w : InfinitePlace K) → w.Completionˣ) :
    (fun w ↦ archimedeanAngle w (u w)) ∈ archimedeanAngularTorsionSlice v ↔
      if hv : v.IsReal then 0 < extensionEmbeddingOfIsReal hv (u v).val
      else Complex.arg (extensionEmbedding v (u v).val) ∈
        Ico 0 (2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ)) := by
  change (archimedeanAngularChart v).coord (u v) ∈ angularTorsionSector v ↔ _
  refine angularTorsionSector_cases v (fun c s ↦ c.coord (u v) ∈ s ↔ _) ?_ ?_
  · intro hv
    rw [dite_eq_left hv]
    change (if 0 < extensionEmbeddingOfIsReal hv (u v).val then true else false) ∈
      ({true} : Set Bool) ↔ _
    simp
  · intro hv
    rw [dite_eq_right hv]
    rfl

public theorem measurableSet_archimedeanAngularTorsionSlice (v : InfinitePlace K) :
    MeasurableSet (archimedeanAngularTorsionSlice v) := by
  apply MeasurableSet.preimage _ (measurable_pi_apply v)
  refine angularTorsionSector_cases v (fun c s ↦ @MeasurableSet _ c.space s) ?_ ?_
  · exact fun _ ↦ measurableSet_singleton true
  · exact fun _ ↦ (measurableSet_Ico : MeasurableSet (Ico (0 : ℝ)
    (2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ))))

variable [NumberField K]

private theorem angularTorsionSector_mass (v : InfinitePlace K) :
    archimedeanAngularMeasure v (angularTorsionSector v) =
      archimedeanAngularMeasure v univ / (NumberField.Units.torsionOrder K : ℝ≥0∞) := by
  refine angularTorsionSector_cases v (fun c s ↦
    c.measure s = c.measure univ / (NumberField.Units.torsionOrder K : ℝ≥0∞)) ?_ ?_
  · intro hv
    change (Measure.count : Measure Bool) {true} = Measure.count univ / _
    rw [InfinitePlace.torsionOrder_eq_two_of_isReal hv, Measure.count_singleton, Measure.count_univ, ENat.card_eq_coe_fintype_card]
    norm_num [ENNReal.div_self]
  · intro _
    have hn : 0 < (NumberField.Units.torsionOrder K : ℝ) :=
      Nat.cast_pos.mpr (NumberField.Units.torsionOrder_pos K)
    have htwo : (2 : ℝ) ≤ (NumberField.Units.torsionOrder K : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NumberField.Units.torsionOrder_pos K)
        (NumberField.Units.even_torsionOrder K).two_dvd
    have hi : Ico 0 (2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ)) ⊆
        Ioo (-Real.pi) Real.pi := by
      have hb : 2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ) ≤ Real.pi := by
        rw [div_le_iff₀ hn]
        nlinarith [Real.pi_pos]
      exact fun x hx ↦ ⟨lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_pos) hx.1, hx.2.trans_le hb⟩
    let μ := (volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi)
    change μ (Ico 0 (2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ))) = μ univ / _
    dsimp only [μ]
    rw [Measure.restrict_apply measurableSet_Ico, inter_eq_left.mpr hi, Measure.restrict_apply_univ,
      Real.volume_Ico, Real.volume_Ioo, sub_zero, sub_neg_eq_add, ← two_mul,
      ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_natCast]

/-- The cylinder has exactly `1 / w_F` of the full angular mass. Count
one rather than one-half for the selected real sign, and take the length
of the selected complex interval. The unselected factors are unchanged. -/
public theorem measure_archimedeanAngularTorsionSlice (v : InfinitePlace K) :
    (Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w)
        (archimedeanAngularTorsionSlice v) =
      (Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w) univ /
        (NumberField.Units.torsionOrder K : ℝ≥0∞) := by
  rw [archimedeanAngularTorsionSlice, ← Set.univ_pi_update_univ, Measure.pi_pi, Measure.pi_univ]
  let f (w : InfinitePlace K) := archimedeanAngularMeasure w
    (Function.update (fun _ ↦ univ) v (angularTorsionSector v) w)
  let t (w : InfinitePlace K) := archimedeanAngularMeasure w univ
  -- Split off the selected place and retain the measure of every other factor.
  change ∏ w, f w = (∏ w, t w) / _
  rw [← Finset.prod_erase_mul _ f (Finset.mem_univ v),
    ← Finset.prod_erase_mul _ t (Finset.mem_univ v)]
  have hprod : ∏ w ∈ Finset.univ.erase v, f w = ∏ w ∈ Finset.univ.erase v, t w := by
    apply Finset.prod_congr rfl
    intro w hw
    simp only [f, t, Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  have hlocal : f v = t v / (NumberField.Units.torsionOrder K : ℝ≥0∞) := by
    simpa only [f, t, Function.update_self] using angularTorsionSector_mass v
  rw [hprod, hlocal, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

/-- The measured angular cylinder imposes the same condition on the
norm-one Archimedean group as the pointwise torsion-orbit theorem. -/
public theorem archimedeanInTorsionSector_iff_angularTorsionSlice (v : InfinitePlace K)
    (g : archimedeanNormOne (K := K)) :
    archimedeanInTorsionSector v g ↔
    (fun w ↦ archimedeanAngle w (ContinuousMulEquiv.piUnits
      (g : (InfiniteAdeleRing K)ˣ) w)) ∈ archimedeanAngularTorsionSlice v :=
  (mem_archimedeanAngularTorsionSlice_iff v
    (ContinuousMulEquiv.piUnits (g : (InfiniteAdeleRing K)ˣ))).symm

end Masullo
