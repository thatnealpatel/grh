module

public import Lemmas.RealMultiplicativeDensity
import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Group.Units
import Theorems.RealMultiplicativeMeasure

/-!
# Multiplicative Haar at the real place

Definition A.3.2.2(1), p. 560, uses `dt / |t|` on the entire real unit
group. In particular the negative component is not discarded or folded
into the positive component. The window calibration uses the positive
strip `[1, e]` only, as in the rational window of A.3.3.1, p. 561.
-/

open MeasureTheory Set

namespace Masullo

private theorem range_realUnits_val : range (Units.val : ℝˣ → ℝ) = ({0} : Set ℝ)ᶜ := by
  ext t
  exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ Units.ne_zero u, fun ht ↦ ⟨Units.mk0 t ht, rfl⟩⟩

/-- Mathlib's measurable space on real units is the Borel sigma-algebra. -/
public instance realUnitsBorelSpace : BorelSpace ℝˣ where
  measurable_eq := by
    change MeasurableSpace.comap (Units.val : ℝˣ → ℝ) _ = borel ℝˣ
    rw [BorelSpace.measurable_eq (α := ℝ), ← borel_comap,
      ← (Units.isOpenEmbedding_val (R := ℝ)).isInducing.eq_induced]

/-- The full real local multiplicative measure of Definition A.3.2.2(1). -/
public noncomputable def realMultiplicativeHaar : Measure ℝˣ :=
  realMultiplicativeDensity.comap Units.val

/-- In the real value coordinate the Haar measure is `dt / |t|` off zero,
with both signs retained. -/
public theorem map_realMultiplicativeHaar_val :
    realMultiplicativeHaar.map Units.val =
      (((volume : Measure ℝ).restrict ({0}ᶜ)).withDensity (fun t ↦ ENNReal.ofReal |t|⁻¹)) := by
  rw [realMultiplicativeHaar, Units.isOpenEmbedding_val.measurableEmbedding.map_comap,
    range_realUnits_val, realMultiplicativeDensity, restrict_withDensity (measurableSet_singleton 0).compl,
    Measure.restrict_restrict (measurableSet_singleton 0).compl, inter_self]

/-- The positive strip calibrating the real local Haar measure has mass one. -/
public theorem realMultiplicativeHaar_unitStrip :
    realMultiplicativeHaar (Units.val ⁻¹' Icc 1 (Real.exp 1)) = 1 := by
  rw [← Measure.map_apply Units.isOpenEmbedding_val.measurableEmbedding.measurable measurableSet_Icc,
    map_realMultiplicativeHaar_val,
    ← Measure.restrict_eq_self _ (show Icc 1 (Real.exp 1) ⊆ Ioi 0 from
      fun _ hx ↦ zero_lt_one.trans_le hx.1),
    restrict_realMultiplicative_Icc_one _ (Real.one_le_exp (by norm_num)), Real.log_exp, ENNReal.ofReal_one]

private theorem realMultiplicativeHaar_mulLeftInvariant :
    realMultiplicativeHaar.IsMulLeftInvariant where
  map_mul_left_eq_self a := by
    ext s hs
    let j : MeasurableEmbedding (Units.val : ℝˣ → ℝ) :=
      Units.isOpenEmbedding_val.measurableEmbedding
    let u := (a * ·) ⁻¹' s
    have hm : Measurable (a * ·) := (continuous_const_mul a).measurable
    have hu : MeasurableSet (Units.val '' u) := j.measurableSet_image' (hm hs)
    have hu₀ : Units.val '' u ⊆ ({0} : Set ℝ)ᶜ := range_realUnits_val ▸ image_subset_range _ _
    rw [Measure.map_apply hm hs, realMultiplicativeHaar,
      j.comap_apply, j.comap_apply]
    rw [← realMultiplicativeDensity_image_mul a.ne_zero hu hu₀]
    congr 1
    ext t
    constructor
    · rintro ⟨v, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a * b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(↑(a⁻¹ * b) : ℝ), ⟨a⁻¹ * b, ?_, rfl⟩, ?_⟩
      · simpa only [u, mem_preimage, mul_inv_cancel_left] using hb
      · change (↑(a * (a⁻¹ * b)) : ℝ) = ↑b
        rw [mul_inv_cancel_left]

public instance : realMultiplicativeHaar.IsHaarMeasure := by
  let : realMultiplicativeHaar.IsMulLeftInvariant := realMultiplicativeHaar_mulLeftInvariant
  let K : Set ℝˣ := Units.val ⁻¹' Icc 1 (Real.exp 1)
  have hK : IsCompact K := by
    apply Units.isOpenEmbedding_val.isCompact_iff.mpr
    rw [image_preimage_eq_of_subset (by
      rw [range_realUnits_val]
      exact fun _ hx ↦ (zero_lt_one.trans_le hx.1).ne')]
    exact isCompact_Icc
  have hlt : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  obtain ⟨t, ht⟩ := nonempty_Ioo.mpr hlt
  have hKint : (interior K).Nonempty := by
    refine ⟨Units.mk0 t (zero_lt_one.trans ht.1).ne', ?_⟩
    apply interior_maximal (t := Units.val ⁻¹' Ioo 1 (Real.exp 1))
      (preimage_mono Ioo_subset_Icc_self) (isOpen_Ioo.preimage Units.continuous_val)
    exact ht
  have hmass : realMultiplicativeHaar K = 1 := realMultiplicativeHaar_unitStrip
  exact Measure.isHaarMeasure_of_isCompact_nonempty_interior _ K hK hKint
    (hmass.symm ▸ one_ne_zero) (hmass.symm ▸ ENNReal.one_ne_top)

end Masullo
