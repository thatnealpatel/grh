module

public import Theorems.RationalAdeleAddHaar
public import Theorems.RationalAdeleClassTopology
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Probability Haar measure on the additive rational adele classes

Restricting upstairs additive Haar to the half-open strip and projecting gives
normalized additive Haar on the quotient in Definition A.3.1.1, p. 555.
This proves the probability normalization; the counting-measure integral formula
of Theorem C.4.4.3 is separate.
-/

open NumberField MeasureTheory Set TopologicalSpace
open scoped Pointwise ENNReal

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "C" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → C)

local instance : CompactSpace C := compactSpace_rationalAdeleClasses
local instance : T2Space C := t2Space_rationalAdeleClasses
local instance : Countable rationalDiagonal := Set.countable_range (algebraMap ℚ A)

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace C] [BorelSpace C]

/-- Pushforward of normalized adelic Haar restricted to the half-open strip. -/
public noncomputable def rationalAdeleClassHaar : Measure C :=
  (rationalAdeleAddHaar.restrict rationalAdeleUnitStrip).map π

/-- Projecting the half-open strip preserves measure for the induced quotient measure. -/
public theorem measurePreserving_rationalAdeleClass_mk :
    MeasurePreserving π (rationalAdeleAddHaar.restrict rationalAdeleUnitStrip)
      rationalAdeleClassHaar :=
  ⟨QuotientAddGroup.continuous_mk.measurable, rfl⟩

public instance isProbabilityMeasure_rationalAdeleClassHaar :
    IsProbabilityMeasure rationalAdeleClassHaar := by
  constructor
  rw [rationalAdeleClassHaar, Measure.map_apply QuotientAddGroup.continuous_mk.measurable
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ, rationalAdeleAddHaar_unitStrip]

private theorem isAddLeftInvariant_rationalAdeleClassHaar :
    rationalAdeleClassHaar.IsAddLeftInvariant := by
  constructor
  intro c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  ext U hU
  have hπ : Measurable π := QuotientAddGroup.continuous_mk.measurable
  rw [Measure.map_apply (measurable_const_add _) hU]
  simp only [rationalAdeleClassHaar,
    Measure.map_apply hπ ((measurable_const_add (π a)) hU), Measure.map_apply hπ hU,
    Measure.restrict_apply (hπ ((measurable_const_add (π a)) hU)),
    Measure.restrict_apply (hπ hU)]
  -- Translating the strip by the lift gives another fundamental domain.
  have hD := rationalAdeleUnitStrip_isAddFundamentalDomain rationalAdeleAddHaar
  have hDa := hD.vadd_of_comm a
  have htrans : π ⁻¹' ((π a + ·) ⁻¹' U) ∩ rationalAdeleUnitStrip =
      (a + ·) ⁻¹' (π ⁻¹' U ∩ (a +ᵥ rationalAdeleUnitStrip)) := by
    ext x
    change (π a + π x ∈ U ∧ x ∈ rationalAdeleUnitStrip) ↔
      (π (a + x) ∈ U ∧ a + x ∈ a +ᵥ rationalAdeleUnitStrip)
    rw [QuotientAddGroup.mk_add, mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add, neg_add_cancel_left]
  rw [htrans, measure_preimage_add]
  -- Saturated preimages have the same intersection mass on the two domains.
  apply hDa.measure_set_eq hD (hπ hU)
  intro d
  have hd : π (d : A) = 0 := by
    rw [QuotientAddGroup.eq_zero_iff]
    exact d.property
  ext x
  change π ((d : A) + x) ∈ U ↔ π x ∈ U
  rw [QuotientAddGroup.mk_add, hd, zero_add]

/-- The induced probability is additive Haar on the compact quotient. -/
public instance isAddHaarMeasure_rationalAdeleClassHaar : rationalAdeleClassHaar.IsAddHaarMeasure := by
  let := isAddLeftInvariant_rationalAdeleClassHaar
  exact Measure.isAddHaarMeasure_of_isCompact_nonempty_interior _ univ isCompact_univ
    (by simp) (by simp) (by simp)

/-- There is only one additive Haar probability on the rational adele classes. -/
public theorem eq_rationalAdeleClassHaar (ν : Measure C) [ν.IsAddHaarMeasure]
    [IsProbabilityMeasure ν] : ν = rationalAdeleClassHaar := by
  have hscale := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure
    ν rationalAdeleClassHaar (isClosed_closure (s := (univ : Set C))).isCompact
  rw [measure_univ, measure_univ] at hscale
  change 1 = (↑(ν.addHaarScalarFactor rationalAdeleClassHaar) : ℝ≥0∞) * 1 at hscale
  rw [mul_one] at hscale
  ext U _
  rw [Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν rationalAdeleClassHaar
    (isClosed_closure (s := U)).isCompact]
  change (↑(ν.addHaarScalarFactor rationalAdeleClassHaar) : ℝ≥0∞) * _ = _
  rw [← hscale, one_mul]

public instance regular_rationalAdeleClassHaar : rationalAdeleClassHaar.Regular := by
  let K : PositiveCompacts C := ⊤
  have : IsProbabilityMeasure (Measure.addHaarMeasure K) := by
    constructor
    simpa only [K, PositiveCompacts.coe_top] using
      (Measure.addHaarMeasure_self (K₀ := K))
  rw [← eq_rationalAdeleClassHaar (Measure.addHaarMeasure K)]
  infer_instance

end Masullo
