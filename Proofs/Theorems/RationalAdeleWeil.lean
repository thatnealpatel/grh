module

public import Theorems.RationalAdeleClassHaar
public import Lemmas.RationalAdeleStripSection
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weil's integration formula over the additive rational adele classes

The nonnegative Borel version of (C.4.4.5), p. 718, and the complex Borel
`L¹` case of (D.1.2.1), p. 747, on the actual rational adeles. The diagonal
has counting measure, and the quotient has the probability normalization
of Definition A.3.1.1. This is not the Pettis integral statement.
-/

open NumberField MeasureTheory
open scoped ENNReal

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "C" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → C)

local instance : Countable rationalDiagonal := Set.countable_range (algebraMap ℚ A)

/-- Periodization by the diagonal rationals, equivalently integration against
counting measure. The nonnegative sum may be infinite. -/
public noncomputable def rationalAdelePeriodization (f : A → ℝ≥0∞) (c : C) : ℝ≥0∞ :=
  ∑' d : rationalDiagonal, f (rationalAdeleStripRep c + (d : A))

private theorem tsum_rationalAdeleStripRep_mk {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : A → E) (a : A) :
    (∑' d : rationalDiagonal, f (rationalAdeleStripRep (π a) + (d : A))) =
      ∑' d : rationalDiagonal, f (a + (d : A)) := by
  let s := rationalAdeleStripRep (π a)
  have h : s - a ∈ rationalDiagonal :=
    QuotientAddGroup.eq_iff_sub_mem.mp (mk_rationalAdeleStripRep (π a))
  let d₀ : rationalDiagonal := ⟨s - a, h⟩
  calc
    (∑' d : rationalDiagonal, f (s + (d : A))) =
        ∑' d : rationalDiagonal, f (a + (↑(d₀ + d) : A)) := by
      apply tsum_congr
      intro d
      congr 1
      change s + (d : A) = a + ((s - a) + (d : A))
      abel
    _ = ∑' d : rationalDiagonal, f (a + (d : A)) :=
      (Equiv.addLeft d₀).tsum_eq (fun d : rationalDiagonal ↦ f (a + (d : A)))

/-- The nonnegative sum is independent of the representative, at every adele. -/
public theorem rationalAdelePeriodization_mk (f : A → ℝ≥0∞) (a : A) :
    rationalAdelePeriodization f (π a) = ∑' d : rationalDiagonal, f (a + (d : A)) :=
  tsum_rationalAdeleStripRep_mk f a

/-- Complex periodization by the diagonal rationals. This uses Lean's totalized
sum; the `L¹` theorem guarantees absolute convergence only almost everywhere. -/
public noncomputable def rationalAdeleComplexPeriodization (f : A → ℂ) (c : C) : ℂ :=
  ∑' d : rationalDiagonal, f (rationalAdeleStripRep c + (d : A))

/-- Reindexing the totalized complex sum permits any lift of the class. -/
public theorem rationalAdeleComplexPeriodization_mk (f : A → ℂ) (a : A) :
    rationalAdeleComplexPeriodization f (π a) = ∑' d : rationalDiagonal, f (a + (d : A)) :=
  tsum_rationalAdeleStripRep_mk f a

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace C] [BorelSpace C]

public theorem measurable_rationalAdelePeriodization {f : A → ℝ≥0∞} (hf : Measurable f) :
    Measurable (rationalAdelePeriodization f) :=
  Measurable.tsum fun d ↦ hf.comp ((measurable_add_const (d : A)).comp measurable_rationalAdeleStripRep)

/-- Weil's integral formula for every nonnegative Borel function, with no
finiteness assumption on either side. -/
public theorem lintegral_eq_lintegral_rationalAdelePeriodization {f : A → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂rationalAdeleAddHaar =
      ∫⁻ c, rationalAdelePeriodization f c ∂rationalAdeleClassHaar := by
  let μ := rationalAdeleAddHaar
  let S := rationalAdeleUnitStrip
  have hD := rationalAdeleUnitStrip_isAddFundamentalDomain μ
  calc
    ∫⁻ a, f a ∂μ = ∑' d : rationalDiagonal, ∫⁻ a in S, f ((d : A) + a) ∂μ :=
      hD.lintegral_eq_tsum'' f
    _ = ∫⁻ a in S, ∑' d : rationalDiagonal, f ((d : A) + a) ∂μ :=
      (lintegral_tsum (f := fun (d : rationalDiagonal) a ↦ f ((d : A) + a))
        (fun d ↦ (hf.comp (measurable_const_add (d : A))).aemeasurable)).symm
    _ = ∫⁻ a in S, rationalAdelePeriodization f (π a) ∂μ := by
      simp only [rationalAdelePeriodization_mk, add_comm]
    _ = ∫⁻ c, rationalAdelePeriodization f c ∂rationalAdeleClassHaar :=
      measurePreserving_rationalAdeleClass_mk.lintegral_comp (measurable_rationalAdelePeriodization hf)

public theorem measurable_rationalAdeleComplexPeriodization {f : A → ℂ} (hf : Measurable f) :
    Measurable (rationalAdeleComplexPeriodization f) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.tsum
  intro d
  exact (hf.comp ((measurable_add_const (d : A)).comp
    measurable_rationalAdeleStripRep)).stronglyMeasurable

private theorem lintegral_periodized_eNorm_lt_top {f : A → ℂ} (hf : Measurable f)
    (hfi : Integrable f rationalAdeleAddHaar) :
    (∫⁻ c, rationalAdelePeriodization (fun a ↦ ‖f a‖ₑ) c ∂rationalAdeleClassHaar) < ∞ := by
  rw [← lintegral_eq_lintegral_rationalAdelePeriodization hf.eNorm]
  exact hfi.hasFiniteIntegral

/-- An upstairs Borel `L¹` function has absolutely summable fibers for almost
all classes, with respect to the quotient probability. -/
public theorem ae_summable_norm_rationalAdeleComplexPeriodization {f : A → ℂ}
    (hf : Measurable f) (hfi : Integrable f rationalAdeleAddHaar) :
    ∀ᵐ c ∂rationalAdeleClassHaar,
      Summable (fun d : rationalDiagonal ↦ ‖f (rationalAdeleStripRep c + (d : A))‖) := by
  filter_upwards [ae_lt_top (measurable_rationalAdelePeriodization hf.eNorm)
    (lintegral_periodized_eNorm_lt_top hf hfi).ne] with c hc
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hc.ne)

/-- The complex periodization is integrable, dominated in extended norm by
the nonnegative periodization of the extended norm. -/
public theorem integrable_rationalAdeleComplexPeriodization {f : A → ℂ}
    (hf : Measurable f) (hfi : Integrable f rationalAdeleAddHaar) :
    Integrable (rationalAdeleComplexPeriodization f) rationalAdeleClassHaar := by
  refine ⟨(measurable_rationalAdeleComplexPeriodization hf).aestronglyMeasurable, ?_⟩
  exact (lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm).trans_lt
    (lintegral_periodized_eNorm_lt_top hf hfi)

/-- Weil's integral formula for complex Borel `L¹` functions. -/
public theorem integral_eq_integral_rationalAdeleComplexPeriodization {f : A → ℂ}
    (hf : Measurable f) (hfi : Integrable f rationalAdeleAddHaar) :
    ∫ a, f a ∂rationalAdeleAddHaar =
      ∫ c, rationalAdeleComplexPeriodization f c ∂rationalAdeleClassHaar := by
  let μ := rationalAdeleAddHaar
  let S := rationalAdeleUnitStrip
  have hD := rationalAdeleUnitStrip_isAddFundamentalDomain μ
  -- Absolute integrability upstairs bounds the sum of the strip norm integrals.
  have hfin : (∑' d : rationalDiagonal, ∫⁻ a in S, ‖f ((d : A) + a)‖ₑ ∂μ) ≠ ∞ :=
    (hD.lintegral_eq_tsum'' (fun a ↦ ‖f a‖ₑ)).symm.trans_ne hfi.hasFiniteIntegral.ne
  calc
    ∫ a, f a ∂μ = ∑' d : rationalDiagonal, ∫ a in S, f ((d : A) + a) ∂μ :=
      hD.integral_eq_tsum'' f hfi
    _ = ∫ a in S, ∑' d : rationalDiagonal, f ((d : A) + a) ∂μ :=
      (integral_tsum (fun d : rationalDiagonal ↦
        (hf.comp (measurable_const_add (d : A))).aestronglyMeasurable) hfin).symm
    _ = ∫ a in S, rationalAdeleComplexPeriodization f (π a) ∂μ := by
      simp only [rationalAdeleComplexPeriodization_mk, add_comm]
    _ = ∫ c, rationalAdeleComplexPeriodization f c ∂rationalAdeleClassHaar := by
      have hπ := measurePreserving_rationalAdeleClass_mk
      rw [← hπ.map_eq, integral_map_of_stronglyMeasurable hπ.measurable
        (measurable_rationalAdeleComplexPeriodization hf).stronglyMeasurable]

end Masullo
