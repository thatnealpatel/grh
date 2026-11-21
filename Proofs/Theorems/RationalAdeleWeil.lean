module

public import Theorems.RationalAdeleClassHaar
public import Lemmas.RationalAdeleStripSection

/-!
# Weil's integration formula over the additive rational adele classes

The nonnegative Borel version of (C.4.4.5), p. 718, on the actual rational
adeles, with counting measure on the discrete diagonal and the probability
normalization of Definition A.3.1.1. This is not the Pettis integral statement.
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

/-- The sum is independent of the representative, at every adele. -/
public theorem rationalAdelePeriodization_mk (f : A → ℝ≥0∞) (a : A) :
    rationalAdelePeriodization f (π a) = ∑' d : rationalDiagonal, f (a + (d : A)) := by
  let s := rationalAdeleStripRep (π a)
  have h : s - a ∈ rationalDiagonal :=
    QuotientAddGroup.eq_iff_sub_mem.mp (mk_rationalAdeleStripRep (π a))
  let d₀ : rationalDiagonal := ⟨s - a, h⟩
  calc
    rationalAdelePeriodization f (π a) = ∑' d : rationalDiagonal, f (a + (↑(d₀ + d) : A)) := by
      unfold rationalAdelePeriodization
      apply tsum_congr
      intro d
      congr 1
      change s + (d : A) = a + ((s - a) + (d : A))
      abel
    _ = ∑' d : rationalDiagonal, f (a + (d : A)) :=
      (Equiv.addLeft d₀).tsum_eq (fun d : rationalDiagonal ↦ f (a + (d : A)))

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

end Masullo
