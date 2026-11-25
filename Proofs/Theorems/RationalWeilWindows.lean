module

public import Lemmas.PickPrimeTruncation
public import Lemmas.ShiftedZetaZeros
public import Theorems.RationalIdeleRadialExplicitFormula
import Theorems.RationalMellinDivisorJetBlock
import Theorems.RationalShortWindowStripTrace
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Tactic.Linarith

/-!
# Nested log windows for the rational reflected zero form

The zero argument is centered at `1/2`; the second Mellin sample is reflected
across the imaginary axis and conjugated. The scalar test for this product is
the autocorrelation, not the ordinary self-convolution. The window passage
below asserts no Riemann-hypothesis criterion.
-/

open Filter MeasureTheory Set
open scoped ComplexConjugate ContDiff Convolution Pointwise Topology

namespace Masullo

/-- The real part of the full-order rational zero sum with the reflected Mellin sample. -/
@[expose] public noncomputable def rationalWeilZeroForm (u : ℝ → ℂ) : ℝ :=
  (∑' ρ : criticalStripZetaZeros, (zetaZeroOrder ρ : ℂ) *
    compactLogMellin u (shiftedZetaZero ρ) * conj (compactLogMellin u (-conj (shiftedZetaZero ρ)))).re

local notation "L" => ContinuousLinearMap.mul ℂ ℂ

private theorem pickAutocorrelation_eq_reflectedConvolution (u : ℝ → ℂ) :
    pickAutocorrelation u = u ⋆[L, volume] (fun t ↦ conj (u (-t))) := by
  funext t
  calc
    _ = ∫ x, conj (u (x - t)) * u x := by
      simpa only [pickAutocorrelation, add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x ↦ conj (u (x - t)) * u x) t)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      change conj (u (x - t)) * u x = u x * conj (u (-(t - x)))
      rw [neg_sub, mul_comm]

private theorem compactLogMellin_reflectedConj (u : ℝ → ℂ) (z : ℂ) :
    compactLogMellin (fun t ↦ conj (u (-t))) z = conj (compactLogMellin u (-conj z)) := by
  rw [compactLogMellin, compactLogMellin, ← integral_conj]
  let f (t : ℝ) := conj (u t * Complex.exp ((-conj z) * (t : ℂ)))
  calc
    _ = ∫ t, f (-t) := by
      apply integral_congr_ae
      filter_upwards with t
      simp [f, ← Complex.exp_conj]
    _ = ∫ t, f t := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding f

/-- The autocorrelation Mellin transform in the positive log-exponent convention. -/
public theorem compactLogMellin_pickAutocorrelation {u : ℝ → ℂ}
    (hu : Continuous u) (hc : HasCompactSupport u) (z : ℂ) :
    compactLogMellin (pickAutocorrelation u) z =
      compactLogMellin u z * conj (compactLogMellin u (-conj z)) := by
  have hstar : Continuous (fun t ↦ conj (u (-t))) :=
    Complex.conjCLE.continuous.comp (hu.comp continuous_neg)
  have hcstar : HasCompactSupport (fun t ↦ conj (u (-t))) :=
    (hc.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero _)
  rw [pickAutocorrelation_eq_reflectedConvolution, compactLogMellin_convolution hu hc hstar hcstar,
    Pi.mul_apply, compactLogMellin_reflectedConj]

private theorem pickAutocorrelation_smooth_compact {u : ℝ → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ContDiff ℝ ∞ (pickAutocorrelation u) ∧ HasCompactSupport (pickAutocorrelation u) := by
  have hstar : ContDiff ℝ ∞ (fun t ↦ conj (u (-t))) :=
    Complex.conjCLE.contDiff.comp (hu.comp contDiff_neg)
  have hcstar : HasCompactSupport (fun t ↦ conj (u (-t))) :=
    (hc.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero _)
  rw [pickAutocorrelation_eq_reflectedConvolution]
  let Lℝ := ContinuousLinearMap.mul ℝ ℂ
  change ContDiff ℝ ∞ (u ⋆[Lℝ, volume] (fun t ↦ conj (u (-t)))) ∧
    HasCompactSupport (u ⋆[Lℝ, volume] (fun t ↦ conj (u (-t))))
  exact ⟨hcstar.contDiff_convolution_right Lℝ
      (hu.continuous.integrable_of_hasCompactSupport hc).locallyIntegrable hstar,
    hc.convolution Lℝ (μ := volume) hcstar⟩

/-- A test in `[-R,R]` has autocorrelation supported in `[-2R,2R]`. -/
public theorem tsupport_pickAutocorrelation_subset {R : ℝ} {u : ℝ → ℂ}
    (hs : tsupport u ⊆ Icc (-R) R) :
    tsupport (pickAutocorrelation u) ⊆ Icc (-(2 * R)) (2 * R) := by
  rw [pickAutocorrelation_eq_reflectedConvolution]
  apply closure_minimal _ isClosed_Icc
  refine (support_convolution_subset L).trans ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hx' := hs (subset_closure hx)
  have hy' : -y ∈ Icc (-R) R := hs (subset_closure (show u (-y) ≠ 0 from fun h ↦ hy (by simp [h])))
  exact ⟨by linarith [hx'.1, hy'.2], by linarith [hx'.2, hy'.1]⟩

set_option linter.concreteInstances false in
/-- The reflected summands are absolutely summable, and their real sum is
exactly the real part of the all-zero side of the rational radial scalar
formula on the autocorrelation. This uses the formula for general profiles,
which need not vanish at log norm zero. -/
public theorem rationalWeilZeroForm_radial_zeroSide
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    Summable (fun ρ : criticalStripZetaZeros ↦ ‖(zetaZeroOrder ρ : ℂ) *
      compactLogMellin u (shiftedZetaZero ρ) * conj (compactLogMellin u (-conj (shiftedZetaZero ρ)))‖) ∧
    rationalWeilZeroForm u = (∑' ρ : criticalStripZetaZeros,
      (zetaZeroOrder ρ : ℂ) * rationalIdeleRadialMellin (pickAutocorrelation u) ρ).re := by
  obtain ⟨hA, hcA⟩ := pickAutocorrelation_smooth_compact hu hc
  have hM (ρ : criticalStripZetaZeros) : rationalIdeleRadialMellin (pickAutocorrelation u) ρ =
      compactLogMellin u (shiftedZetaZero ρ) * conj (compactLogMellin u (-conj (shiftedZetaZero ρ))) :=
    (rationalIdeleRadialMellin_eq_shiftedCompactLogMellin hA.continuous hcA ρ).trans
      (compactLogMellin_pickAutocorrelation hu.continuous hc (shiftedZetaZero ρ))
  obtain ⟨_, _, hsum, _⟩ := rationalIdeleRadial_explicit_formula hA hcA
  exact ⟨by simpa only [hM, ← mul_assoc] using hsum,
    by simp only [rationalWeilZeroForm, hM, ← mul_assoc]⟩

/-- Global nonnegativity is equivalent to a common lower bound in each
sufficiently large window, with one error function tending to zero.
`pickL2Sq u` is the squared Lebesgue `L²` norm. The passage to the limit
uses the bound on each fixed test and does not normalize it. -/
public theorem rationalWeilZeroForm_nonneg_iff_window_lower_bounds :
    (∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u → 0 ≤ rationalWeilZeroForm u) ↔
    ∃ η : ℝ → ℝ, Tendsto η atTop (𝓝 0) ∧ ∀ᶠ R in atTop,
      ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → tsupport u ⊆ Icc (-R) R →
        -η R * pickL2Sq u ≤ rationalWeilZeroForm u := by
  constructor
  · intro h
    refine ⟨fun _ ↦ 0, tendsto_const_nhds, Eventually.of_forall fun R u hu hs ↦ ?_⟩
    have hc : HasCompactSupport u := isCompact_Icc.of_isClosed_subset isClosed_closure hs
    simpa only [neg_zero, zero_mul] using h u hu hc
  · rintro ⟨η, hη, hbound⟩ u hu hc
    obtain ⟨a, ha⟩ := hc.bddBelow
    obtain ⟨b, hb⟩ := hc.bddAbove
    have hs : ∀ᶠ R : ℝ in atTop, tsupport u ⊆ Icc (-R) R := by
      filter_upwards [eventually_ge_atTop (max (-a) b)] with R hR x hx
      exact ⟨(neg_le.mp ((le_max_left _ _).trans hR)).trans (ha hx),
        (hb hx).trans ((le_max_right _ _).trans hR)⟩
    have hlim : Tendsto (fun R ↦ -η R * pickL2Sq u) atTop (𝓝 0) := by
      simpa only [neg_zero, zero_mul] using hη.neg.mul_const (pickL2Sq u)
    apply le_of_tendsto hlim
    filter_upwards [hbound, hs] with R hR huR
    exact hR u hu huR

end Masullo
