module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The capacity chord in squared imbalance

Source: `40e98c62:.godel/bob/imbalance-chords.md:9–21`, at pin `5ab1b80f`.
Consumers: `5ab1b80f:.godel/bob/all-pairs-10-2.md:7` and
`5ab1b80f:.godel/bob/right-sector-10-2.md:25`.
Owning check session: `01a20ce0-1582-79d6-b657-1b3239837bf7`.

This proves the analytic interpolation for a finite positive measure, with the
worse of the two same-sign coefficient orientations. It includes the balanced
node, and takes the node lower bounds as inputs. No numerical bounds, table
certification, or interpolation across rectangles in the shift variables is
asserted here.
-/

open MeasureTheory

namespace Masullo.ImbalanceCapacityChord

/-- The same-sign capacity integrand at imbalance `h` and gap `d`. -/
@[expose] public noncomputable def capacityKernel (h d x : ℝ) : ℝ :=
  Real.sqrt (Real.cos (d * x / 2) ^ 2 + h ^ 2 * Real.sin (d * x / 2) ^ 2)

/-- The source capacity `K(h,d)` against the positive measure `ν`. -/
@[expose] public noncomputable def capacity (ν : Measure ℝ) (h d : ℝ) : ℝ :=
  ∫ x, capacityKernel h d x ∂ν

private theorem integrable_kernel {ν : Measure ℝ} [IsFiniteMeasure ν]
    (d : ℝ) {h : ℝ} (hh : 0 ≤ h) (hu : h ≤ 1) :
    Integrable (capacityKernel h d) ν := by
  have hc : Continuous (capacityKernel h d) := by unfold capacityKernel; fun_prop
  refine (integrable_const (μ := ν) (1 : ℝ)).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  unfold capacityKernel
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  refine Real.sqrt_le_iff.mpr ⟨zero_le_one, ?_⟩
  have hh2 : h ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hh hu 2
  calc
    _ ≤ Real.cos (d * x / 2) ^ 2 + Real.sin (d * x / 2) ^ 2 := by
      have hs := mul_le_mul_of_nonneg_right hh2 (sq_nonneg (Real.sin (d * x / 2)))
      simpa only [one_mul] using add_le_add_right hs (Real.cos (d * x / 2) ^ 2)
    _ = 1 ^ 2 := by rw [Real.cos_sq_add_sin_sq, one_pow]

private theorem chord_parameters {l h u : ℝ} (hl : 0 ≤ l) (hlh : l ≤ h)
    (hhu : h ≤ u) (hlu : l < u) :
    let t := (h ^ 2 - l ^ 2) / (u ^ 2 - l ^ 2)
    0 ≤ t ∧ 0 ≤ 1 - t ∧ (1 - t) * l ^ 2 + t * u ^ 2 = h ^ 2 := by
  have hden : 0 < u ^ 2 - l ^ 2 := sub_pos.mpr (pow_lt_pow_left₀ hlu hl (by decide))
  have hl2 := pow_le_pow_left₀ hl hlh 2
  have hu2 := pow_le_pow_left₀ (hl.trans hlh) hhu 2
  dsimp only
  refine ⟨div_nonneg (sub_nonneg.mpr hl2) hden.le,
    sub_nonneg.mpr ((div_le_one₀ hden).mpr (sub_le_sub_right hu2 _)), ?_⟩
  calc
    _ = l ^ 2 + (h ^ 2 - l ^ 2) / (u ^ 2 - l ^ 2) * (u ^ 2 - l ^ 2) := by ring
    _ = h ^ 2 := by rw [div_mul_cancel₀ _ hden.ne']; ring

/-- The capacity lies above its chord between any two distinct nodes in `[0,1]`,
with the interpolation parameter taken in squared imbalance. -/
public theorem capacity_chord (ν : Measure ℝ) [IsFiniteMeasure ν] (d : ℝ)
    {l h u : ℝ} (hl : 0 ≤ l) (hlh : l ≤ h) (hhu : h ≤ u) (hu : u ≤ 1) (hlu : l < u) :
    let t := (h ^ 2 - l ^ 2) / (u ^ 2 - l ^ 2)
    (1 - t) * capacity ν l d + t * capacity ν u d ≤ capacity ν h d := by
  let t := (h ^ 2 - l ^ 2) / (u ^ 2 - l ^ 2)
  obtain ⟨ht, ht', hsq⟩ : 0 ≤ t ∧ 0 ≤ 1 - t ∧ (1 - t) * l ^ 2 + t * u ^ 2 = h ^ 2 :=
    chord_parameters hl hlh hhu hlu
  have hpoint (x : ℝ) :
      (1 - t) * capacityKernel l d x + t * capacityKernel u d x ≤ capacityKernel h d x := by
    let F (z : ℝ) := Real.cos (d * x / 2) ^ 2 + z * Real.sin (d * x / 2) ^ 2
    have hF (z : ℝ) (hz : 0 ≤ z) : 0 ≤ F z := by dsimp only [F]; positivity
    have haff : (1 - t) * F (l ^ 2) + t * F (u ^ 2) = F (h ^ 2) := calc
      _ = F ((1 - t) * l ^ 2 + t * u ^ 2) := by dsimp only [F]; ring
      _ = _ := by rw [hsq]
    change (1 - t) * Real.sqrt (F (l ^ 2)) + t * Real.sqrt (F (u ^ 2)) ≤ Real.sqrt (F (h ^ 2))
    rw [← haff]
    exact Real.strictConcaveOn_sqrt.concaveOn.2 (Set.mem_Ici.mpr (hF _ (sq_nonneg l)))
      (Set.mem_Ici.mpr (hF _ (sq_nonneg u))) ht' ht (sub_add_cancel 1 t)
  have hil := integrable_kernel (ν := ν) d hl (hlh.trans (hhu.trans hu))
  have hih := integrable_kernel (ν := ν) d (hl.trans hlh) (hhu.trans hu)
  have hiu := integrable_kernel (ν := ν) d (hl.trans hlu.le) hu
  have hfl := hil.const_mul (1 - t)
  have hfu := hiu.const_mul t
  have hint : (∫ x, (1 - t) * capacityKernel l d x + t * capacityKernel u d x ∂ν) ≤
      ∫ x, capacityKernel h d x ∂ν := integral_mono (hfl.add hfu) hih hpoint
  rw [integral_add hfl hfu, integral_const_mul, integral_const_mul] at hint
  exact hint

private theorem max_abs_add_sub (a b : ℝ) : max |a + b| |a - b| = |a| + |b| := by
  apply le_antisymm
  · refine max_le (abs_add_le _ _) ?_
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  · rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg ha, abs_of_nonneg hb]
      exact (le_abs_self _).trans (le_max_left _ _)
    · rw [abs_of_nonneg ha, abs_of_nonpos hb, ← sub_eq_add_neg]
      exact (le_abs_self _).trans (le_max_right _ _)
    · rw [abs_of_nonpos ha, abs_of_nonneg hb, show -a + b = -(a - b) by ring]
      exact (neg_le_abs _).trans (le_max_right _ _)
    · rw [abs_of_nonpos ha, abs_of_nonpos hb, ← neg_add]
      exact (neg_le_abs _).trans (le_max_left _ _)

/-- Interchanging the two same-sign weights gives opposite deviations from the
same half-sum. This is the exact price of the worse absolute center. -/
public theorem worst_center_eq {h : ℝ} (hh : 0 ≤ h) (S₁ S₂ : ℝ) :
    max |((1 + h) * S₁ + (1 - h) * S₂) / 2| |((1 - h) * S₁ + (1 + h) * S₂) / 2| =
      |S₁ + S₂| / 2 + h * |S₁ - S₂| / 2 := by
  let a := (S₁ + S₂) / 2
  let b := h * (S₁ - S₂) / 2
  have hp : ((1 + h) * S₁ + (1 - h) * S₂) / 2 = a + b := by dsimp only [a, b]; ring
  have hm : ((1 - h) * S₁ + (1 + h) * S₂) / 2 = a - b := by dsimp only [a, b]; ring
  rw [hp, hm, max_abs_add_sub]
  simp only [a, b, abs_div, abs_mul, abs_of_nonneg hh, abs_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)]

/-- Node lower bounds give a lower bound for the slack after paying the worse
of the two absolute centers. The case `h = 0` requires no separate assumption. -/
public theorem slack_lower_bound (ν : Measure ℝ) [IsFiniteMeasure ν] (d S₁ S₂ : ℝ)
    {l h u L_l L_u : ℝ} (hl : 0 ≤ l) (hlh : l ≤ h) (hhu : h ≤ u) (hu : u ≤ 1) (hlu : l < u)
    (hLl : L_l ≤ capacity ν l d) (hLu : L_u ≤ capacity ν u d) :
    let t := (h ^ 2 - l ^ 2) / (u ^ 2 - l ^ 2)
    (1 - t) * L_l + t * L_u - |S₁ + S₂| / 2 - h * |S₁ - S₂| / 2 ≤
      capacity ν h d -
        max |((1 + h) * S₁ + (1 - h) * S₂) / 2| |((1 - h) * S₁ + (1 + h) * S₂) / 2| := by
  let t := (h ^ 2 - l ^ 2) / (u ^ 2 - l ^ 2)
  obtain ⟨ht, ht', _⟩ : 0 ≤ t ∧ 0 ≤ 1 - t ∧ (1 - t) * l ^ 2 + t * u ^ 2 = h ^ 2 :=
    chord_parameters hl hlh hhu hlu
  have hbound : (1 - t) * L_l + t * L_u ≤ capacity ν h d :=
    (add_le_add (mul_le_mul_of_nonneg_left hLl ht') (mul_le_mul_of_nonneg_left hLu ht)).trans
      (capacity_chord ν d hl hlh hhu hu hlu)
  dsimp only
  rw [worst_center_eq (hl.trans hlh), sub_sub]
  exact sub_le_sub_right hbound _

end Masullo.ImbalanceCapacityChord
