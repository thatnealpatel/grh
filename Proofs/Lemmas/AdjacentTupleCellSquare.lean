module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Physical-space identities for adjacent tuple cells

Source: `233d4a52:.godel/bob/adjacent-tuple-cells.md`, lines 5–23, specifically
`∫ m_ℓ² = ℓ B_ℓ` and `Q_d = 2 B_δ - B_(2δ)`. This file only treats the
physical-space identities, before the Fourier and arithmetic steps.

The atoms are indexed, not quotiented by location: distinct indices can have
the same location. The weights are nonnegative reals with no mass normalization.
Owning check session: `01a2095b-3cd7-7c85-a8af-4a73f8cbf3ba`.
-/

open MeasureTheory Set
open scoped BigOperators NNReal

namespace Masullo.AdjacentTupleCell

variable {ι : Type*} [Fintype ι]

/-- The mass `m_ℓ(x)` of `[x, x + ℓ)` for the finite atomic family `(y i, w i)`. -/
@[expose] public noncomputable def mass (y : ι → ℝ) (w : ι → ℝ≥0) (ℓ x : ℝ) : ℝ :=
  ∑ i, (Ico x (x + ℓ)).indicator (fun _ ↦ (w i : ℝ)) (y i)

/-- The tent `T_ℓ(v) = max (0, 1 - |v| / ℓ)`. -/
@[expose] public noncomputable def tent (ℓ v : ℝ) : ℝ :=
  max 0 (1 - |v| / ℓ)

/-- The weighted tent sum `B_ℓ`, taken over all ordered pairs of atom indices. -/
@[expose] public noncomputable def pairSum (y : ι → ℝ) (w : ι → ℝ≥0) (ℓ : ℝ) : ℝ :=
  ∑ i, ∑ j, (w i : ℝ) * (w j : ℝ) * tent ℓ (y i - y j)

private theorem mem_cell_iff_mem_starts {ℓ x y : ℝ} :
    y ∈ Ico x (x + ℓ) ↔ x ∈ Ioc (y - ℓ) y := by
  simp only [mem_Ico, mem_Ioc, sub_lt_iff_lt_add, and_comm]

-- A pair contributes exactly on the intersection of the two intervals of starts.
private noncomputable def pairContribution (ℓ y z a b : ℝ) : ℝ → ℝ :=
  (Ioc (y - ℓ) y ∩ Ioc (z - ℓ) z).indicator (fun _ ↦ a * b)

private theorem mass_sq_eq_sum (y : ι → ℝ) (w : ι → ℝ≥0) (ℓ x : ℝ) :
    mass y w ℓ x ^ 2 = ∑ i, ∑ j, pairContribution ℓ (y i) (y j) (w i) (w j) x := by
  rw [mass, pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [pairContribution, indicator_apply, mem_inter_iff, ← mem_cell_iff_mem_starts]
  by_cases hi : y i ∈ Ico x (x + ℓ) <;> by_cases hj : y j ∈ Ico x (x + ℓ) <;> simp [hi, hj]

private theorem integrable_pairContribution (ℓ y z a b : ℝ) :
    Integrable (pairContribution ℓ y z a b) volume := by
  unfold pairContribution
  apply IntegrableOn.integrable_indicator _ (measurableSet_Ioc.inter measurableSet_Ioc)
  refine integrableOn_const ?_ eNorm_ne_top
  rw [Ioc_inter_Ioc, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

private theorem integrable_mass_sq (y : ι → ℝ) (w : ι → ℝ≥0) (ℓ : ℝ) :
    Integrable (fun x ↦ mass y w ℓ x ^ 2) volume := by
  simp_rw [mass_sq_eq_sum]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ integrable_pairContribution ℓ (y i) (y j) (w i) (w j)

private theorem overlap_length {ℓ : ℝ} (hℓ : 0 < ℓ) (y z : ℝ) :
    (volume : Measure ℝ).real (Ioc (y - ℓ) y ∩ Ioc (z - ℓ) z) = ℓ * tent ℓ (y - z) := by
  have hdiff : min y z - max (y - ℓ) (z - ℓ) = ℓ - |y - z| := by
    rcases le_total y z with h | h
    · rw [min_eq_left h, max_eq_right (sub_le_sub_right h ℓ), abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, max_eq_left (sub_le_sub_right h ℓ), abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  rw [Ioc_inter_Ioc, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal', hdiff, tent,
    mul_max_of_nonneg _ _ hℓ.le, mul_zero, mul_sub, mul_one, mul_div_cancel₀ _ hℓ.ne', max_comm]

private theorem integral_pairContribution {ℓ : ℝ} (hℓ : 0 < ℓ) (y z a b : ℝ) :
    (∫ x, pairContribution ℓ y z a b x) = ℓ * (a * b * tent ℓ (y - z)) := by
  rw [pairContribution, integral_indicator (measurableSet_Ioc.inter measurableSet_Ioc),
    setIntegral_const, overlap_length hℓ, smul_eq_mul]
  ring

/-- The Lebesgue integral of the squared cell mass is `ℓ B_ℓ`. -/
public theorem integral_mass_sq (y : ι → ℝ) (w : ι → ℝ≥0) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x, mass y w ℓ x ^ 2) = ℓ * pairSum y w ℓ := by
  simp_rw [mass_sq_eq_sum]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_pairContribution ℓ (y i) (y j) (w i) (w j))]
  simp_rw [integral_finsetSum _ (fun j _ ↦ integrable_pairContribution ℓ _ (y j) _ (w j)),
    integral_pairContribution hℓ, pairSum, Finset.mul_sum]

private theorem mass_add_mass (y : ι → ℝ) (w : ι → ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    mass y w δ x + mass y w δ (x + δ) = mass y w (2 * δ) x := by
  have h₁ : x ≤ x + δ := le_add_of_nonneg_right hδ.le
  have h₂ : x + δ ≤ x + δ + δ := le_add_of_nonneg_right hδ.le
  have hd : Disjoint (Ico x (x + δ)) (Ico (x + δ) (x + δ + δ)) :=
    Ico_disjoint_Ico.mpr ((min_le_left _ _).trans (le_max_right _ _))
  have he : x + 2 * δ = x + δ + δ := by ring
  rw [mass, mass, mass, ← Finset.sum_add_distrib, he, ← Ico_union_Ico_eq_Ico h₁ h₂]
  exact Finset.sum_congr rfl fun i _ ↦ (congrFun (indicator_union_of_disjoint hd _) (y i)).symm

/-- The normalized adjacent-cell square is `2 B_δ - B_(2δ)`. -/
public theorem normalized_integral_adjacent_mass_sub_sq (y : ι → ℝ) (w : ι → ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) :
    (1 / (2 * δ)) * (∫ x, (mass y w δ x - mass y w δ (x + δ)) ^ 2) =
      2 * pairSum y w δ - pairSum y w (2 * δ) := by
  have h2δ : 0 < 2 * δ := mul_pos two_pos hδ
  have hsq := integrable_mass_sq y w δ
  have hshift := hsq.comp_add_right δ
  have hdouble := integrable_mass_sq y w (2 * δ)
  have hpoint (x : ℝ) :
      (mass y w δ x - mass y w δ (x + δ)) ^ 2 =
        2 * mass y w δ x ^ 2 + 2 * mass y w δ (x + δ) ^ 2 - mass y w (2 * δ) x ^ 2 := by
    rw [← mass_add_mass y w hδ x]
    ring
  have hsub := integral_sub ((hsq.const_mul 2).add (hshift.const_mul 2)) hdouble
  simp only [Pi.add_apply] at hsub
  simp_rw [hpoint]
  rw [hsub,
    integral_add (hsq.const_mul 2) (hshift.const_mul 2), integral_const_mul, integral_const_mul,
    integral_add_right_eq_self (fun x ↦ mass y w δ x ^ 2) δ,
    integral_mass_sq y w hδ, integral_mass_sq y w h2δ]
  field_simp [hδ.ne']
  ring

end Masullo.AdjacentTupleCell
