module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Removing low-observable mass from a zero-moment probability law

Source: `b825bc5:.godel/bob/noisy-sparse-harmonics.md`, lines 11–16 (the
common perturbation in line 16). The exact-zero inputs in the two branches
are a mixture of shifted grids and a cosine-density law, following
`fea7eb0:.godel/alice/sharp-sparse-harmonics.md`. This lemma takes their
mean, moment, and low-observable mass bounds as hypotheses; it does not
construct the witnesses or assert an angular minimax or arithmetic bound.

The construction works on any measurable space, including the full circle
with all queried harmonics and with atomic probability laws. A single
scaled restriction removes the desired mass, even when this takes a
fraction of an atom. The tolerance may be any nonnegative real number.

Owning check session: `01a208be-3e66-7cc4-8f5d-223682424036`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Masullo

/-- Delete mass `e / (1 + e)` from `A` and renormalize. One probability
measure controls every test simultaneously, without any restriction on the
index type or on the sign of the upper bound `B` on `A`. -/
public theorem exists_noisy_moment_witness {α ι : Type*} [MeasurableSpace α]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀] (h : ι → α → ℂ)
    (hh_meas : ∀ j, Measurable (h j)) (hh_norm : ∀ j x, ‖h j x‖ ≤ 1)
    (hh_zero : ∀ j, (∫ x, h j x ∂μ₀) = 0)
    (f : α → ℝ) (hf : Integrable f μ₀) {C B e : ℝ}
    (hC : C ≤ ∫ x, f x ∂μ₀) (he : 0 ≤ e) {A : Set α} (hA : MeasurableSet A)
    (hmass : ENNReal.ofReal (e / (1 + e)) ≤ μ₀ A) (hB : ∀ x ∈ A, f x ≤ B) :
    ∃ μ : Measure α, IsProbabilityMeasure μ ∧
      (∀ j, ‖∫ x, h j x ∂μ‖ ≤ e) ∧ (1 + e) * C - e * B ≤ ∫ x, f x ∂μ := by
  rcases he.eq_or_lt with rfl | he_pos
  · refine ⟨μ₀, inferInstance, fun j ↦ ?_, ?_⟩
    · simp [hh_zero j]
    · simpa using hC
  have hs : 0 < 1 + e := by linarith
  let t : ℝ := e / (1 + e)
  have ht : 0 < t := div_pos he_pos hs
  have hst : (1 + e) * t = e := by
    rw [mul_comm]
    exact div_mul_cancel₀ e hs.ne'
  have htA : t ≤ (μ₀ A).toReal := calc
    t = (ENNReal.ofReal t).toReal := (ENNReal.toReal_ofReal ht.le).symm
    _ ≤ (μ₀ A).toReal := ENNReal.toReal_mono (measure_ne_top μ₀ A) hmass
  have hA_pos : 0 < (μ₀ A).toReal := ht.trans_le htA
  let r : ℝ := t / (μ₀ A).toReal
  have hr : 0 ≤ r := (div_pos ht hA_pos).le
  have hr₁ : r ≤ 1 := (div_le_iff₀ hA_pos).mpr (by simpa only [one_mul] using htA)
  have hrA : r * (μ₀ A).toReal = t := div_mul_cancel₀ t hA_pos.ne'
  -- Split the original measure into retained and deleted positive parts.
  let ν : Measure α := ENNReal.ofReal r • μ₀.restrict A
  let ρ : Measure α := ENNReal.ofReal (1 - r) • μ₀.restrict A + μ₀.restrict Aᶜ
  have hsplit : ρ + ν = μ₀ := by
    dsimp only [ρ, ν]
    rw [add_right_comm, ← add_smul, ← ENNReal.ofReal_add (sub_nonneg.mpr hr₁) hr,
      sub_add_cancel, ENNReal.ofReal_one, one_smul, Measure.restrict_add_restrict_compl hA]
  have hρ_le : ρ ≤ μ₀ := hsplit ▸ Measure.le_add_right (ν' := ν) le_rfl
  have hν_le : ν ≤ μ₀ := hsplit ▸ Measure.le_add_left (ν' := ρ) le_rfl
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ₀ hν_le
  have hν_mass : ν univ = ENNReal.ofReal t := by
    change (ENNReal.ofReal r • μ₀.restrict A) univ = _
    rw [smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
      ← ENNReal.ofReal_toReal (measure_ne_top μ₀ A), ← ENNReal.ofReal_mul hr, hrA]
  have hρ_mass : ρ univ = ENNReal.ofReal (1 - t) := by
    rw [ENNReal.ofReal_sub _ ht.le, ENNReal.ofReal_one, ← hν_mass]
    apply ENNReal.eq_sub_of_add_eq (measure_ne_top ν univ)
    rw [← add_apply, hsplit, measure_univ]
  have hsplit_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {g : α → E} (hg : Integrable g μ₀) :
      (∫ x, g x ∂ρ) + (∫ x, g x ∂ν) = ∫ x, g x ∂μ₀ := by
    rw [← integral_add_measure (hg.mono_measure hρ_le) (hg.mono_measure hν_le), hsplit]
  refine ⟨ENNReal.ofReal (1 + e) • ρ, ⟨?_⟩, ?_, ?_⟩
  · rw [smul_apply, smul_eq_mul, hρ_mass, ← ENNReal.ofReal_mul hs.le,
      mul_sub, mul_one, hst, add_sub_cancel_right, ENNReal.ofReal_one]
  · intro j
    have hj : Integrable (h j) μ₀ :=
      Integrable.of_bound (hh_meas j).aestronglyMeasurable 1 (ae_of_all _ (hh_norm j))
    have hjρ : (∫ x, h j x ∂ρ) = -(∫ x, h j x ∂ν) :=
      add_eq_zero_iff_eq_neg.mp ((hsplit_integral hj).trans (hh_zero j))
    have hjν : ‖∫ x, h j x ∂ν‖ ≤ t := by
      simpa only [one_mul, measureReal_def, hν_mass, ENNReal.toReal_ofReal ht.le] using
        (norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all _ (hh_norm j)))
    rw [integral_smul_measure, ENNReal.toReal_ofReal hs.le, norm_smul,
      Real.norm_of_nonneg hs.le, hjρ, norm_neg]
    calc
      _ ≤ (1 + e) * t := mul_le_mul_of_nonneg_left hjν hs.le
      _ = e := hst
  · have hA_mean : (∫ x in A, f x ∂μ₀) ≤ (μ₀ A).toReal * B := by
      calc
        _ ≤ ∫ _ in A, B ∂μ₀ := setIntegral_mono_on hf.restrict (integrable_const B) hA hB
        _ = _ := by rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    have hν_mean : (∫ x, f x ∂ν) ≤ t * B := by
      change (∫ x, f x ∂(ENNReal.ofReal r • μ₀.restrict A)) ≤ t * B
      rw [integral_smul_measure, ENNReal.toReal_ofReal hr, smul_eq_mul, ← hrA, mul_assoc]
      exact mul_le_mul_of_nonneg_left hA_mean hr
    have hρ_mean : C - t * B ≤ ∫ x, f x ∂ρ := by
      linarith [hsplit_integral hf]
    rw [integral_smul_measure, ENNReal.toReal_ofReal hs.le, smul_eq_mul]
    calc
      (1 + e) * C - e * B = (1 + e) * (C - t * B) := by
        rw [mul_sub, ← mul_assoc, hst]
      _ ≤ (1 + e) * (∫ x, f x ∂ρ) := mul_le_mul_of_nonneg_left hρ_mean hs.le

end Masullo
