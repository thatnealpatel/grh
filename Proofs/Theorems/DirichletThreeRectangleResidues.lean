module

public import Theorems.DirichletThreeHorizontalExhaustion
public import Props.RectangleResidue
public import Lemmas.TestedLogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Finite residue rectangles for the quadratic character modulo three

The contour uses Mathlib's completed L-function, without a conductor power.
This is a local finite-height repair corresponding to the counterclockwise
contour of Fig. 3 and (B.3.2.3), PDF pp. 605–606, and the logarithmic derivative
of §B.4.2.1, (B.4.2.2), PDF p. 614 (provisional manuscript mapping). Each
interior zero is counted with its full order. This does not exhaust the
infinite full-order sum or identify Mathlib's completion with an idelic one.
Owning check session: `01a20519-8da6-7d73-8b2b-9d442392e7a2`.
-/

open Complex Filter Set
open scoped ContDiff Topology

namespace Masullo

local notation "χ₃" => padicRamifiedThreeCharacter
local notation "completed₃" => DirichletCharacter.completedLFunction padicRamifiedThreeCharacter

private theorem three_ne_one : χ₃ ≠ 1 := by
  intro h
  exact DirichletCharacter.Odd.not_even χ₃ padicRamifiedThreeCharacter_odd
    (h ▸ DirichletCharacter.even_one)

/-- Mathlib's exact completion for the nontrivial character modulo three is entire. -/
public theorem analyticAt_padicRamifiedThree_completed (z : ℂ) : AnalyticAt ℂ completed₃ z :=
  Complex.analyticAt_iff_eventually_differentiableAt.mpr
    (Eventually.of_forall (DirichletCharacter.differentiable_completedLFunction three_ne_one))

/-- In particular the right edge of real part `3 / 2` contains no zero. -/
public theorem padicRamifiedThree_completed_ne_zero_of_one_le_re {z : ℂ} (hz : 1 ≤ z.re) :
    completed₃ z ≠ 0 :=
  DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ₃ (Or.inl three_ne_one) hz

/-- Primitive reflection to the inverse character excludes zeros on the left,
including the edge of real part `-1 / 2`. -/
public theorem padicRamifiedThree_completed_ne_zero_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) :
    completed₃ z ≠ 0 := by
  have hp := padicRamifiedThreeCharacter_isPrimitive
  have hre : 1 ≤ (1 - z).re := by simp [sub_re, hz]
  rw [← show 1 - (1 - z) = z by ring, hp.completedLFunction_one_sub]
  refine mul_ne_zero (mul_ne_zero ?_ (DirichletCharacter.rootNumber_ne_zero hp)) ?_
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ₃⁻¹
      (Or.inl (fun h ↦ three_ne_one (inv_eq_one.mp h))) hre

private theorem three_ne_zero_at_two : completed₃ 2 ≠ 0 :=
  padicRamifiedThree_completed_ne_zero_of_one_le_re (by norm_num)

/-- The natural analytic order never truncates an infinite order for this completion. -/
public theorem analyticOrderAt_padicRamifiedThree_completed_ne_top (z : ℂ) :
    analyticOrderAt completed₃ z ≠ ⊤ := by
  intro h
  have heq := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
    analyticAt_padicRamifiedThree_completed).mp h
  exact three_ne_zero_at_two (congrFun heq 2)

private theorem three_rectangleZeros_finite (T : ℝ) :
    {z ∈ Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T | completed₃ z = 0}.Finite := by
  let Z : Set ℂ := completed₃ ⁻¹' {0}
  have hcod : Zᶜ ∈ Filter.codiscrete ℂ :=
    (show AnalyticOnNhd ℂ completed₃ univ from
      fun z _ ↦ analyticAt_padicRamifiedThree_completed z).preimage_zero_mem_codiscrete
      three_ne_zero_at_two
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcod
  have hK : IsCompact (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hfin := (hK.inter_right hclosed).finite (hdisc.mono inter_subset_right)
  refine hfin.subset fun z hz ↦ ⟨?_, hz.2⟩
  obtain ⟨hre, him⟩ := mem_reProdIm.mp hz.1
  exact mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hre, Ioo_subset_Icc_self him⟩

/-- The distinct zeros strictly inside the rectangle of height `±T`. -/
public noncomputable def padicRamifiedThree_rectangleZeros (T : ℝ) : Finset ℂ :=
  (three_rectangleZeros_finite T).toFinset

@[simp] public theorem mem_padicRamifiedThree_rectangleZeros {T : ℝ} {z : ℂ} :
    z ∈ padicRamifiedThree_rectangleZeros T ↔
      z ∈ Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T ∧ completed₃ z = 0 := by
  rw [padicRamifiedThree_rectangleZeros, Set.Finite.mem_toFinset]
  rfl

/-- On a rectangle with zero-free horizontal edges, the counterclockwise
boundary integral is `2πi` times the finite sum over the interior zeros,
weighted by their full orders. There are no pole terms. -/
public theorem rectangleIntegral_padicRamifiedThree_completed_logDeriv {T : ℝ} (hT : 0 < T)
    (horiz : ∀ z : ℂ, z.re ∈ Icc (-1 / 2 : ℝ) (3 / 2) → |z.im| = T → completed₃ z ≠ 0)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    rectangleIntegral (-1 / 2) (3 / 2) (-T) T (fun s ↦ compactLogMellin g s * logDeriv completed₃ s) =
      (2 * Real.pi * I) * ∑ z ∈ padicRamifiedThree_rectangleZeros T,
        (analyticOrderNatAt completed₃ z : ℂ) * compactLogMellin g z := by
  refine rectangleIntegral_eq_sum_simpleResidues (by norm_num) (by linarith)
    (fun z hz ↦ (mem_padicRamifiedThree_rectangleZeros.mp hz).1) ?_ ?_
  · intro z hz
    obtain ⟨hre, him⟩ := mem_reProdIm.mp hz.1
    refine (analyticAt_compactLogMellin hg.continuous hcg z).mul
      ((analyticAt_padicRamifiedThree_completed z).deriv.div
        (analyticAt_padicRamifiedThree_completed z) ?_)
    intro hzero
    have hl : (-1 / 2 : ℝ) < z.re := hre.1.lt_of_ne (fun h ↦
      padicRamifiedThree_completed_ne_zero_of_re_nonpos (by rw [← h]; norm_num) hzero)
    have hr : z.re < (3 / 2 : ℝ) := hre.2.lt_of_ne (fun h ↦
      padicRamifiedThree_completed_ne_zero_of_one_le_re (by rw [h]; norm_num) hzero)
    have hb : -T < z.im := him.1.lt_of_ne (fun h ↦ horiz z hre (by rw [← h, abs_neg, abs_of_pos hT]) hzero)
    have ht : z.im < T := him.2.lt_of_ne (fun h ↦ horiz z hre (by rw [h, abs_of_pos hT]) hzero)
    exact hz.2 (mem_padicRamifiedThree_rectangleZeros.mpr ⟨mem_reProdIm.mpr ⟨⟨hl, hr⟩, ⟨hb, ht⟩⟩, hzero⟩)
  · intro z _
    have han := analyticAt_padicRamifiedThree_completed z
    have hord : meromorphicOrderAt completed₃ z = (analyticOrderNatAt completed₃ z : ℤ) := by
      rw [han.meromorphicOrderAt_eq,
        ← Nat.cast_analyticOrderNatAt (analyticOrderAt_padicRamifiedThree_completed_ne_top z),
        ENat.map_natCast]
    simpa only [Int.cast_natCast, div_eq_mul_inv] using
      logDeriv_weighted_principalPart han.meromorphicAt hord
        (analyticAt_compactLogMellin hg.continuous hcg z)

/-- The existing common-height sequence gives both the finite residue identities
and the two vanishing horizontal pairings for every smooth compact log profile. -/
public theorem padicRamifiedThree_completed_rectangleResidues_at_good_heights :
    ∃ T : ℕ → ℝ,
      (∀ n : ℕ, T n ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2)) ∧
      (∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → HasCompactSupport g →
        (∀ n, rectangleIntegral (-1 / 2) (3 / 2) (-T n) (T n)
            (fun s ↦ compactLogMellin g s * logDeriv completed₃ s) =
          (2 * Real.pi * I) * ∑ z ∈ padicRamifiedThree_rectangleZeros (T n),
            (analyticOrderNatAt completed₃ z : ℂ) * compactLogMellin g z) ∧
        (Tendsto (fun n ↦ ∫ σ in (-1 / 2 : ℝ)..(3 / 2),
          let s := (σ : ℂ) + (T n : ℂ) * I
          compactLogMellin g s * logDeriv completed₃ s) atTop (𝓝 0)) ∧
        (Tendsto (fun n ↦ ∫ σ in (-1 / 2 : ℝ)..(3 / 2),
          let s := (σ : ℂ) - (T n : ℂ) * I
          compactLogMellin g s * logDeriv completed₃ s) atTop (𝓝 0))) := by
  obtain ⟨T, _, _, _, hT, hbound, hlim⟩ := padicRamifiedThree_completed_horizontal
  refine ⟨T, hT, fun g hg hcg ↦ ⟨fun n ↦ ?_, hlim g hg hcg⟩⟩
  have hpos : 0 < T n := by linarith [(hT n).1, Nat.cast_nonneg (α := ℝ) n]
  refine rectangleIntegral_padicRamifiedThree_completed_logDeriv hpos ?_ hg hcg
  intro z hre him
  simpa only [Complex.re_add_im] using (hbound n z.re hre z.im him).1

end Masullo
