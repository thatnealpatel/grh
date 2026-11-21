module

public import Lemmas.ShiftedZetaZeros
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Linarith

/-! Supporting analytic and finiteness facts for the rational form of (B.4.2.2). -/

open Complex Set

namespace Masullo

public theorem analyticAt_completedZeta {s : ℂ} (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  let U : Set ℂ := {0}ᶜ ∩ {1}ᶜ
  have hopen : IsOpen U := isOpen_compl_singleton.inter isOpen_compl_singleton
  have hdiff : DifferentiableOn ℂ completedRiemannZeta U := fun w hw ↦
    (differentiableAt_completedZeta hw.1 hw.2).differentiableWithinAt
  exact hdiff.analyticOnNhd hopen s ⟨h₀, h₁⟩

private theorem completedZeta_eq_zero_iff_of_re_pos {s : ℂ} (h₀ : s ≠ 0) (h : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  rw [riemannZeta_def_of_ne_zero h₀, div_eq_zero_iff]
  simp [Gammaℝ_ne_zero_of_re_pos h]

/-- Off its two poles, the completed zeta function has exactly the open-strip zeros. -/
public theorem completedZeta_eq_zero_iff_mem_criticalStripZetaZeros {s : ℂ}
    (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    completedRiemannZeta s = 0 ↔ s ∈ criticalStripZetaZeros := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hp : 0 < s.re := by
      by_contra! hn
      have hre : 1 ≤ (1 - s).re := by simpa using hn
      exact riemannZeta_ne_zero_of_one_le_re hre
        ((completedZeta_eq_zero_iff_of_re_pos (sub_ne_zero.mpr h₁.symm) (zero_lt_one.trans_le hre)).mp
          ((completedRiemannZeta_one_sub s).trans h))
    have hz := (completedZeta_eq_zero_iff_of_re_pos h₀ hp).mp h
    exact mem_criticalStripZetaZeros.mpr ⟨hz, hp,
      lt_of_not_ge fun hs ↦ riemannZeta_ne_zero_of_one_le_re hs hz⟩
  · obtain ⟨hz, hp, _⟩ := mem_criticalStripZetaZeros.mp h
    exact (completedZeta_eq_zero_iff_of_re_pos h₀ hp).mpr hz

/-- In a bounded open height interval there are only finitely many distinct
open-strip zeros, by compactness of the enclosing closed rectangle. -/
public theorem criticalStripZetaZeros_boundedIm_finite (u v : ℝ) :
    {ρ : criticalStripZetaZeros | u < (ρ : ℂ).im ∧ (ρ : ℂ).im < v}.Finite := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc u v) := isCompact_Icc.reProdIm isCompact_Icc
  refine (hK.inter_riemannZetaZeros_finite.preimage Subtype.val_injective.injOn).subset ?_
  intro ρ hρ
  obtain ⟨hz, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
  exact ⟨mem_reProdIm.mpr ⟨⟨hpos.le, hlt.le⟩, ⟨hρ.1.le, hρ.2.le⟩⟩,
    mem_riemannZetaZeros.mpr hz⟩

end Masullo
