module

public import Props.RationalExplicitFormulaResidues
public import Props.RectangleResidue
public import Lemmas.RationalCompletedZetaZeros
import Mathlib.Tactic.Linarith

/-!
# The finite completed-zeta contour over the rationals

Masullo applies the rectangle residue identity (B.3.2.3), p. 606, to the
completed logarithmic derivative in (B.4.2.1)–(B.4.2.2), p. 614. At finite
height, the residue theorem uses the principal part of the tested integrand;
`Props.RationalExplicitFormulaResidues` supplies its simple germs with the
actual orders. `Props.RectangleResidue` uses the counterclockwise orientation
of Figure 3, p. 605. Taking the height limit is a separate step.
-/

open Complex Set Filter
open scoped Topology

namespace Masullo

/-- The finite contour with sides at `1-a` and `a`. The two completed-zeta
poles contribute the negative test values at zero and one. Each distinct
open-strip zero strictly between the two heights contributes its full order. -/
public theorem rectangleIntegral_completedZeta_logDeriv {a u v : ℝ}
    (ha : 1 < a) (hu : u < 0) (hv : 0 < v)
    (hboundary : ∀ ρ : criticalStripZetaZeros, (ρ : ℂ).im ≠ u ∧ (ρ : ℂ).im ≠ v)
    {Φ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ (Icc (1 - a) a ×ℂ Icc u v)) :
    rectangleIntegral (1 - a) a u v (fun s ↦ Φ s * logDeriv completedRiemannZeta s) =
      (2 * Real.pi * I) * (-Φ 0 - Φ 1 +
        ∑ ρ ∈ (criticalStripZetaZeros_boundedIm_finite u v).toFinset,
          (zetaZeroOrder ρ : ℂ) * Φ (ρ : ℂ)) := by
  classical
  -- Enumerate the distinct zeros and adjoin the two poles without duplication.
  let F := (criticalStripZetaZeros_boundedIm_finite u v).toFinset
  let E : criticalStripZetaZeros ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  let Z : Finset ℂ := insert 0 (insert 1 (F.map E))
  let k (z : ℂ) : ℂ := if h : z ∈ criticalStripZetaZeros then
    (zetaZeroOrder ⟨z, h⟩ : ℂ) * Φ z else -Φ z
  have hleft : 1 - a < 0 := by linarith
  have hzero : (0 : ℂ) ∉ criticalStripZetaZeros := fun h ↦ by
    simpa using (mem_criticalStripZetaZeros.mp h).2.1
  have hone : (1 : ℂ) ∉ criticalStripZetaZeros := fun h ↦ by
    simpa using (mem_criticalStripZetaZeros.mp h).2.2
  have hmap (ρ : criticalStripZetaZeros) : (ρ : ℂ) ∈ F.map E ↔
      u < (ρ : ℂ).im ∧ (ρ : ℂ).im < v := by
    change E ρ ∈ F.map E ↔ _
    rw [Finset.mem_map', Set.Finite.mem_toFinset]
    rfl
  have hinterior : ∀ z ∈ Z, z ∈ Ioo (1 - a) a ×ℂ Ioo u v := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact mem_reProdIm.mpr ⟨by simp [hleft, zero_lt_one.trans ha], by simp [hu, hv]⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact mem_reProdIm.mpr ⟨by simp [hleft.trans zero_lt_one, ha], by simp [hu, hv]⟩
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨_, hp, hl⟩ := mem_criticalStripZetaZeros.mp ρ.property
    exact mem_reProdIm.mpr ⟨⟨hleft.trans hp, hl.trans ha⟩,
      (hmap ρ).mp (Finset.mem_map.mpr ⟨ρ, hρ, rfl⟩)⟩
  -- Reflection and right-half-plane nonvanishing exclude any further singularities.
  have hregular : ∀ w ∈ (Icc (1 - a) a ×ℂ Icc u v) \ (Z : Set ℂ),
      AnalyticAt ℂ (fun s ↦ Φ s * logDeriv completedRiemannZeta s) w := by
    intro w hw
    have hw₀ : w ≠ 0 := fun h ↦ hw.2 (Finset.mem_insert.mpr (Or.inl h))
    have hw₁ : w ≠ 1 := fun h ↦
      hw.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h))))
    have hΛ : completedRiemannZeta w ≠ 0 := by
      intro hz
      let ρ : criticalStripZetaZeros := ⟨w,
        (completedZeta_eq_zero_iff_mem_criticalStripZetaZeros hw₀ hw₁).mp hz⟩
      have hi := (mem_reProdIm.mp hw.1).2
      obtain ⟨hne₁, hne₂⟩ := hboundary ρ
      exact hw.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        ((hmap ρ).mpr ⟨hi.1.lt_of_ne hne₁.symm, hi.2.lt_of_ne hne₂⟩)))
    have han := analyticAt_completedZeta hw₀ hw₁
    exact (hΦ w hw.1).mul (han.deriv.div han hΛ)
  -- Apply the tested simple principal parts, not a higher-pole residue factorization.
  have hparts : ∀ z ∈ Z, ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧
      (fun s ↦ Φ s * logDeriv completedRiemannZeta s) =ᶠ[𝓝[≠] z]
        fun w ↦ k z * (w - z)⁻¹ + H w := by
    intro z hz
    obtain ⟨hre, him⟩ := mem_reProdIm.mp (hinterior z hz)
    have ht := hΦ z (mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hre, Ioo_subset_Icc_self him⟩)
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simpa only [k, dite_eq_right hzero, div_eq_mul_inv] using
        completedZeta_tested_pole_principalPart (Or.inl rfl) ht
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simpa only [k, dite_eq_right hone, div_eq_mul_inv] using
        completedZeta_tested_pole_principalPart (Or.inr rfl) ht
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_map.mp hz
    simpa only [k, E, Function.Embedding.coeFn_mk, dite_eq_left ρ.property, div_eq_mul_inv] using
      completedZeta_tested_zero_principalPart ρ ht
  have hnot (z : ℂ) (hz : z ∉ criticalStripZetaZeros) : z ∉ F.map E := by
    rintro h
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_map.mp h
    exact hz ρ.property
  rw [rectangleIntegral_eq_sum_simpleResidues (hleft.trans (zero_lt_one.trans ha)) (hu.trans hv)
    hinterior hregular hparts]
  have hzeroZ : (0 : ℂ) ∉ insert 1 (F.map E) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact zero_ne_one h
    · exact hnot 0 hzero h
  rw [show Z = insert 0 (insert 1 (F.map E)) from rfl, Finset.sum_insert hzeroZ,
    Finset.sum_insert (hnot 1 hone), Finset.sum_map]
  simp only [k, dite_eq_right hzero, dite_eq_right hone, E, Function.Embedding.coeFn_mk,
    Subtype.coe_prop, dite_true]
  rw [← add_assoc, ← sub_eq_add_neg]

end Masullo
