module

public import Props.RectangleResidue
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Analytic.Order
import Lemmas.TestedLogDeriv

/-! # Signed residues of the tested, twice pole-cleared function

For (B.3.2.3), p. 606, apply the finite rectangle with the
counterclockwise orientation of Figure 3, p. 605. The two negative
terms in (B.4.2.2), p. 614, require actual simple poles of the
completed function. Below, it is the nonzero numerator at each of
0 and 1 that ensures order −1. The other coefficients use full zero
orders, not just the set of zero locations. Source reading provisional
(pinned Markdown and numbered PDF layout).
-/

open Complex Filter Set
open scoped Topology

namespace Masullo

private theorem polePolynomial_order (z : ℂ) :
    meromorphicOrderAt (fun s : ℂ ↦ (s - 1) * s) z =
      if z = 0 ∨ z = 1 then 1 else 0 := by
  split_ifs with hz
  · rcases hz with rfl | rfl
    · have ha : AnalyticAt ℂ (· - (1 : ℂ)) 0 := by fun_prop
      change meromorphicOrderAt ((· - (1 : ℂ)) * id) 0 = 1
      rw [meromorphicOrderAt_mul_of_ne_zero ha (by simp),
        meromorphicOrderAt_id]
    · rw [show (fun s : ℂ ↦ (s - 1) * s) = id * (· - (1 : ℂ)) from funext fun _ ↦ mul_comm ..,
        meromorphicOrderAt_mul_of_ne_zero analyticAt_id (by simp : (1 : ℂ) ≠ 0),
        meromorphicOrderAt_id_sub_const]
  · have h : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1) * s) z := by fun_prop
    rw [h.meromorphicOrderAt_eq, h.analyticOrderAt_eq_zero.mpr
      (mul_ne_zero (sub_ne_zero.mpr (fun h₁ ↦ hz (.inr h₁))) (fun h₀ ↦ hz (.inl h₀)))]
    rfl

private theorem order_of_poleCleared {L H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s)
    (z : ℂ) : meromorphicOrderAt L z = meromorphicOrderAt H z -
      (if z = 0 ∨ z = 1 then 1 else 0) := by
  let q (s : ℂ) := (s - 1) * s
  have hne (p : ℂ) : ∀ᶠ s in 𝓝[≠] z, s ≠ p := by
    by_cases h : z = p
    · subst p; exact self_mem_nhdsWithin
    · exact (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds
  have heq : L =ᶠ[𝓝[≠] z] fun s ↦ H s / q s := by
    filter_upwards [hne 0, hne 1] with s hs₀ hs₁
    rw [hclear s hs₀ hs₁, mul_comm, mul_div_cancel_right₀ _ (mul_ne_zero (sub_ne_zero.mpr hs₁) hs₀)]
  rw [meromorphicOrderAt_congr heq]
  change meromorphicOrderAt (H / q) z = _
  rw [meromorphicOrderAt_div (hH.analyticAt z).meromorphicAt (by dsimp [q]; fun_prop),
    polePolynomial_order]

private theorem interiorZeros_finite {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h₁ : H 1 ≠ 0) (T : ℝ) :
    {z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (-T) T | H z = 0}.Finite := by
  let Z : Set ℂ := H ⁻¹' {0}
  have hcod : Zᶜ ∈ Filter.codiscrete ℂ :=
    (show AnalyticOnNhd ℂ H univ from fun z _ ↦ hH.analyticAt z).preimage_zero_mem_codiscrete h₁
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcod
  have hK : IsCompact (Icc (-1 : ℝ) 2 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  refine ((hK.inter_right hclosed).finite (hdisc.mono inter_subset_right)).subset fun z hz ↦ ⟨?_, hz.2⟩
  obtain ⟨hre, him⟩ := mem_reProdIm.mp hz.1
  exact mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hre, Ioo_subset_Icc_self him⟩

/-- Finite counterclockwise contour, with the exact interior zeros of
`H` (equivalently the ordinary zeros of `L`) and both negative pole terms.
Only a boundary nonvanishing hypothesis is needed at this finite height. -/
public theorem rectangleIntegral_logDeriv_of_two_poles {L H : ℂ → ℂ} {T : ℝ}
    (hT : 0 < T) (hL : Meromorphic L) (hH : Differentiable ℂ H)
    (hclear : ∀ s, s ≠ 0 → s ≠ 1 → H s = (s - 1) * s * L s)
    (h₀ : H 0 ≠ 0) (h₁ : H 1 ≠ 0)
    (hbd : ∀ z ∈ (Icc (-1 : ℝ) 2 ×ℂ Icc (-T) T) \ (Ioo (-1 : ℝ) 2 ×ℂ Ioo (-T) T), L z ≠ 0) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ z ∈ Ioo (-1 : ℝ) 2 ×ℂ Ioo (-T) T ∧ H z = 0) ∧
      ∀ {Φ : ℂ → ℂ}, AnalyticOnNhd ℂ Φ univ →
        rectangleIntegral (-1) 2 (-T) T (fun s ↦ Φ s * logDeriv L s) =
          (2 * Real.pi * I) * ((∑ z ∈ Z, (analyticOrderNatAt H z : ℂ) * Φ z) - Φ 0 - Φ 1) := by
  classical
  let U : Set ℂ := Ioo (-1 : ℝ) 2 ×ℂ Ioo (-T) T
  let Z := (interiorZeros_finite hH h₁ T).toFinset
  have hZ (z : ℂ) : z ∈ Z ↔ z ∈ U ∧ H z = 0 := Set.Finite.mem_toFinset _
  let P : Finset ℂ := {0, 1}
  have hP (z : ℂ) : z ∈ P ↔ z = 0 ∨ z = 1 := by simp [P]
  have hdisj : Disjoint Z P := Finset.disjoint_left.mpr (by
    intro z hz hp
    rcases (hP z).mp hp with rfl | rfl
    · exact h₀ ((hZ 0).mp hz).2
    · exact h₁ ((hZ 1).mp hz).2)
  have hPU (z : ℂ) (hz : z ∈ P) : z ∈ U := by
    rcases (hP z).mp hz with rfl | rfl <;>
      apply mem_reProdIm.mpr <;> constructor <;>
      simp [hT, neg_lt_zero.mpr hT]
  refine ⟨Z, hZ, fun {Φ} hΦ ↦ ?_⟩
  let k (z : ℂ) := if z ∈ Z then (analyticOrderNatAt H z : ℂ) * Φ z else -Φ z
  have hI := rectangleIntegral_eq_sum_simpleResidues (Z := Z ∪ P) (k := k)
    (g := fun s ↦ Φ s * logDeriv L s) (by norm_num : (-1 : ℝ) < 2) (by linarith : -T < T) ?_ ?_ ?_
  · rw [hI, Finset.sum_union hdisj]
    congr 1
    have hz : ∑ z ∈ Z, k z = ∑ z ∈ Z, (analyticOrderNatAt H z : ℂ) * Φ z :=
      Finset.sum_congr rfl fun z hz ↦ ite_eq_left hz
    have hp : ∑ z ∈ P, k z = ∑ z ∈ P, -Φ z :=
      Finset.sum_congr rfl fun z hz ↦ ite_eq_right (fun hz' ↦ Finset.disjoint_left.mp hdisj hz' hz)
    rw [hz, hp]
    simp [P]
    ring
  · intro z hz
    exact (Finset.mem_union.mp hz).elim (fun hz ↦ ((hZ z).mp hz).1) (hPU z)
  · intro z hz
    have hnotP : z ∉ P := fun hp ↦ hz.2 (Finset.mem_union_right _ hp)
    have hz₀ : z ≠ 0 := fun h ↦ hnotP ((hP z).mpr (.inl h))
    have hz₁ : z ≠ 1 := fun h ↦ hnotP ((hP z).mpr (.inr h))
    have hne : L z ≠ 0 := by
      by_cases hu : z ∈ U
      · intro hzL
        apply hz.2
        exact Finset.mem_union_left _ ((hZ z).mpr ⟨hu, by simp [hclear z hz₀ hz₁, hzL]⟩)
      · exact hbd z ⟨hz.1, hu⟩
    -- The same quotient is analytic at ordinary points, not merely meromorphic.
    have heq : (fun s ↦ H s / ((s - 1) * s)) =ᶠ[𝓝 z] L := by
      filter_upwards [eventually_ne_nhds hz₀, eventually_ne_nhds hz₁] with s hs₀ hs₁
      rw [hclear s hs₀ hs₁, mul_div_cancel_left₀ _ (mul_ne_zero (sub_ne_zero.mpr hs₁) hs₀)]
    have hq : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1) * s) z := by fun_prop
    have han : AnalyticAt ℂ L z :=
      ((hH.analyticAt z).div hq (mul_ne_zero (sub_ne_zero.mpr hz₁) hz₀)).congr heq
    exact (hΦ z (mem_univ z)).mul (han.deriv.div han hne)
  · intro z hz
    have hOrd := order_of_poleCleared hH hclear z
    rcases Finset.mem_union.mp hz with hzz | hzp
    · have hnotP := Finset.disjoint_left.mp hdisj hzz
      have han := hH.analyticAt z
      have hfin : analyticOrderAt H z ≠ ⊤ := fun ht ↦ h₁ (congrFun
        ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w ↦ hH.analyticAt w)).mp ht) 1)
      rw [ite_eq_right (fun hp ↦ hnotP ((hP z).mpr hp)), sub_zero, han.meromorphicOrderAt_eq,
        ← Nat.cast_analyticOrderNatAt hfin, ENat.map_natCast] at hOrd
      simpa only [k, ite_eq_left hzz, Int.cast_natCast, div_eq_mul_inv] using
        logDeriv_weighted_principalPart (hL z) hOrd (hΦ z (mem_univ z))
    · have hnotZ : z ∉ Z := fun hz' ↦ Finset.disjoint_left.mp hdisj hz' hzp
      have hne : H z ≠ 0 := by rcases (hP z).mp hzp with rfl | rfl <;> assumption
      have han := hH.analyticAt z
      have hh : meromorphicOrderAt H z = 0 := by
        rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr hne]
        rfl
      rw [ite_eq_left ((hP z).mp hzp), hh] at hOrd
      have hOrd' : meromorphicOrderAt L z = ((-1 : ℤ) : WithTop ℤ) := by simpa using hOrd
      simpa only [k, ite_eq_right hnotZ, Int.cast_neg, Int.cast_one, neg_one_mul, div_eq_mul_inv] using
        logDeriv_weighted_principalPart (hL z) hOrd' (hΦ z (mem_univ z))

end Masullo
