module

public import Examples.Chi8ZeroBudget
public import Props.RectangleResidue
import Lemmas.TestedLogDeriv

/-!
# Finite endpoint residue rectangles for χ₈

The counterclockwise contour uses `Chi8Entire.Λ`, including at `0`.
It counts the distinct interior strip zeros with their full analytic orders.
No critical-line hypothesis is needed for the complex identity.
-/

open Complex Filter Set
open scoped Topology

namespace Chi8ZeroBudget

open Chi8ZeroKernel

local notation "E" => Chi8Entire.Λ
local notation "D" => logDeriv Chi8Entire.Λ

private theorem rectangleZeros_finite (a b c d : ℝ) :
    {ρ : Zero | (ρ : ℂ) ∈ Ioo a b ×ℂ Ioo c d}.Finite := by
  let Z : Set ℂ := E ⁻¹' {0}
  have hcod : Zᶜ ∈ Filter.codiscrete ℂ :=
    AnalyticOnNhd.preimage_zero_mem_codiscrete
      (fun z _ ↦ Chi8Entire.differentiable.analyticAt z) Chi8Entire.one_ne_zero
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcod
  have hK : IsCompact (Icc a b ×ℂ Icc c d) := isCompact_Icc.reProdIm isCompact_Icc
  have hfin := (hK.inter_right hclosed).finite (hdisc.mono inter_subset_right)
  refine (hfin.preimage Subtype.val_injective.injOn).subset fun ρ hρ ↦ ⟨?_, ?_⟩
  · obtain ⟨hre, him⟩ := mem_reProdIm.mp hρ
    exact mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hre, Ioo_subset_Icc_self him⟩
  · exact (Chi8Entire.zero_iff ρ).mpr ρ.property

/-- The strip zeros strictly inside the rectangle, without repetition. -/
public noncomputable def rectangleZeros (a b c d : ℝ) : Finset Zero :=
  (rectangleZeros_finite a b c d).toFinset

@[simp] public theorem mem_rectangleZeros {a b c d : ℝ} {ρ : Zero} :
    ρ ∈ rectangleZeros a b c d ↔ (ρ : ℂ) ∈ Ioo a b ×ℂ Ioo c d :=
  Set.Finite.mem_toFinset _

private theorem analyticAt_logDeriv {z : ℂ} (hz : E z ≠ 0) : AnalyticAt ℂ D z :=
  let h := Chi8Entire.differentiable.analyticAt z
  h.deriv.div h hz

private theorem div_sub_principalPart {A : ℂ → ℂ} {z : ℂ} :
    (fun s ↦ A s / (s - z)) =ᶠ[𝓝[≠] z] fun s ↦ A z * (s - z)⁻¹ + dslope A z s := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hn : s - z ≠ 0 := sub_ne_zero.mpr hs
  have he : (s - z) * dslope A z s = A s - A z := by
    simpa only [smul_eq_mul] using sub_smul_dslope A z s
  rw [mul_comm] at he
  change A s / (s - z) = A z * (s - z)⁻¹ + dslope A z s
  apply (div_eq_iff hn).2
  rw [← div_eq_mul_inv, add_mul, div_mul_cancel₀ _ hn, he]
  ring

private theorem principalPart_zero :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      (fun s ↦ D s / (s * (1 - s))) =ᶠ[𝓝[≠] (0 : ℂ)] fun s ↦ D 0 * (s - 0)⁻¹ + H s := by
  let A (s : ℂ) := D s / (1 - s)
  have ha : AnalyticAt ℂ A 0 :=
    (analyticAt_logDeriv Chi8Entire.zero_ne_zero).div (by fun_prop) (by simp)
  refine ⟨dslope A 0, ha.dslope 0, ?_⟩
  simpa only [A, sub_zero, div_div, mul_comm, div_one] using
    (div_sub_principalPart (A := A) (z := 0))

private theorem principalPart_one :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 1 ∧
      (fun s ↦ D s / (s * (1 - s))) =ᶠ[𝓝[≠] (1 : ℂ)] fun s ↦ -D 1 * (s - 1)⁻¹ + H s := by
  let A (s : ℂ) := -D s / s
  have ha : AnalyticAt ℂ A 1 :=
    (analyticAt_logDeriv Chi8Entire.one_ne_zero).neg.div analyticAt_id one_ne_zero
  refine ⟨dslope A 1, ha.dslope 1, ?_⟩
  have hfactor (s : ℂ) : s * (1 - s) = -(s * (s - 1)) := by ring
  simpa only [A, div_one, neg_div, div_div, hfactor, div_neg] using
    (div_sub_principalPart (A := A) (z := 1))

private theorem principalPart_stripZero (ρ : Zero) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H (ρ : ℂ) ∧
      (fun s ↦ D s / (s * (1 - s))) =ᶠ[𝓝[≠] (ρ : ℂ)] fun s ↦
        ((multiplicity ρ : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ)))) * (s - (ρ : ℂ))⁻¹ + H s := by
  have han := Chi8Entire.differentiable.analyticAt (ρ : ℂ)
  have hfinite : analyticOrderAt E (ρ : ℂ) ≠ ⊤ := fun ht ↦ Chi8Entire.one_ne_zero (congrFun
    ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (ρ : ℂ)
      (fun w ↦ Chi8Entire.differentiable.analyticAt w)).mp ht) 1)
  have hord : meromorphicOrderAt E (ρ : ℂ) = (multiplicity ρ : ℤ) := by
    rw [han.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hfinite, ENat.map_natCast]
    rw [analyticOrderNatAt, Chi8Entire.analyticOrderAt_eq ρ.property.1]
    rfl
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h ↦ (ne_of_gt ρ.property.1) (congrArg Complex.re h)
  have hρ1 : (ρ : ℂ) ≠ 1 := fun h ↦ (ne_of_lt ρ.property.2.1) (congrArg Complex.re h)
  have hΦ : AnalyticAt ℂ (fun s : ℂ ↦ (s * (1 - s))⁻¹) (ρ : ℂ) :=
    (show AnalyticAt ℂ (fun s : ℂ ↦ s * (1 - s)) (ρ : ℂ) by fun_prop).inv
      (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1.symm))
  simpa only [Int.cast_natCast, div_eq_mul_inv, mul_comm _ (D _)] using
    Masullo.logDeriv_weighted_principalPart han.meromorphicAt hord hΦ

/-- The normalized counterclockwise rectangle integral is `D 0 - D 1` plus the
sum of the full-order zero residues. The four strict inequalities put both
endpoints in the interior; the only other hypothesis is boundary nonvanishing. -/
public theorem rectangleIntegral_eq_endpoint_sub_add_sum {a b c d : ℝ}
    (ha : a < 0) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hbd : ∀ z ∈ (Icc a b ×ℂ Icc c d) \ (Ioo a b ×ℂ Ioo c d), E z ≠ 0) :
    Masullo.rectangleIntegral a b c d (fun s ↦ D s / (s * (1 - s))) / (2 * Real.pi * I) =
      D 0 - D 1 + ∑ ρ ∈ rectangleZeros a b c d,
        (multiplicity ρ : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ))) := by
  classical
  let U := Ioo a b ×ℂ Ioo c d
  let S := rectangleZeros a b c d
  let e : Zero ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  let Z := S.map e
  let P := insert (0 : ℂ) (insert 1 Z)
  have hz (z : ℂ) : z ∈ Z ↔ z ∈ U ∧ E z = 0 := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact ⟨mem_rectangleZeros.mp hρ, (Chi8Entire.zero_iff ρ).mpr ρ.property⟩
    · intro ⟨hu, hzero⟩
      exact ⟨⟨z, (Chi8Entire.zero_iff z).mp hzero⟩, mem_rectangleZeros.mpr hu, rfl⟩
  have h0Z : 0 ∉ Z := fun h ↦ Chi8Entire.zero_ne_zero ((hz 0).mp h).2
  have h1Z : 1 ∉ Z := fun h ↦ Chi8Entire.one_ne_zero ((hz 1).mp h).2
  have h0U : (0 : ℂ) ∈ U := by
    have hb' : 0 < b := by linarith
    simp [U, mem_reProdIm, ha, hb', hc, hd]
  have h1U : (1 : ℂ) ∈ U := by
    have ha' : a < 1 := by linarith
    simp [U, mem_reProdIm, ha', hb, hc, hd]
  let k (z : ℂ) := if z = 0 then D 0 else if z = 1 then -D 1 else
    (analyticOrderNatAt E z : ℂ) / (z * (1 - z))
  have hk (ρ : Zero) : k (e ρ) = (multiplicity ρ : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ))) := by
    have hρ0 : (ρ : ℂ) ≠ 0 := fun h ↦ (ne_of_gt ρ.property.1) (congrArg Complex.re h)
    have hρ1 : (ρ : ℂ) ≠ 1 := fun h ↦ (ne_of_lt ρ.property.2.1) (congrArg Complex.re h)
    simp only [k, e, Function.Embedding.coeFn_mk, ite_eq_right hρ0, ite_eq_right hρ1,
      analyticOrderNatAt, Chi8Entire.analyticOrderAt_eq ρ.property.1]
    rfl
  have hI := Masullo.rectangleIntegral_eq_sum_simpleResidues (Z := P) (k := k)
    (g := fun s ↦ D s / (s * (1 - s))) (show a < b by linarith) (hc.trans hd) ?_ ?_ ?_
  · have hnorm : (2 * Real.pi * I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    rw [div_eq_iff hnorm, mul_comm _ (2 * Real.pi * I), hI]
    congr 1
    rw [Finset.sum_insert (show (0 : ℂ) ∉ insert 1 Z by simp [h0Z]), Finset.sum_insert h1Z]
    have hsum : ∑ z ∈ Z, k z = ∑ ρ ∈ S,
        (multiplicity ρ : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ))) := by
      change ∑ z ∈ S.map e, k z = _
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun ρ _ ↦ hk ρ
    rw [hsum]
    simp [k, S, sub_eq_add_neg, add_assoc]
  · intro z hzP
    rcases (show z = 0 ∨ z = 1 ∨ z ∈ Z by simpa [P] using hzP) with rfl | rfl | h
    · exact h0U
    · exact h1U
    · exact ((hz z).mp h).1
  · intro z hreg
    have h0 : z ≠ 0 := fun h ↦ hreg.2 (by simp [P, h])
    have h1 : z ≠ 1 := fun h ↦ hreg.2 (by simp [P, h])
    have hne : E z ≠ 0 := by
      by_cases hu : z ∈ U
      · intro hzero
        have hzZ := (hz z).mpr ⟨hu, hzero⟩
        exact hreg.2 (by simp [P, hzZ])
      · exact hbd z ⟨hreg.1, hu⟩
    exact (analyticAt_logDeriv hne).div (by fun_prop) (mul_ne_zero h0 (sub_ne_zero.mpr h1.symm))
  · intro z hzP
    rcases (show z = 0 ∨ z = 1 ∨ z ∈ Z by simpa [P] using hzP) with rfl | rfl | h
    · simpa [k] using principalPart_zero
    · simpa [k] using principalPart_one
    · obtain ⟨ρ, _, rfl⟩ := Finset.mem_map.mp h
      rw [hk]
      exact principalPart_stripZero ρ

/-- On the critical line, the real normalized boundary integral is the finite
weight sum minus the endpoint budget. Only the interior zeros need be on the line. -/
public theorem re_rectangleIntegral_eq_sum_weight_sub_budget {a b c d : ℝ}
    (ha : a < 0) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hbd : ∀ z ∈ (Icc a b ×ℂ Icc c d) \ (Ioo a b ×ℂ Ioo c d), E z ≠ 0)
    (hline : ∀ ρ ∈ rectangleZeros a b c d, (ρ : ℂ).re = 1 / 2) :
    (Masullo.rectangleIntegral a b c d (fun s ↦ D s / (s * (1 - s))) / (2 * Real.pi * I)).re =
      (∑ ρ ∈ rectangleZeros a b c d, weight ρ) - C := by
  rw [rectangleIntegral_eq_endpoint_sub_add_sum ha hb hc hd hbd, add_re, re_sum, ← endpoint_difference]
  have hsum : ∑ ρ ∈ rectangleZeros a b c d,
      ((multiplicity ρ : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ)))).re =
      ∑ ρ ∈ rectangleZeros a b c d, weight ρ := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hconj : 1 - (ρ : ℂ) = starRingEnd ℂ (ρ : ℂ) := by
      apply Complex.ext
      · norm_num [sub_re, hline ρ hρ]
      · simp [sub_im]
    rw [hconj, mul_conj, ← Complex.sq_norm, ← ofReal_natCast, ← ofReal_div, ofReal_re]
    rfl
  rw [hsum, sub_re, sub_re]
  ring

end Chi8ZeroBudget
