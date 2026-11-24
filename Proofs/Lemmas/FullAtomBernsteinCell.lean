module

public import Lemmas.MeasurableBernsteinCell
-- Reuse the three-control envelope and its exact integral without changing its API.
import all Lemmas.MeasurableBernsteinCell
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The full atom Bernstein cell allowance

Source: `b6766e46:.godel/bob/eight-piece-deletion-33.md:50–67` (the measurable
release bound), and `b6766e46:.godel/bob/release-costs-33.py:13–43` (mass,
Bernstein rows and allowances). The cell argument is unchanged at `fad1c055`.
Owning session: `01a20eab-a304-7e57-9eec-1f7fc75e3637`.

Scope: one closed cell on either side of zero, including cells that meet zero
at an endpoint. The two outer controls and the middle control are each bounded
on the whole atom interval `[0,1]`. The extra third-derivative allowance is
proved for the one-sided mass; only a smooth branch on the given cell is used.
The law enters as a probability kernel, with the cell's Lebesgue measure as
its outer measure. No numerical certificate or summation over cells is asserted.
-/

open Set MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Masullo.FullAtomBernsteinCell

open MeasurableBernsteinCell (atomPayoff)

noncomputable section

/-- The mass coefficient of the full score, zero on the negative half-line. -/
@[expose] public def mass (t : ℝ) : ℝ := if 0 ≤ t then t * Real.exp (-t) else 0

/-- The score `m(t) * u - a(t) * X - b(t) * (4 * X^3 - 3 * X)`, with `X = 2 * u^2 - 1`. -/
@[expose] public def score (a b : ℝ → ℝ) (t u : ℝ) : ℝ :=
  mass t * u + atomPayoff a b t (2 * u ^ 2 - 1)

private def positiveMass (t : ℝ) : ℝ := t * Real.exp (-t)

private def cellMass (l : ℝ) : ℝ → ℝ :=
  if 0 ≤ l then positiveMass else fun _ ↦ 0

private theorem mass_eq_cellMass {l r t : ℝ} (hlr : l < r) (hcell : r ≤ 0 ∨ 0 ≤ l)
    (ht : t ∈ Icc l r) : mass t = cellMass l t := by
  rcases hcell with hr | hl
  · have hl' : ¬ 0 ≤ l := not_le.mpr (hlr.trans_le hr)
    rcases (ht.2.trans hr).eq_or_lt with rfl | ht'
    · simp [mass, cellMass, hl']
    · simp [mass, cellMass, hl', not_le.mpr ht']
  · simp [mass, cellMass, hl, hl.trans ht.1, positiveMass]

private theorem contDiff_cellMass (l : ℝ) : ContDiff ℝ 3 (cellMass l) := by
  by_cases hl : 0 ≤ l
  · rw [cellMass, ite_eq_left hl]
    unfold positiveMass
    exact contDiff_id.mul (Real.contDiff_exp.comp contDiff_id.neg)
  · rw [cellMass, ite_eq_right hl]
    exact contDiff_const

private theorem third_positiveMass (t : ℝ) :
    iteratedDeriv 3 positiveMass t = (3 - t) * Real.exp (-t) := by
  have hexp (s : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (-Real.exp (-s)) s := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg
  have h₁ (s : ℝ) : HasDerivAt positiveMass ((1 - s) * Real.exp (-s)) s := by
    unfold positiveMass
    convert (hasDerivAt_id' s).fun_mul (hexp s) using 1
    ring
  have h₂ (s : ℝ) : HasDerivAt (fun x : ℝ ↦ (1 - x) * Real.exp (-x))
      ((s - 2) * Real.exp (-s)) s := by
    convert ((hasDerivAt_id' s).const_sub 1).fun_mul (hexp s) using 1
    ring
  have h₃ (s : ℝ) : HasDerivAt (fun x : ℝ ↦ (x - 2) * Real.exp (-x))
      ((3 - s) * Real.exp (-s)) s := by
    convert ((hasDerivAt_id' s).sub_const 2).fun_mul (hexp s) using 1
    ring
  rw [iteratedDeriv_succ (n := 2), iteratedDeriv_succ (n := 1), iteratedDeriv_succ (n := 0),
    iteratedDeriv_zero, funext (fun s ↦ (h₁ s).deriv), funext (fun s ↦ (h₂ s).deriv), (h₃ t).deriv]

private theorem third_cellMass_le {l t : ℝ} (ht : l ≤ t) :
    |iteratedDeriv 3 (cellMass l) t| ≤ if 0 ≤ l then 3 * Real.exp (-l / 2) else 0 := by
  by_cases hl : 0 ≤ l
  · simp only [cellMass, ite_eq_left hl, third_positiveMass, abs_mul, abs_of_pos (Real.exp_pos _)]
    have ht0 := hl.trans ht
    have hlin : |3 - t| ≤ 3 * Real.exp (t / 2) := by
      calc
        |3 - t| ≤ 3 + t := abs_le.mpr ⟨by linarith, by linarith⟩
        _ ≤ 3 * Real.exp (t / 2) := by linarith only [ht0, Real.add_one_le_exp (t / 2)]
    calc
      |3 - t| * Real.exp (-t) ≤ (3 * Real.exp (t / 2)) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
      _ = 3 * Real.exp (-t / 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 3 * Real.exp (-l / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [ht])) (by norm_num)
  · simp [cellMass, hl]

-- Use the composition-product comparison from MeasurableTailChord with a
-- Bernstein envelope in place of the chord. Its first marginal is Lebesgue
-- measure on the cell, independently of the time variation of the kernel.
private theorem kernel_integral_le {l r : ℝ} (ν : Kernel (Icc l r) (Icc (0 : ℝ) 1))
    [IsMarkovKernel ν] {F : Icc l r × Icc (0 : ℝ) 1 → ℝ} (hF : Continuous F)
    {G : ℝ → ℝ} (hG : Continuous G) (hle : ∀ p, F p ≤ G p.1) :
    (∫ t : Icc l r, (∫ u, F (t, u) ∂ν t) ∂(volume.comap Subtype.val)) ≤
      ∫ t in Icc l r, G t := by
  let μ : Measure (Icc l r) := volume.comap Subtype.val
  have : IsFiniteMeasure μ := by
    constructor
    dsimp only [μ]
    rw [Measure.comap_apply Subtype.val Subtype.coe_injective
      (fun _ hs ↦ measurableSet_Icc.subtype_image hs) _ MeasurableSet.univ]
    simp only [Set.image_univ, Subtype.range_coe, Real.volume_Icc, ENNReal.ofReal_lt_top]
  let : CompactSpace (Icc l r) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace (Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hFi : Integrable F (μ ⊗ₘ ν) :=
    integrableOn_univ.mp (hF.continuousOn.integrableOn_compact isCompact_univ)
  let Gcell : Icc l r → ℝ := fun t ↦ G t
  have hmarg : (μ ⊗ₘ ν).map Prod.fst = μ := Measure.fst_compProd μ ν
  have hGi : Integrable Gcell ((μ ⊗ₘ ν).map Prod.fst) := by
    rw [hmarg]
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hG.integrableOn_Icc
  calc
    (∫ t : Icc l r, (∫ u, F (t, u) ∂ν t) ∂μ) = ∫ p, F p ∂(μ ⊗ₘ ν) :=
      (Measure.integral_compProd hFi).symm
    _ ≤ ∫ p, Gcell p.1 ∂(μ ⊗ₘ ν) := integral_mono hFi (hGi.comp_measurable measurable_fst) hle
    _ = ∫ t, Gcell t ∂μ := by
      rw [← integral_map measurable_fst.aemeasurable hGi.aestronglyMeasurable, hmarg]
    _ = ∫ t in Icc l r, G t := integral_subtype_comap measurableSet_Icc G

/-- The full-score cell price is the integrated three-control price plus the
third-derivative remainder. Its uniform allowance is the angular allowance `A`
plus `3 * exp (-l / 2)` on a nonnegative cell and just `A` on a negative cell.
In each control, the same atom is used in every score evaluation, but the caps
need not be attained at the same atom across different controls. -/
public theorem integral_score_le {l r : ℝ} (hlr : l < r) (hcell : r ≤ 0 ∨ 0 ≤ l)
    {a b : ℝ → ℝ} (ha : ContDiffOn ℝ 3 a (Icc l r)) (hb : ContDiffOn ℝ 3 b (Icc l r))
    (ν : Kernel (Icc l r) (Icc (0 : ℝ) 1)) [IsMarkovKernel ν] {L M U A : ℝ}
    (hangular : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Ioo l r,
      |iteratedDeriv 3 (fun s ↦ atomPayoff a b s (2 * u ^ 2 - 1)) t| ≤ A)
    (hleft : ∀ u ∈ Icc (0 : ℝ) 1, score a b l u ≤ L)
    (hmiddle : ∀ u ∈ Icc (0 : ℝ) 1,
      2 * score a b ((l + r) / 2) u - (score a b l u + score a b r u) / 2 ≤ M)
    (hright : ∀ u ∈ Icc (0 : ℝ) 1, score a b r u ≤ U) :
    (∫ t : Icc l r, (∫ u, score a b t u ∂ν t) ∂(volume.comap Subtype.val)) ≤
      (r - l) * (L + M + U) / 3 +
        (A + (if 0 ≤ l then 3 * Real.exp (-l / 2) else 0)) * (r - l) ^ 4 / 192 := by
  let R := A + (if 0 ≤ l then 3 * Real.exp (-l / 2) else 0)
  let g (t u : ℝ) := cellMass l t * u + atomPayoff a b t (2 * u ^ 2 - 1)
  have hEq {t : ℝ} (ht : t ∈ Icc l r) (u : ℝ) : score a b t u = g t u := by
    simp only [score, g, mass_eq_cellMass hlr hcell ht]
  have hA (u : ℝ) : ContDiffOn ℝ 3 (fun s ↦ atomPayoff a b s (2 * u ^ 2 - 1)) (Icc l r) :=
    (ha.neg.mul contDiffOn_const).sub (hb.mul contDiffOn_const)
  have hMass (u : ℝ) : ContDiff ℝ 3 (fun s ↦ cellMass l s * u) :=
    (contDiff_cellMass l).mul contDiff_const
  have hthird (u : Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Ioo l r) :
      |iteratedDeriv 3 (fun s ↦ g s u) t| ≤ R := by
    have hat := ((hA u).mono Ioo_subset_Icc_self).contDiffAt (isOpen_Ioo.mem_nhds ht)
    simp only [g, iteratedDeriv_fun_add (hMass u).contDiffAt hat, iteratedDeriv_mul_const_field]
    have hmu : |iteratedDeriv 3 (cellMass l) t * (u : ℝ)| ≤
        if 0 ≤ l then 3 * Real.exp (-l / 2) else 0 := by
      rw [abs_mul, abs_of_nonneg u.property.1]
      exact (mul_le_of_le_one_right (abs_nonneg _) u.property.2).trans (third_cellMass_le ht.1.le)
    refine (abs_add_le _ _).trans ?_
    dsimp only [R]
    rw [add_comm A]
    exact add_le_add hmu (hangular u u.property t ht)
  let F (p : Icc l r × Icc (0 : ℝ) 1) := g p.1 p.2
  have hF : Continuous F := by
    have ha' : Continuous (fun p : Icc l r × Icc (0 : ℝ) 1 ↦ a p.1) :=
      ha.continuousOn.domRestrict.comp continuous_fst
    have hb' : Continuous (fun p : Icc l r × Icc (0 : ℝ) 1 ↦ b p.1) :=
      hb.continuousOn.domRestrict.comp continuous_fst
    have hm' : Continuous (fun p : Icc l r × Icc (0 : ℝ) 1 ↦ cellMass l p.1) :=
      (contDiff_cellMass l).continuous.comp (continuous_subtype_val.comp continuous_fst)
    have hu' : Continuous (fun p : Icc l r × Icc (0 : ℝ) 1 ↦ (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hx : Continuous (fun p : Icc l r × Icc (0 : ℝ) 1 ↦ 2 * (p.2 : ℝ) ^ 2 - 1) :=
      (continuous_const.mul (hu'.pow 2)).sub continuous_const
    exact (hm'.mul hu').add ((ha'.neg.mul hx).sub
      (hb'.mul ((continuous_const.mul (hx.pow 3)).sub (continuous_const.mul hx))))
  let G := MeasurableBernsteinCell.envelope l r L M U R
  have hle (p : Icc l r × Icc (0 : ℝ) 1) : F p ≤ G p.1 := by
    have hl : l ∈ Icc l r := left_mem_Icc.mpr hlr.le
    have hr : r ∈ Icc l r := right_mem_Icc.mpr hlr.le
    have hm : (l + r) / 2 ∈ Icc l r := ⟨by linarith, by linarith⟩
    have hL := hleft p.2 p.2.property
    have hM := hmiddle p.2 p.2.property
    have hU := hright p.2 p.2.property
    rw [hEq hl] at hL
    rw [hEq hm, hEq hl, hEq hr] at hM
    rw [hEq hr] at hU
    exact MeasurableBernsteinCell.le_envelope hlr ((hMass p.2).contDiffOn.add (hA p.2))
      (hthird p.2) hL hM hU p.1.property
  change _ ≤ (r - l) * (L + M + U) / 3 + R * (r - l) ^ 4 / 192
  calc
    (∫ t : Icc l r, (∫ u, score a b t u ∂ν t) ∂(volume.comap Subtype.val)) =
        ∫ t : Icc l r, (∫ u, F (t, u) ∂ν t) ∂(volume.comap Subtype.val) := by
      simp only [F, hEq (Subtype.property _)]
    _ ≤ ∫ t in Icc l r, G t :=
      kernel_integral_le ν hF (MeasurableBernsteinCell.continuous_envelope ..) hle
    _ = _ := MeasurableBernsteinCell.integral_envelope hlr L M U R

end

end Masullo.FullAtomBernsteinCell
