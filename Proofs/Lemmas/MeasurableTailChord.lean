module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The measurable positive-tail chord allowance

Source: `9d0e1e0:.godel/bob/joint-tail-deletion-33.md:86–112`, in particular
lines 102–108 (the chord and trapezoid step). The same argument is at lines
106–112 at scan pin `f8c831a3e7afbcdd3488a3ad51afa8cea6e9fc99`.
Owning check session: `01a20e06-2914-72b5-a0f3-35d7c4cdf9e8`.

Scope: one closed cell with a measurable family of probability laws on `[0,1]`.
For the source take `g(t,u) = t exp(-t) (u - U*) - a(t) (X(u) - A*) -
b(t) (T(X(u)) - B*)`, keeping the reference moments fixed and using the same
atom `u` in all terms. Take `L` and `R` to bound the full atom scores at the
endpoints, and `C` to bound the Lipschitz constant of the time derivative of
each fixed-atom score. Second-derivative breakpoints are allowed. The source's
measurable score and integrable time envelope imply joint integrability: the
composition-product measure has the cell's Lebesgue measure as its first
marginal, so a majorizing function of time alone has the same integral there.
Neither computation of the source's price and derivative bounds nor summation
over cells and the remote remainder is part of this lemma.
-/

open Set MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal

namespace Masullo.MeasurableTailChord

private noncomputable def upperPrice (l r L R C t : ℝ) : ℝ :=
  (r - t) / (r - l) * L + (t - l) / (r - l) * R + C * (r - l) ^ 2 / 8

-- Adding a quadratic makes the derivative monotone without differentiating it.
private theorem le_upperPrice {l r L R : ℝ} (hlr : l < r) {C : ℝ≥0} {f d : ℝ → ℝ}
    (hf : ∀ t ∈ Icc l r, HasDerivWithinAt f (d t) (Icc l r) t)
    (hd : LipschitzOnWith C d (Icc l r)) (hL : f l ≤ L) (hR : f r ≤ R)
    {t : ℝ} (ht : t ∈ Icc l r) : f t ≤ upperPrice l r L R C t := by
  let c : ℝ := C
  let q (s : ℝ) := (c / 2) * (s - l) ^ 2
  have hq (s : ℝ) : HasDerivAt q (c * (s - l)) s := by
    have hs : HasDerivAt (fun x : ℝ ↦ x - l) 1 s := (hasDerivAt_id s).sub_const l
    convert ((hs.pow 2).const_mul (c / 2)) using 1
    ring
  have hF (s : ℝ) (hs : s ∈ Icc l r) :
      HasDerivWithinAt (fun x ↦ f x + q x) (d s + c * (s - l)) (Icc l r) s :=
    (hf s hs).add (hq s).hasDerivWithinAt
  have hD (s : ℝ) (hs : s ∈ interior (Icc l r)) :
      HasDerivAt (fun x ↦ f x + q x) (d s + c * (s - l)) s :=
    (hF s (interior_subset hs)).hasDerivAt (mem_interior_iff_mem_nhds.mp hs)
  have hconv : ConvexOn ℝ (Icc l r) (fun x ↦ f x + q x) := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc l r)
    · exact fun s hs ↦ (hF s hs).continuousWithinAt
    · exact fun s hs ↦ (hD s hs).differentiableAt.differentiableWithinAt
    · intro x hx y hy hxy
      rw [(hD x hx).deriv, (hD y hy).deriv]
      have hdist : |d x - d y| ≤ c * (y - x) := by
        simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using
          hd.dist_le_mul x (interior_subset hx) y (interior_subset hy)
      have hdiff := (le_abs_self _).trans hdist
      nlinarith only [hdiff]
  let a := (r - t) / (r - l)
  let b := (t - l) / (r - l)
  have hh : 0 < r - l := sub_pos.mpr hlr
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr ht.2) hh.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr ht.1) hh.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hh.ne']
    ring
  have hcomb : a * l + b * r = t := by
    dsimp [a, b]
    field_simp [hh.ne']
    ring
  have hchord := hconv.2 (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le) ha hb hab
  simp only [smul_eq_mul, mul_add] at hchord
  rw [hcomb] at hchord
  have herr : a * q l + b * q r - q t = c * (t - l) * (r - t) / 2 := by
    dsimp [a, b, q]
    field_simp [hh.ne']
    ring
  have hprod : (t - l) * (r - t) ≤ (r - l) ^ 2 / 4 := by
    nlinarith only [sq_nonneg ((t - l) - (r - t))]
  have hbudget : c * (t - l) * (r - t) / 2 ≤ c * (r - l) ^ 2 / 8 := by
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ c from C.coe_nonneg)
    nlinarith only [h]
  have hprices := add_le_add (mul_le_mul_of_nonneg_left hL ha) (mul_le_mul_of_nonneg_left hR hb)
  change f t ≤ a * L + b * R + c * (r - l) ^ 2 / 8
  calc
    f t ≤ a * f l + b * f r + (a * q l + b * q r - q t) := by linarith only [hchord]
    _ ≤ a * L + b * R + c * (r - l) ^ 2 / 8 :=
      add_le_add hprices (by rw [herr]; exact hbudget)

private theorem continuous_upperPrice (l r L R C : ℝ) : Continuous (upperPrice l r L R C) := by
  unfold upperPrice
  fun_prop

private theorem integral_upperPrice {l r : ℝ} (hlr : l < r) (L R C : ℝ) :
    (∫ t in Icc l r, upperPrice l r L R C t) =
      (r - l) * (L + R) / 2 + C * (r - l) ^ 3 / 8 := by
  let h := r - l
  let A (t : ℝ) := -(L / h / 2) * (r - t) ^ 2 + (R / h / 2) * (t - l) ^ 2 +
    (C * h ^ 2 / 8) * (t - l)
  have hA (t : ℝ) : HasDerivAt A (upperPrice l r L R C t) t := by
    have hs : HasDerivAt (fun x : ℝ ↦ x - l) 1 t := (hasDerivAt_id t).sub_const l
    have hr : HasDerivAt (fun x : ℝ ↦ r - x) (-1) t := (hasDerivAt_id t).const_sub r
    convert (((hr.pow 2).const_mul (-(L / h / 2))).add
      ((hs.pow 2).const_mul (R / h / 2))).add (hs.const_mul (C * h ^ 2 / 8)) using 1
    dsimp [upperPrice, h]
    ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hA t)
      ((continuous_upperPrice l r L R C).intervalIntegrable l r)]
  dsimp [A, h]
  field_simp [sub_ne_zero.mpr hlr.ne']
  ring

/-- For each fixed atom, a `C`-Lipschitz derivative gives a uniform allowance
`C * (r - l)^2 / 8` over the chord of the two endpoint upper prices. Integrating
against the law at the current time and then over the cell gives the trapezoid
price plus `C * (r - l)^3 / 8`. Joint integrability suffices; the law need not
be continuous, and no second time derivative of the score is assumed. -/
public theorem integral_score_le {l r : ℝ} (hlr : l < r)
    (ν : Kernel (Icc l r) (Icc (0 : ℝ) 1)) [IsMarkovKernel ν]
    {g dg : ℝ → Icc (0 : ℝ) 1 → ℝ} {C : ℝ≥0} {L R : ℝ}
    (hg : Integrable (fun p : Icc l r × Icc (0 : ℝ) 1 ↦ g p.1 p.2)
      ((volume.comap Subtype.val) ⊗ₘ ν))
    (hderiv : ∀ u, ∀ t ∈ Icc l r, HasDerivWithinAt (fun s ↦ g s u) (dg t u) (Icc l r) t)
    (hlip : ∀ u, LipschitzOnWith C (fun t ↦ dg t u) (Icc l r))
    (hL : ∀ u, g l u ≤ L) (hR : ∀ u, g r u ≤ R) :
    (∫ t : Icc l r, (∫ u, g t u ∂ν t) ∂(volume.comap Subtype.val)) ≤
      (r - l) * (L + R) / 2 + (C : ℝ) * (r - l) ^ 3 / 8 := by
  let μ : Measure (Icc l r) := volume.comap Subtype.val
  have : IsFiniteMeasure μ := by
    constructor
    dsimp only [μ]
    rw [Measure.comap_apply Subtype.val Subtype.coe_injective
      (fun _ hs ↦ measurableSet_Icc.subtype_image hs) _ MeasurableSet.univ]
    simp only [Set.image_univ, Subtype.range_coe, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  let P := upperPrice l r L R C
  let Pcell : Icc l r → ℝ := fun t ↦ P t
  have hP : Integrable Pcell μ :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
      (continuous_upperPrice l r L R C).integrableOn_Icc
  have hmarg : (μ ⊗ₘ ν).map Prod.fst = μ := Measure.fst_compProd μ ν
  have hPmap : Integrable Pcell ((μ ⊗ₘ ν).map Prod.fst) := by rwa [hmarg]
  have hPjoint := hPmap.comp_measurable measurable_fst
  calc
    (∫ t : Icc l r, (∫ u, g t u ∂ν t) ∂μ) =
        ∫ p, g p.1 p.2 ∂(μ ⊗ₘ ν) := (Measure.integral_compProd hg).symm
    _ ≤ ∫ p, Pcell p.1 ∂(μ ⊗ₘ ν) :=
      integral_mono hg hPjoint fun p ↦
        le_upperPrice hlr (hderiv p.2) (hlip p.2) (hL p.2) (hR p.2) p.1.property
    _ = ∫ t, Pcell t ∂μ := by
      rw [← integral_map measurable_fst.aemeasurable hPmap.aestronglyMeasurable, hmarg]
    _ = ∫ t in Icc l r, P t := integral_subtype_comap measurableSet_Icc P
    _ = _ := integral_upperPrice hlr L R C

end Masullo.MeasurableTailChord
