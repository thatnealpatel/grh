module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Kernel.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# A Bernstein cell bound for varying measurable laws

Source: `3b6ca9d444e9:.godel/bob/measurable-negative-deletion-33.md:26–42`.
Owning check session: `01a20dea-9bff-7af6-950c-47bd0e521e1e`.

Scope: one closed cell of the negative-law upper-price argument. The three Bernstein
controls are bounded separately over the full atom interval. The interpolation and
third-derivative remainder are atomwise; the law is used only at the current time.
This does not include the source's numerical bounds or its sum over cells.
-/

open Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace Masullo.MeasurableBernsteinCell

noncomputable section

private def midpoint (l r : ℝ) : ℝ := (l + r) / 2

private def weightLeft (l r t : ℝ) : ℝ := (r - t) ^ 2 / (r - l) ^ 2
private def weightMiddle (l r t : ℝ) : ℝ := 2 * (t - l) * (r - t) / (r - l) ^ 2
private def weightRight (l r t : ℝ) : ℝ := (t - l) ^ 2 / (r - l) ^ 2

private def bernstein (l r L M U t : ℝ) : ℝ :=
  L * weightLeft l r t + M * weightMiddle l r t + U * weightRight l r t

private def quadratic (l r : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  bernstein l r (f l) (2 * f (midpoint l r) - (f l + f r) / 2) (f r)

private def nodal (l r t : ℝ) : ℝ := (t - l) * (t - midpoint l r) * (t - r)

private theorem quadratic_nodes {l r : ℝ} (hlr : l < r) (f : ℝ → ℝ) :
    quadratic l r f l = f l ∧ quadratic l r f (midpoint l r) = f (midpoint l r) ∧
      quadratic l r f r = f r := by
  have hn : r - l ≠ 0 := sub_ne_zero.mpr hlr.ne'
  constructor
  · simp [quadratic, bernstein, weightLeft, weightMiddle, weightRight, hn]
  constructor
  · unfold quadratic bernstein weightLeft weightMiddle weightRight
    generalize f (midpoint l r) = F
    unfold midpoint
    field_simp
    ring
  · simp [quadratic, bernstein, weightLeft, weightMiddle, weightRight, hn]

private theorem contDiff_bernstein (l r L M U : ℝ) : ContDiff ℝ 3 (bernstein l r L M U) := by
  unfold bernstein weightLeft weightMiddle weightRight
  fun_prop

private theorem contDiff_nodal (l r : ℝ) : ContDiff ℝ 3 (nodal l r) := by
  unfold nodal
  fun_prop

private theorem third_deriv_cubic (a b c d x : ℝ) :
    iteratedDeriv 3 (fun t : ℝ ↦ a * t ^ 3 + b * t ^ 2 + c * t ^ 1 + d) x = 6 * a := by
  repeat rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow, iteratedDeriv_const]
  norm_num [Nat.descFactorial]
  ring

private theorem third_deriv_bernstein (l r L M U x : ℝ) :
    iteratedDeriv 3 (bernstein l r L M U) x = 0 := by
  let D := (r - l) ^ 2
  have heq : bernstein l r L M U = fun t ↦
      0 * t ^ 3 + ((L - 2 * M + U) / D) * t ^ 2 +
        ((-2 * r * L + 2 * (l + r) * M - 2 * l * U) / D) * t ^ 1 +
          (r ^ 2 * L - 2 * l * r * M + l ^ 2 * U) / D := by
    funext t
    unfold bernstein weightLeft weightMiddle weightRight
    dsimp only [D]
    ring
  rw [heq, third_deriv_cubic, mul_zero]

private theorem third_deriv_nodal (l r x : ℝ) : iteratedDeriv 3 (nodal l r) x = 6 := by
  let m := midpoint l r
  have heq : nodal l r = fun t ↦
      1 * t ^ 3 + (-(l + m + r)) * t ^ 2 + (l * m + l * r + m * r) * t ^ 1 +
        (-(l * m * r)) := by
    funext t
    change (t - l) * (t - m) * (t - r) = _
    ring
  rw [heq, third_deriv_cubic, mul_one]

-- The closed cell is needed for the first Rolle step; all later Rolle intervals
-- are strictly in the interior, where ordinary derivatives are continuous.
private theorem continuousOn_iterated {l r : ℝ} {g : ℝ → ℝ} {n : ℕ}
    (hg : ContDiffOn ℝ n g (Ioo l r)) : ContinuousOn (iteratedDeriv n g) (Ioo l r) := by
  apply (hg.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ioo l r)).congr
  intro x hx
  exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo l r)
    (hg.contDiffAt (isOpen_Ioo.mem_nhds hx)) hx).symm

private theorem third_deriv_zero_of_four_zeros {l r p q s u : ℝ} {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 3 g (Icc l r)) (hl : l ≤ p) (hpq : p < q) (hqs : q < s)
    (hsu : s < u) (hu : u ≤ r) (hp : g p = 0) (hq : g q = 0) (hs : g s = 0)
    (hu' : g u = 0) : ∃ z ∈ Ioo l r, iteratedDeriv 3 g z = 0 := by
  have roll {a b : ℝ} (ha : l ≤ a) (hb : b ≤ r) (hab : a < b) (he : g a = g b) :
      ∃ c ∈ Ioo a b, iteratedDeriv 1 g c = 0 := by
    rw [iteratedDeriv_succ (n := 0), iteratedDeriv_zero]
    exact exists_deriv_eq_zero hab (hg.continuousOn.mono (Icc_subset_Icc ha hb)) he
  obtain ⟨x, hx, hx0⟩ := roll hl (hqs.le.trans (hsu.le.trans hu)) hpq (hp.trans hq.symm)
  obtain ⟨y, hy, hy0⟩ := roll (hl.trans hpq.le) (hsu.le.trans hu) hqs (hq.trans hs.symm)
  obtain ⟨z, hz, hz0⟩ := roll (hl.trans (hpq.le.trans hqs.le)) hu hsu (hs.trans hu'.symm)
  have hxl : l < x := hl.trans_lt hx.1
  have hzr : z < r := hz.2.trans_le hu
  have hxy := hx.2.trans hy.1
  have hyz := hy.2.trans hz.1
  have hg' := hg.mono Ioo_subset_Icc_self
  have hcont1 : ContinuousOn (iteratedDeriv 1 g) (Ioo l r) :=
    continuousOn_iterated (hg'.of_le (by norm_num))
  have roll' {a b : ℝ} (ha : l < a) (hb : b < r) (hab : a < b)
      (he : iteratedDeriv 1 g a = iteratedDeriv 1 g b) :
      ∃ c ∈ Ioo a b, iteratedDeriv 2 g c = 0 := by
    rw [iteratedDeriv_succ (n := 1)]
    exact exists_deriv_eq_zero hab (hcont1.mono (Icc_subset_Ioo ha hb)) he
  obtain ⟨v, hv, hv0⟩ := roll' hxl (hyz.trans hzr) hxy (hx0.trans hy0.symm)
  obtain ⟨w, hw, hw0⟩ := roll' (hxl.trans hxy) hzr hyz (hy0.trans hz0.symm)
  have hcont2 : ContinuousOn (iteratedDeriv 2 g) (Ioo l r) :=
    continuousOn_iterated (hg'.of_le (by norm_num))
  have hvl := hxl.trans hv.1
  have hwr := hw.2.trans hzr
  obtain ⟨t, ht, ht0⟩ := exists_deriv_eq_zero (hv.2.trans hw.1)
    (hcont2.mono (Icc_subset_Ioo hvl hwr)) (hv0.trans hw0.symm)
  exact ⟨t, ⟨hvl.trans ht.1, ht.2.trans hwr⟩, by rwa [iteratedDeriv_succ (n := 2)]⟩

private theorem abs_quadratic_error_le {l r R : ℝ} {f : ℝ → ℝ} (hlr : l < r)
    (hf : ContDiffOn ℝ 3 f (Icc l r))
    (hR : ∀ z ∈ Ioo l r, |iteratedDeriv 3 f z| ≤ R) {t : ℝ} (ht : t ∈ Icc l r) :
    |f t - quadratic l r f t| ≤ (R / 6) * |nodal l r t| := by
  let m := midpoint l r
  have hlm : l < m := by dsimp [m, midpoint]; linarith
  have hmr : m < r := by dsimp [m, midpoint]; linarith
  obtain ⟨hql, hqm, hqr⟩ := quadratic_nodes hlr f
  by_cases htl : t = l
  · subst t
    simp [hql, nodal]
  by_cases htm : t = m
  · subst t
    simp [m, hqm, nodal]
  by_cases htr : t = r
  · subst t
    simp [hqr, nodal]
  let q := quadratic l r f
  let K := (f t - q t) / nodal l r t
  let Q : ℝ → ℝ := fun s ↦ q s + K * nodal l r s
  let g : ℝ → ℝ := fun s ↦ f s - Q s
  have hN : nodal l r t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr htl) (sub_ne_zero.mpr htm)) (sub_ne_zero.mpr htr)
  have hq : ContDiff ℝ 3 q := contDiff_bernstein ..
  have hkn : ContDiff ℝ 3 (fun s ↦ K * nodal l r s) :=
    contDiff_const.mul (contDiff_nodal l r)
  have hQ : ContDiff ℝ 3 Q := hq.add hkn
  have hg : ContDiffOn ℝ 3 g (Icc l r) := hf.sub hQ.contDiffOn
  have hgl : g l = 0 := by simp [g, Q, q, hql, nodal]
  have hgm : g m = 0 := by simp [g, Q, q, m, hqm, nodal]
  have hgr : g r = 0 := by simp [g, Q, q, hqr, nodal]
  have hgt : g t = 0 := by
    dsimp only [g, Q, K]
    rw [div_mul_cancel₀ _ hN]
    ring
  have hlt : l < t := lt_of_le_of_ne ht.1 (Ne.symm htl)
  have htr' : t < r := lt_of_le_of_ne ht.2 htr
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Ioo l r, iteratedDeriv 3 g z = 0 := by
    rcases lt_or_gt_of_ne htm with h | h
    · exact third_deriv_zero_of_four_zeros hg le_rfl hlt h hmr le_rfl hgl hgt hgm hgr
    · exact third_deriv_zero_of_four_zeros hg le_rfl hlm h htr' le_rfl hgl hgm hgt hgr
  have hzQ : iteratedDeriv 3 Q z = 6 * K := by
    dsimp only [Q]
    rw [iteratedDeriv_fun_add hq.contDiffAt hkn.contDiffAt,
      show iteratedDeriv 3 q z = 0 from third_deriv_bernstein ..,
      iteratedDeriv_const_mul_field, third_deriv_nodal]
    ring
  have heq : iteratedDeriv 3 f z = 6 * K := by
    have hzf := (hf.mono Ioo_subset_Icc_self).contDiffAt (isOpen_Ioo.mem_nhds hz)
    change iteratedDeriv 3 (fun s ↦ f s - Q s) z = 0 at hz0
    rwa [iteratedDeriv_fun_sub hzf hQ.contDiffAt, hzQ, sub_eq_zero] at hz0
  have hK : |K| ≤ R / 6 := by
    calc
      |K| = |iteratedDeriv 3 f z| / 6 := by
        rw [heq, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (6 : ℝ))]
        ring
      _ ≤ R / 6 := div_le_div_of_nonneg_right (hR z hz) (by norm_num)
  change |f t - q t| ≤ _
  calc
    |f t - q t| = |K| * |nodal l r t| := by
      rw [← abs_mul, show K * nodal l r t = _ from div_mul_cancel₀ _ hN]
    _ ≤ (R / 6) * |nodal l r t| := mul_le_mul_of_nonneg_right hK (abs_nonneg _)

-- The absolute nodal product has opposite signs on the two half-cells.
private theorem integral_abs_nodal {l r : ℝ} (hlr : l < r) :
    (∫ t in l..r, |nodal l r t|) = (r - l) ^ 4 / 32 := by
  let m := midpoint l r
  let h := r - l
  have hlm : l ≤ m := by dsimp [m, midpoint]; linarith
  have hmr : m ≤ r := by dsimp [m, midpoint]; linarith
  have hc : Continuous (nodal l r) := (contDiff_nodal l r).continuous
  let A (t : ℝ) := (t - l) ^ 4 / 4 - h * (t - l) ^ 3 / 2 + h ^ 2 * (t - l) ^ 2 / 4
  have hA (t : ℝ) : HasDerivAt A (nodal l r t) t := by
    have hs : HasDerivAt (fun u : ℝ ↦ u - l) 1 t := (hasDerivAt_id t).sub_const l
    convert (((hs.pow 4).div_const 4).sub (((hs.pow 3).const_mul h).div_const 2)).add
      (((hs.pow 2).const_mul (h ^ 2)).div_const 4) using 1
    dsimp [A, h, nodal, midpoint]
    ring
  have hFTC (a b : ℝ) : (∫ t in a..b, nodal l r t) = A b - A a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hA t) (hc.intervalIntegrable a b)
  have hleft : (∫ t in l..m, |nodal l r t|) = ∫ t in l..m, nodal l r t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hlm]
    intro t ht
    exact abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.1) (sub_nonpos.mpr ht.2))
      (sub_nonpos.mpr (ht.2.trans hmr)))
  have hright : (∫ t in m..r, |nodal l r t|) = ∫ t in m..r, -nodal l r t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hmr]
    intro t ht
    exact abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sub_nonneg.mpr (hlm.trans ht.1)) (sub_nonneg.mpr ht.1))
      (sub_nonpos.mpr ht.2))
  calc
    (∫ t in l..r, |nodal l r t|) = (A m - A l) - (A r - A m) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hc.abs.intervalIntegrable l m)
        (hc.abs.intervalIntegrable m r), hleft, hright, intervalIntegral.integral_neg,
        hFTC l m, hFTC m r]
      simp only [sub_eq_add_neg]
    _ = (r - l) ^ 4 / 32 := by dsimp [A, h, m, midpoint]; ring

-- Linearity in the three controls also gives the integral of each weight, h/3.
private theorem integral_bernstein {l r : ℝ} (hlr : l < r) (L M U : ℝ) :
    (∫ t in l..r, bernstein l r L M U t) = (r - l) * (L + M + U) / 3 := by
  let h := r - l
  let A (t : ℝ) :=
    (L * (h ^ 2 * (t - l) - h * (t - l) ^ 2 + (t - l) ^ 3 / 3) +
      M * (h * (t - l) ^ 2 - 2 * (t - l) ^ 3 / 3) + U * ((t - l) ^ 3 / 3)) / h ^ 2
  have hA (t : ℝ) : HasDerivAt A (bernstein l r L M U t) t := by
    have hs : HasDerivAt (fun u : ℝ ↦ u - l) 1 t := (hasDerivAt_id t).sub_const l
    have hL := ((((hs.const_mul (h ^ 2)).sub ((hs.pow 2).const_mul h)).add
      ((hs.pow 3).div_const 3)).const_mul L)
    have hM := (((hs.pow 2).const_mul h).sub (((hs.pow 3).const_mul 2).div_const 3)).const_mul M
    have hU := ((hs.pow 3).div_const 3).const_mul U
    convert ((hL.add hM).add hU).div_const (h ^ 2) using 1
    dsimp [A, h, bernstein, weightLeft, weightMiddle, weightRight]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hA t)
    ((contDiff_bernstein l r L M U).continuous.intervalIntegrable l r)]
  have hn : r - l ≠ 0 := sub_ne_zero.mpr hlr.ne'
  dsimp [A, h]
  field_simp
  ring

private def envelope (l r L M U R t : ℝ) : ℝ :=
  bernstein l r L M U t + (R / 6) * |nodal l r t|

private theorem continuous_envelope (l r L M U R : ℝ) : Continuous (envelope l r L M U R) :=
  (contDiff_bernstein l r L M U).continuous.add
    (continuous_const.mul (contDiff_nodal l r).continuous.abs)

private theorem integral_envelope {l r : ℝ} (hlr : l < r) (L M U R : ℝ) :
    (∫ t in Icc l r, envelope l r L M U R t) =
      (r - l) * (L + M + U) / 3 + R * (r - l) ^ 4 / 192 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr.le]
  unfold envelope
  rw [intervalIntegral.integral_add ((contDiff_bernstein l r L M U).continuous.intervalIntegrable l r)
    ((contDiff_nodal l r).continuous.abs.intervalIntegrable l r |>.const_mul (R / 6)),
    integral_bernstein hlr, intervalIntegral.integral_const_mul, integral_abs_nodal hlr]
  ring

private theorem le_envelope {l r L M U R : ℝ} {f : ℝ → ℝ} (hlr : l < r)
    (hf : ContDiffOn ℝ 3 f (Icc l r))
    (hR : ∀ z ∈ Ioo l r, |iteratedDeriv 3 f z| ≤ R) (hL : f l ≤ L)
    (hM : 2 * f (midpoint l r) - (f l + f r) / 2 ≤ M) (hU : f r ≤ U)
    {t : ℝ} (ht : t ∈ Icc l r) : f t ≤ envelope l r L M U R t := by
  have hleft : 0 ≤ weightLeft l r t := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hright : 0 ≤ weightRight l r t := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmiddle : 0 ≤ weightMiddle l r t :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ht.1))
      (sub_nonneg.mpr ht.2)) (sq_nonneg _)
  have hquad : quadratic l r f t ≤ bernstein l r L M U t :=
    add_le_add (add_le_add (mul_le_mul_of_nonneg_right hL hleft)
      (mul_le_mul_of_nonneg_right hM hmiddle)) (mul_le_mul_of_nonneg_right hU hright)
  have herr := (le_abs_self _).trans (abs_quadratic_error_le hlr hf hR ht)
  exact (sub_le_iff_le_add'.mp herr).trans (add_le_add hquad le_rfl)

/-- A common cap on the three midpoint Bernstein controls bounds the score up to the
pointwise cubic interpolation remainder. -/
public theorem le_cap_add_nodal_error {l r C R : ℝ} {f : ℝ → ℝ} (hlr : l < r)
    (hf : ContDiffOn ℝ 3 f (Icc l r))
    (hR : ∀ z ∈ Ioo l r, |iteratedDeriv 3 f z| ≤ R)
    (hL : f l ≤ C) (hM : 2 * f ((l + r) / 2) - (f l + f r) / 2 ≤ C) (hU : f r ≤ C)
    {t : ℝ} (ht : t ∈ Icc l r) :
    f t ≤ C + (R / 6) * |(t - l) * (t - (l + r) / 2) * (t - r)| := by
  have hconst : bernstein l r C C C t = C := by
    unfold bernstein weightLeft weightMiddle weightRight
    have hn : r - l ≠ 0 := sub_ne_zero.mpr hlr.ne'
    field_simp
    ring
  simpa only [envelope, hconst, nodal, midpoint] using le_envelope hlr hf hR hL hM hU ht

-- Compare with a function of time only, integrating against the probability law at that time.
private theorem kernel_integral_le {l r : ℝ} (ν : Kernel (Icc l r) (Icc (-1 : ℝ) 1))
    [IsMarkovKernel ν] {F : Icc l r × Icc (-1 : ℝ) 1 → ℝ} (hF : Continuous F)
    {G : ℝ → ℝ} (hG : Continuous G) (hle : ∀ t x, F (t, x) ≤ G t) :
    (∫ t : Icc l r, (∫ x, F (t, x) ∂ν t) ∂(volume.comap Subtype.val)) ≤
      ∫ t in Icc l r, G t := by
  let μ : Measure (Icc l r) := volume.comap Subtype.val
  have hμ : μ univ = ENNReal.ofReal (r - l) := by
    dsimp only [μ]
    rw [Measure.comap_apply Subtype.val Subtype.coe_injective
      (fun _ hs ↦ measurableSet_Icc.subtype_image hs) _ MeasurableSet.univ]
    simp only [Set.image_univ, Subtype.range_coe, Real.volume_Icc]
  let : IsFiniteMeasure μ := ⟨by rw [hμ]; exact ENNReal.ofReal_lt_top⟩
  let : CompactSpace (Icc l r) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace (Icc (-1 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  have hbound (t : Icc l r) (x : Icc (-1 : ℝ) 1) : ‖F (t, x)‖ ≤ C :=
    hC (t, x) (mem_univ _)
  have hinner (t : Icc l r) : Integrable (fun x ↦ F (t, x)) (ν t) :=
    Integrable.of_bound (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      C (Filter.Eventually.of_forall (hbound t))
  have hmeas := hF.stronglyMeasurable.integral_kernel_prod_right' (κ := ν)
  have houter : Integrable (fun t ↦ ∫ x, F (t, x) ∂ν t) μ := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable C (Filter.Eventually.of_forall ?_)
    intro t
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ν t) (Filter.Eventually.of_forall (hbound t)))
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := l) (b := r)).exists_bound_of_continuousOn hG.continuousOn
  have hmajor : Integrable (fun t : Icc l r ↦ G t) μ :=
    Integrable.of_bound (hG.comp continuous_subtype_val).aestronglyMeasurable D
      (Filter.Eventually.of_forall fun t ↦ hD t t.property)
  rw [← integral_subtype_comap measurableSet_Icc G]
  refine integral_mono houter hmajor fun t ↦ ?_
  simpa only [integral_const, probReal_univ, one_smul] using
    (integral_mono (hinner t) (integrable_const (G t)) (hle t))

/-- The signed score of a fixed atom in Bob's negative-law upper-price argument. -/
@[expose] public def atomPayoff (a b : ℝ → ℝ) (t X : ℝ) : ℝ := -a t * X - b t * (4 * X ^ 3 - 3 * X)

/-- A uniform third-derivative bound gives the cost `R * (r - l) ^ 4 / 192` in addition
to the integrated separate Bernstein control bounds. The outer measure is Lebesgue
measure on the closed cell, written on its subtype so the kernel only needs to be
defined and measurable on that cell. -/
public theorem integral_atomPayoff_le {l r : ℝ} (hlr : l < r) {a b : ℝ → ℝ}
    (ha : ContDiffOn ℝ 3 a (Icc l r)) (hb : ContDiffOn ℝ 3 b (Icc l r))
    (ν : Kernel (Icc l r) (Icc (-1 : ℝ) 1)) [IsMarkovKernel ν] {L M U R : ℝ}
    (hthird : ∀ X ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Ioo l r,
      |iteratedDeriv 3 (fun s ↦ atomPayoff a b s X) t| ≤ R)
    (hleft : ∀ X ∈ Icc (-1 : ℝ) 1, atomPayoff a b l X ≤ L)
    (hmiddle : ∀ X ∈ Icc (-1 : ℝ) 1,
      2 * atomPayoff a b ((l + r) / 2) X - (atomPayoff a b l X + atomPayoff a b r X) / 2 ≤ M)
    (hright : ∀ X ∈ Icc (-1 : ℝ) 1, atomPayoff a b r X ≤ U) :
    (∫ t : Icc l r, (∫ X, atomPayoff a b t X ∂ν t) ∂(volume.comap Subtype.val)) ≤
      (r - l) * (L + M + U) / 3 + R * (r - l) ^ 4 / 192 := by
  let F (p : Icc l r × Icc (-1 : ℝ) 1) := atomPayoff a b p.1 p.2
  have hF : Continuous F := by
    have hat : Continuous (fun p : Icc l r × Icc (-1 : ℝ) 1 ↦ a p.1) :=
      ha.continuousOn.domRestrict.comp continuous_fst
    have hbt : Continuous (fun p : Icc l r × Icc (-1 : ℝ) 1 ↦ b p.1) :=
      hb.continuousOn.domRestrict.comp continuous_fst
    have hx : Continuous (fun p : Icc l r × Icc (-1 : ℝ) 1 ↦ (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (hat.neg.mul hx).sub (hbt.mul ((continuous_const.mul (hx.pow 3)).sub
      (continuous_const.mul hx)))
  have hle (t : Icc l r) (X : Icc (-1 : ℝ) 1) : F (t, X) ≤ envelope l r L M U R t := by
    have hf : ContDiffOn ℝ 3 (fun s ↦ atomPayoff a b s X) (Icc l r) :=
      (ha.neg.mul contDiffOn_const).sub (hb.mul contDiffOn_const)
    exact le_envelope hlr hf (hthird X X.property) (hleft X X.property)
      (hmiddle X X.property) (hright X X.property) t.property
  exact (kernel_integral_le ν hF (continuous_envelope l r L M U R) hle).trans_eq
    (integral_envelope hlr L M U R)

end

end Masullo.MeasurableBernsteinCell
