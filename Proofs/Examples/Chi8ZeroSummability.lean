module

public import Examples.Chi8Origin
public import Mathlib.Analysis.Analytic.Order
import Lemmas.DirichletLFunctionGrowth
import Lemmas.DirichletRightAnchor
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.PSeries

/-! # Inverse-square summability of the conductor-eight zero divisor

On disks centered at `2 + t * I`, the right-hand anchor and polynomial growth
bound give a logarithmic Jensen estimate for the bare L-function. Bounding the
logarithm by a square root gives a `3/2`-series majorant for the inverse-square
weights in unit-height slabs. Isolation of the trivial zero at the origin
controls the denominator at low heights, without a critical-line hypothesis.
-/

open Complex Filter MeromorphicOn Metric Set
open scoped Topology

namespace Chi8Origin

local notation "L" => DirichletCharacter.LFunction χ

private theorem chi8_ne_one : χ ≠ 1 := by
  intro h
  have hc := conductor_eq
  rw [h, DirichletCharacter.conductor_one] at hc
  exact (by decide : (1 : ℕ) ≠ 8) hc

private theorem analyticAt_L (z : ℂ) : AnalyticAt ℂ L z :=
  (χ.differentiable_LFunction chi8_ne_one).analyticAt z

-- The same moving disks as in DirichletThreeResidueSummability, but we
-- retain the logarithm of the polynomial bound before estimating it.
private theorem moving_disk_jensen :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ,
      ((∑ᶠ z, divisor L (closedBall (2 + (t : ℂ) * I) 5) z : ℤ) : ℝ)
        ≤ (A + 6 * Real.log (1 + |t|)) / Real.log (6 / 5 : ℝ) := by
  obtain ⟨C, hC, hG⟩ := Masullo.exists_dirichlet_LFunction_growth_closed_halfPlane χ chi8_ne_one
  obtain ⟨b, hb, hB⟩ := Masullo.exists_dirichlet_anchor_at (show (1 : ℝ) < 2 by norm_num)
  let A := |Real.log C - Real.log b| + 6 * Real.log 14
  refine ⟨A, add_nonneg (abs_nonneg _) (by positivity), fun t ↦ ?_⟩
  let c : ℂ := 2 + (t : ℂ) * I
  have hc : c.re = 2 := by simp [c]
  have hcen : ‖c‖ ≤ 2 + |t| := by simpa [c, norm_mul] using norm_add_le (2 : ℂ) ((t : ℂ) * I)
  have hcen' : b ≤ ‖L c‖ := hB χ hc.ge
  have hcn : 0 < ‖L c‖ := hb.trans_le hcen'
  let u : ℝ := 14 + |t|
  have hu : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg t]
  have hu' : 0 < u := zero_lt_one.trans_le hu
  let M := C * u ^ 6
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hu)
  have hbd : ∀ z ∈ sphere c 6, ‖L z‖ ≤ M := by
    intro z hz
    have h6 : ‖z - c‖ = 6 := by simpa [dist_eq_norm] using hz
    have hRe := Complex.abs_re_le_norm (z - c)
    rw [sub_re, hc, h6] at hRe
    have hn : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa using norm_add_le (z - c) c
    rw [h6] at hn
    have hzbound : ‖z‖ + 6 ≤ u := by dsimp [u]; linarith
    exact (hG z (by linarith [(abs_le.mp hRe).1])).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hzbound _) (by linarith))
  have hj := AnalyticOnNhd.sum_divisor_le («f» := L) (c := c) (r := 5) (R := 6)
    (by norm_num) (by norm_num) hM (fun z _ ↦ analyticAt_L z) (norm_pos_iff.mp hcn)
    (by simpa using hbd)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at hj
  refine hj.trans (div_le_div_of_nonneg_right ?_ (Real.log_nonneg (by norm_num)))
  have hlog := Real.log_le_log hb hcen'
  have hlogu : Real.log u ≤ Real.log 14 + Real.log (1 + |t|) := by
    rw [← Real.log_mul (by norm_num : (14 : ℝ) ≠ 0) (by positivity : 1 + |t| ≠ 0)]
    exact Real.log_le_log hu' (by dsimp [u]; linarith [abs_nonneg t])
  rw [Real.log_div (zero_lt_one.trans_le hM).ne' hcn.ne']
  dsimp only [M]
  rw [Real.log_mul (zero_lt_one.trans_le hC).ne' (pow_ne_zero _ hu'.ne'), Real.log_pow]
  push_cast
  dsimp only [A]
  linarith only [hlog, hlogu, le_abs_self (Real.log C - Real.log b)]

private theorem disk_divisor_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ((∑ᶠ z, divisor L (closedBall (2 + (t : ℂ) * I) 5) z : ℤ) : ℝ)
        ≤ K * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨A, hA, hJ⟩ := moving_disk_jensen
  let d : ℝ := Real.log (6 / 5 : ℝ)
  have hd : 0 < d := Real.log_pos (by norm_num)
  refine ⟨(A + 12) / d, by positivity, fun t ↦ (hJ t).trans ?_⟩
  let x : ℝ := 1 + |t|
  have hx : 1 ≤ x := by dsimp [x]; linarith [abs_nonneg t]
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hx) (by norm_num : (0 : ℝ) < 1 / 2)
  have hpow := Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change (A + 6 * Real.log x) / d ≤ (A + 12) / d * x ^ (1 / 2 : ℝ)
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right
    (by linarith [mul_le_mul_of_nonneg_left hpow hA]) hd.le

private theorem order_ne_top (z : ℂ) : analyticOrderAt L z ≠ ⊤ := by
  intro h
  have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z analyticAt_L).mp h
  have hn : L 2 ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (Or.inl chi8_ne_one) (by norm_num)
  exact hn (congrFun he 2)

-- Compare finite sets of orders with the full nonnegative disk divisor, as
-- in AnalyticSlabSummability. The latter has finite support on the disk.
private theorem sum_orders_le_disk_divisor (c : ℂ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall c 5) :
    ∑ z ∈ S, (analyticOrderNatAt L z : ℝ) ≤
      ((∑ᶠ z, divisor L (closedBall c 5) z : ℤ) : ℝ) := by
  classical
  let D := divisor L (closedBall c 5)
  have han : AnalyticOnNhd ℂ L (closedBall c 5) := fun z _ ↦ analyticAt_L z
  have hD : 0 ≤ D := han.divisor_nonneg
  have hfin := D.finiteSupport (isCompact_closedBall c 5)
  let U := S ∪ hfin.toFinset
  have hsum : ∑ᶠ z, D z = ∑ z ∈ U, D z :=
    finsum_eq_sum_of_support_subset _ fun _ hz ↦
      Finset.subset_union_right (hfin.mem_toFinset.mpr hz)
  have horder (z : ℂ) (hz : z ∈ S) : D z = (analyticOrderNatAt L z : ℤ) := by
    change divisor L (closedBall c 5) z = _
    rw [han.divisor_apply (hS z hz), ← Nat.cast_analyticOrderNatAt (order_ne_top z)]
    simp
  have hle : ∑ z ∈ S, (analyticOrderNatAt L z : ℤ) ≤ ∑ᶠ z, D z := by
    calc
      _ = ∑ z ∈ S, D z := Finset.sum_congr rfl fun z hz ↦ (horder z hz).symm
      _ ≤ ∑ z ∈ U, D z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ ↦ hD z)
      _ = _ := hsum.symm
  exact_mod_cast hle

private abbrev StripZeros := {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ L z = 0}

private noncomputable def shell (z : StripZeros) : ℕ := ⌊|z.val.im|⌋₊

private theorem mem_slab_disk (z : StripZeros) {n : ℕ} (hs : shell z = n) :
    z.val ∈ closedBall (2 + ↑(if 0 ≤ z.val.im then (n : ℝ) else -(n : ℝ)) * I) 5 := by
  let w := z.val
  let t : ℝ := if 0 ≤ w.im then (n : ℝ) else -(n : ℝ)
  change w ∈ closedBall (2 + (t : ℂ) * I) 5
  have hlo := Nat.floor_le (abs_nonneg w.im)
  have hhi := Nat.lt_floor_add_one |w.im|
  change ⌊|w.im|⌋₊ = n at hs
  rw [hs] at hlo hhi
  have him : |w.im - t| ≤ 1 := by
    dsimp only [t]
    split_ifs with h
    · rw [abs_of_nonneg h] at hlo hhi
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [abs_of_nonpos (le_of_not_ge h)] at hlo hhi
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hl, hr, _⟩ := z.property
  have hre : |w.re - 2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [mem_closedBall, dist_eq_norm]
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  have hrw : (w - ((2 : ℂ) + (t : ℂ) * I)).re = w.re - 2 := by simp
  have hiw : (w - ((2 : ℂ) + (t : ℂ) * I)).im = w.im - t := by simp
  rw [hrw, hiw]
  linarith

private theorem order_count_by_shell {K : ℝ}
    (hcount : ∀ t : ℝ,
      ((∑ᶠ z, divisor L (closedBall (2 + (t : ℂ) * I) 5) z : ℤ) : ℝ)
        ≤ K * (1 + |t|) ^ (1 / 2 : ℝ))
    (n : ℕ) (S : Finset StripZeros) (hS : ∀ z ∈ S, shell z = n) :
    ∑ z ∈ S, (analyticOrderNatAt L z.val : ℝ) ≤ 2 * K * (1 + (n : ℝ)) ^ (1 / 2 : ℝ) := by
  classical
  let ord (z : StripZeros) := (analyticOrderNatAt L z.val : ℝ)
  -- Each shell consists of one slab for each sign of the height.
  have hside (p : Bool) : (∑ z ∈ S with decide (0 ≤ z.val.im) = p, ord z) ≤
      K * (1 + (n : ℝ)) ^ (1 / 2 : ℝ) := by
    let Q := S.filter (fun z ↦ decide (0 ≤ z.val.im) = p)
    let e : StripZeros ↪ ℂ := Function.Embedding.subtype _
    let t : ℝ := if p then (n : ℝ) else -(n : ℝ)
    have ht : |t| = n := by cases p <;> simp [t, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    have hQ (w : ℂ) (hw : w ∈ Q.map e) : w ∈ closedBall (2 + (t : ℂ) * I) 5 := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨hzS, hp⟩ := Finset.mem_filter.mp hz
      have ht' : (if 0 ≤ z.val.im then (n : ℝ) else -(n : ℝ)) = t := by
        simp only [t, ← hp, decide_eq_true_eq]
      change z.val ∈ closedBall (2 + (t : ℂ) * I) 5
      rw [← ht']
      exact mem_slab_disk z (hS z hzS)
    rw [← ht]
    have h := sum_orders_le_disk_divisor (2 + (t : ℂ) * I) (Q.map e) hQ
    rw [Finset.sum_map] at h
    exact h.trans (hcount t)
  have hpart := Finset.sum_filter_add_sum_filter_not S (fun z ↦ decide (0 ≤ z.val.im) = true) ord
  have hfalse : (fun z : StripZeros ↦ ¬decide (0 ≤ z.val.im) = true) =
      (fun z : StripZeros ↦ decide (0 ≤ z.val.im) = false) := by
    funext z
    cases decide (0 ≤ z.val.im) <;> simp
  simp only [hfalse] at hpart
  change ∑ z ∈ S, ord z ≤ _
  rw [← hpart]
  linarith only [hside true, hside false]

-- The origin is excluded by the open strip. Isolation keeps all remaining
-- zeros a uniform positive distance from it, including those in shell zero.
private theorem strip_zero_norm_lower_bound :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : StripZeros, δ ≤ ‖z.val‖ := by
  have hn : ∀ᶠ z in 𝓝[≠] (0 : ℂ), L z ≠ 0 :=
    ((analyticAt_L 0).eventually_eq_zero_or_eventually_ne_zero).resolve_left
      (fun he ↦ order_ne_top 0 (analyticOrderAt_eq_top.mpr he))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hn
  refine ⟨δ, hδ, fun z ↦ le_of_not_gt fun hz ↦ ?_⟩
  have hz0 : z.val ≠ 0 := by
    intro h
    simpa [h] using z.property.1
  have hzball : z.val ∈ ball (0 : ℂ) δ := by simpa [mem_ball, dist_zero_right] using hz
  exact (hball ⟨hzball, by simpa using hz0⟩) z.property.2.2

/-- The inverse-square weights of the zeros in the open critical strip of
`χ.LFunction`, counted with their full analytic multiplicities, are summable.
No critical-line hypothesis is needed. -/
public theorem summable_analyticOrderNatAt_div_norm_sq :
    Summable (fun ρ : {z : ℂ // 0 < z.re ∧ z.re < 1 ∧ χ.LFunction z = 0} ↦
      (analyticOrderNatAt χ.LFunction ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  classical
  obtain ⟨K, hK, hcount⟩ := disk_divisor_bound
  obtain ⟨δ, hδ, hnorm⟩ := strip_zero_norm_lower_bound
  let ord (z : StripZeros) := (analyticOrderNatAt L z.val : ℝ)
  let W (z : StripZeros) := ord z / ‖z.val‖ ^ 2
  let D := δ⁻¹ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let P (n : ℕ) := (2 * K * D ^ 2) * (1 / (↑(n + 1) : ℝ) ^ (3 / 2 : ℝ))
  have hP : Summable P := by
    have hp := Real.summable_one_div_nat_rpow.mpr (show 1 < (3 / 2 : ℝ) by norm_num)
    exact (hp.comp_injective Nat.succ_injective).mul_left (2 * K * D ^ 2)
  have hnP (n : ℕ) : 0 ≤ P n := by dsimp [P]; positivity
  have hblock (n : ℕ) (S : Finset StripZeros) (hS : ∀ z ∈ S, shell z = n) :
      ∑ z ∈ S, W z ≤ P n := by
    let d : ℝ := 1 + (n : ℝ)
    have hd : 0 < d := by dsimp [d]; positivity
    have hpoint (z : StripZeros) (hz : z ∈ S) : W z ≤ ord z * (D ^ 2 / d ^ 2) := by
      have hfloor := Nat.floor_le (abs_nonneg z.val.im)
      change (shell z : ℝ) ≤ |z.val.im| at hfloor
      rw [hS z hz] at hfloor
      have hinv : 1 ≤ δ⁻¹ * ‖z.val‖ := by
        rw [← div_eq_inv_mul, le_div_iff₀ hδ, one_mul]
        exact hnorm z
      have hdz : d ≤ D * ‖z.val‖ := by
        dsimp [d, D]
        rw [add_mul, one_mul]
        exact add_le_add hinv (hfloor.trans (abs_im_le_norm _))
      dsimp only [W]
      rw [← mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [div_le_div_iff₀ (pow_pos (hδ.trans_le (hnorm z)) _) (pow_pos hd _), one_mul,
        ← mul_pow]
      exact pow_le_pow_left₀ hd.le hdz _
    calc
      _ ≤ ∑ z ∈ S, ord z * (D ^ 2 / d ^ 2) := Finset.sum_le_sum hpoint
      _ = (∑ z ∈ S, ord z) * (D ^ 2 / d ^ 2) := (Finset.sum_mul ..).symm
      _ ≤ 2 * K * d ^ (1 / 2 : ℝ) * (D ^ 2 / d ^ 2) :=
        mul_le_mul_of_nonneg_right (order_count_by_shell hcount n S hS) (by positivity)
      _ = P n := by
        have hp : d ^ (1 / 2 : ℝ) / d ^ 2 = 1 / d ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_natCast d 2, ← Real.rpow_sub hd]
          norm_num only [Nat.cast_ofNat, show (1 / 2 - 2 : ℝ) = -(3 / 2) by norm_num]
          rw [Real.rpow_neg hd.le, one_div]
        dsimp only [P]
        rw [show (↑(n + 1) : ℝ) = d by simp [d, add_comm], ← hp]
        ring
  -- Bound the sum over every finite set by the same convergent p-series.
  apply summable_of_sum_le («f» := W) (c := ∑' n, P n) (fun z ↦ by dsimp [W, ord]; positivity)
  intro S
  calc
    ∑ z ∈ S, W z = ∑ n ∈ S.image shell, ∑ z ∈ S with shell z = n, W z :=
      (Finset.sum_fiberwise_of_maps_to (fun _ hz ↦ Finset.mem_image_of_mem shell hz) W).symm
    _ ≤ ∑ n ∈ S.image shell, P n :=
      Finset.sum_le_sum fun n _ ↦ hblock n _ (fun z hz ↦ (Finset.mem_filter.mp hz).2)
    _ ≤ ∑' n, P n := hP.sum_le_tsum _ (fun n _ ↦ hnP n)

end Chi8Origin
