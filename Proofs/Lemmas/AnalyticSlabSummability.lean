module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.PSeries

/-! # Absolute summability from an entire function's disk counts

A linear bound on disk multiplicities bounds each unit-height slab. Cubic
vertical decay then gives a summable inverse-square bound on the slab weights.
-/

open Complex MeromorphicOn Metric Set

namespace Masullo

private theorem sum_analyticOrders_le_disk_divisor {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) (h₁ : H 1 ≠ 0) (c : ℂ)
    (A : Finset ℂ) (hA : ∀ z ∈ A, z ∈ closedBall c 5) :
    ∑ z ∈ A, (analyticOrderNatAt H z : ℝ) ≤
      ((∑ᶠ z, divisor H (closedBall c 5) z : ℤ) : ℝ) := by
  classical
  let D := divisor H (closedBall c 5)
  have han : AnalyticOnNhd ℂ H (closedBall c 5) := fun z _ ↦ hH.analyticAt z
  have hD : 0 ≤ D := han.divisor_nonneg
  have hfin := D.finiteSupport (isCompact_closedBall c 5)
  -- Work in a finite set containing both A and the full disk support.
  let U := A ∪ hfin.toFinset
  have hsum : ∑ᶠ z, D z = ∑ z ∈ U, D z :=
    finsum_eq_sum_of_support_subset _ fun _ hz ↦
      Finset.subset_union_right (hfin.mem_toFinset.mpr hz)
  have horder (z : ℂ) (hz : z ∈ A) : D z = (analyticOrderNatAt H z : ℤ) := by
    have ht : analyticOrderAt H z ≠ ⊤ := fun he ↦ h₁ (congrFun
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hH.analyticAt).mp he) 1)
    change divisor H (closedBall c 5) z = _
    rw [han.divisor_apply (hA z hz), ← Nat.cast_analyticOrderNatAt ht]
    simp
  have hle : ∑ z ∈ A, (analyticOrderNatAt H z : ℤ) ≤ ∑ᶠ z, D z := by
    calc
      _ = ∑ z ∈ A, D z := Finset.sum_congr rfl fun z hz ↦ (horder z hz).symm
      _ ≤ ∑ z ∈ U, D z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ ↦ hD z)
      _ = _ := hsum.symm
  exact_mod_cast hle

private noncomputable def slab (z : ℂ) : ℕ := ⌊|z.im|⌋₊

private theorem mem_slab_disk {z : ℂ} (hl : -1 < z.re) (hr : z.re < 2)
    {n : ℕ} (hs : slab z = n) :
    z ∈ closedBall (2 + ↑(if 0 ≤ z.im then (n : ℝ) else -(n : ℝ)) * I) 5 := by
  let t : ℝ := if 0 ≤ z.im then (n : ℝ) else -(n : ℝ)
  change z ∈ closedBall (2 + (t : ℂ) * I) 5
  have hlo := Nat.floor_le (abs_nonneg z.im)
  have hhi := Nat.lt_floor_add_one |z.im|
  change ⌊|z.im|⌋₊ = n at hs
  rw [hs] at hlo hhi
  have him : |z.im - t| ≤ 1 := by
    dsimp only [t]
    split_ifs with h
    · rw [abs_of_nonneg h] at hlo hhi
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [abs_of_nonpos (le_of_not_ge h)] at hlo hhi
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hre : |z.re - 2| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [mem_closedBall, dist_eq_norm]
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  have hrw : (z - ((2 : ℂ) + (t : ℂ) * I)).re = z.re - 2 := by simp
  have hiw : (z - ((2 : ℂ) + (t : ℂ) * I)).im = z.im - t := by simp
  rw [hrw, hiw]
  linarith

/-- A linear bound on the full disk divisor gives absolute convergence of
zero weights with cubic decay on the strip, with all analytic multiplicities. -/
public theorem summable_norm_analyticOrder_mul_of_disk_count
    {H Φ : ℂ → ℂ} (hH : Differentiable ℂ H) (h₁ : H 1 ≠ 0)
    (hstrip : ∀ z, H z = 0 → -1 < z.re ∧ z.re < 2)
    {C B : ℝ} (hB : 0 ≤ B)
    (hcount : ∀ t : ℝ,
      ((∑ᶠ z, MeromorphicOn.divisor H
        (Metric.closedBall (2 + (t : ℂ) * Complex.I) 5) z : ℤ) : ℝ)
        ≤ C * (1 + |t|))
    (hΦ : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      ‖Φ z‖ ≤ B / (1 + |z.im|)^3) :
    Summable (fun z : {z : ℂ // H z = 0} ↦
      ‖(analyticOrderNatAt H z.val : ℂ) * Φ z.val‖) := by
  classical
  let Z := {z : ℂ // H z = 0}
  let shell (z : Z) := slab z.val
  let ord (z : Z) := analyticOrderNatAt H z.val
  let W (z : Z) := ‖(ord z : ℂ) * Φ z.val‖
  have hdisk (t : ℝ) (S : Finset Z)
      (hS : ∀ z ∈ S, z.val ∈ closedBall (2 + (t : ℂ) * I) 5) :
      ∑ z ∈ S, (ord z : ℝ) ≤ C * (1 + |t|) := by
    let e : Z ↪ ℂ := Function.Embedding.subtype _
    have hA (w : ℂ) (hw : w ∈ S.map e) : w ∈ closedBall (2 + (t : ℂ) * I) 5 := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
      exact hS z hz
    have h := sum_analyticOrders_le_disk_divisor hH h₁ (2 + (t : ℂ) * I) (S.map e) hA
    rw [Finset.sum_map] at h
    exact h.trans (hcount t)
  have hC : 0 ≤ C := by simpa using hdisk 0 ∅ (by simp)
  have hslab (n : ℕ) (S : Finset Z) (hS : ∀ z ∈ S, shell z = n) :
      ∑ z ∈ S, (ord z : ℝ) ≤ 2 * C * (1 + n) := by
    -- Each shell is a pair of slabs, one for each sign of the height.
    have hside (p : Bool) :
        (∑ z ∈ S with decide (0 ≤ z.val.im) = p, (ord z : ℝ)) ≤ C * (1 + n) := by
      let t : ℝ := if p then (n : ℝ) else -(n : ℝ)
      have ht : |t| = n := by
        cases p <;> simp [t, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
      rw [← ht]
      apply hdisk
      intro z hz
      obtain ⟨hzS, hp⟩ := Finset.mem_filter.mp hz
      obtain ⟨hl, hr⟩ := hstrip z.val z.property
      have ht' : (if 0 ≤ z.val.im then (n : ℝ) else -(n : ℝ)) = t := by
        simp only [t, ← hp, decide_eq_true_eq]
      rw [← ht']
      exact mem_slab_disk hl hr (hS z hzS)
    have hpart := Finset.sum_filter_add_sum_filter_not S
      (fun z : Z ↦ decide (0 ≤ z.val.im) = true) (fun z ↦ (ord z : ℝ))
    have hfalse : (fun z : Z ↦ ¬decide (0 ≤ z.val.im) = true) =
        (fun z : Z ↦ decide (0 ≤ z.val.im) = false) := by
      funext z
      cases decide (0 ≤ z.val.im) <;> simp
    simp only [hfalse] at hpart
    rw [← hpart]
    linarith [hside true, hside false]
  let P (n : ℕ) := (2 * C * B) * (1 / (↑(n + 1) : ℝ) ^ 2)
  have hP : Summable P := by
    have hp := Real.summable_one_div_nat_pow.mpr (show 1 < (2 : ℕ) by decide)
    exact (hp.comp_injective Nat.succ_injective).mul_left (2 * C * B)
  have hnP (n : ℕ) : 0 ≤ P n := by dsimp [P]; positivity
  have hblock (n : ℕ) (S : Finset Z) (hS : ∀ z ∈ S, shell z = n) :
      ∑ z ∈ S, W z ≤ P n := by
    let d : ℝ := 1 + (n : ℝ)
    have hd : 0 < d := by dsimp [d]; positivity
    have hpoint (z : Z) (hz : z ∈ S) : W z ≤ (ord z : ℝ) * (B / d ^ 3) := by
      obtain ⟨hl, hr⟩ := hstrip z.val z.property
      have hfloor := Nat.floor_le (abs_nonneg z.val.im)
      change (shell z : ℝ) ≤ |z.val.im| at hfloor
      rw [hS z hz] at hfloor
      dsimp [W]
      rw [norm_mul, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left ((hΦ z.val hl.le hr.le).trans ?_) (Nat.cast_nonneg _)
      apply div_le_div_of_nonneg_left hB (pow_pos hd _)
      dsimp [d]
      gcongr
    calc
      _ ≤ ∑ z ∈ S, (ord z : ℝ) * (B / d ^ 3) := Finset.sum_le_sum hpoint
      _ = (∑ z ∈ S, (ord z : ℝ)) * (B / d ^ 3) := (Finset.sum_mul ..).symm
      _ ≤ 2 * C * d * (B / d ^ 3) :=
        mul_le_mul_of_nonneg_right (hslab n S hS) (by positivity)
      _ = P n := by
        dsimp [P]
        rw [show (↑(n + 1) : ℝ) = d by simp [d, add_comm]]
        field_simp
  -- The bounds apply to every finite subset, without an enumeration of zeros.
  apply summable_of_sum_le («f» := W) (c := ∑' n, P n) (fun _ ↦ norm_nonneg _)
  intro S
  calc
    ∑ z ∈ S, W z = ∑ n ∈ S.image shell, ∑ z ∈ S with shell z = n, W z :=
      (Finset.sum_fiberwise_of_maps_to (fun _ hz ↦ Finset.mem_image_of_mem shell hz) W).symm
    _ ≤ ∑ n ∈ S.image shell, P n :=
      Finset.sum_le_sum fun n _ ↦ hblock n _ (fun z hz ↦ (Finset.mem_filter.mp hz).2)
    _ ≤ ∑' n, P n := hP.sum_le_tsum _ (fun n _ ↦ hnP n)

end Masullo
