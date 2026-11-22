module

public import Theorems.DirichletThreeRectangleResidues
import Lemmas.DirichletLFunctionGrowth
import Lemmas.DirichletRightAnchor
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.PSeries

/-!
# Absolute summability over the completed conductor-three zero divisor

The divisor is that of Mathlib's completed L-function of the odd primitive
quadratic character modulo three, without a conductor power. Half-plane
nonvanishing puts every completed zero strictly between real parts zero and
one. The nonvanishing odd Gamma factor preserves the bare analytic order
there. A moving Jensen bound controls the full order in each unit-height
block, and cubic Mellin decay makes the resulting bounds summable.

This prepares the local exhaustion comparison with (B.3.2.3), PDF pp.
605–606, and (B.4.2.2), PDF p. 614 (provisional manuscript mapping). It does
not give the infinite contour identity, identify an idelic completion, or
locate zeros on the critical line. Owning check session:
`01a20525-b261-79ef-94fa-7a6b64536cd6`.
-/

open Complex Filter MeromorphicOn Metric Set
open scoped Topology ContDiff

namespace Masullo

local notation "χ" => padicRamifiedThreeCharacter
local notation "f" => DirichletCharacter.LFunction padicRamifiedThreeCharacter
local notation "F" => DirichletCharacter.completedLFunction padicRamifiedThreeCharacter

private theorem three_ne_one : χ ≠ 1 := by
  intro h
  exact DirichletCharacter.Odd.not_even χ padicRamifiedThreeCharacter_odd
    (h ▸ DirichletCharacter.even_one)

private theorem analyticOnNhd_bare : AnalyticOnNhd ℂ f univ :=
  fun z _ ↦ (DirichletCharacter.differentiable_LFunction three_ne_one).analyticAt z

private theorem completed_eq_bare_mul_gamma {s : ℂ} (hs : 0 < (s + 1).re) :
    F s = f s * Gammaℝ (s + 1) := by
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s
    (Or.inr (by decide : 3 ^ 1 ≠ (1 : ℕ)))
  rw [padicRamifiedThreeCharacter_odd.gammaFactor_def] at h
  exact ((eq_div_iff (Gammaℝ_ne_zero_of_re_pos hs)).mp h).symm

private theorem completed_order_eq_bare {s : ℂ} (hs : -1 < s.re) :
    analyticOrderAt F s = analyticOrderAt f s := by
  have hOpen : IsOpen {z : ℂ | -1 < z.re} := isOpen_lt continuous_const continuous_re
  have hN : ∀ᶠ z : ℂ in 𝓝 s, -1 < z.re := hOpen.mem_nhds hs
  let G : ℂ → ℂ := fun z ↦ Gammaℝ (z + 1)
  have hEq : F =ᶠ[𝓝 s] f * G := by
    filter_upwards [hN] with z hz
    exact completed_eq_bare_mul_gamma (by simp only [add_re, one_re]; linarith)
  have hn : G s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)
  have hg : AnalyticAt ℂ G s := by
    have h₁ := (differentiable_Gammaℝ_inv.analyticAt (s + 1)).inv (inv_ne_zero hn)
    change AnalyticAt ℂ (fun z ↦ ((Gammaℝ z)⁻¹)⁻¹) (s + 1) at h₁
    have h₂ : AnalyticAt ℂ Gammaℝ (s + 1) := by simpa only [inv_inv] using h₁
    change AnalyticAt ℂ (Gammaℝ ∘ fun z : ℂ ↦ z + 1) s
    have hshift : AnalyticAt ℂ (fun z : ℂ ↦ z + 1) s :=
      (differentiable_id.add (differentiable_const (1 : ℂ))).analyticAt s
    exact AnalyticAt.comp (g := Gammaℝ) («f» := fun z : ℂ ↦ z + 1) (x := s) h₂ hshift
  rw [analyticOrderAt_congr hEq, analyticOrderAt_mul (analyticOnNhd_bare s trivial) hg,
    hg.analyticOrderAt_eq_zero.mpr hn, add_zero]

private theorem bare_order_ne_top (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  obtain ⟨b, hb, ha⟩ := exists_dirichlet_anchor_at (show (1 : ℝ) < 2 by norm_num)
  have hz : f 2 ≠ 0 := norm_pos_iff.mp (hb.trans_le (ha χ (s := 2) (by norm_num)))
  exact analyticOnNhd_bare.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    trivial trivial (x := 2)
    (by rw [(analyticOnNhd_bare 2 trivial).analyticOrderAt_eq_zero.mpr hz]; simp)

private theorem bare_divisor_apply {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    divisor f U z = ((analyticOrderAt f z).toNat : ℤ) := by
  have h := ENat.natCast_toNat (bare_order_ne_top z)
  rw [(analyticOnNhd_bare.mono (subset_univ U)).divisor_apply hz, ← h]
  simp

private theorem sum_bare_orders_le_jensen {c : ℂ} {M : ℝ} (hc : f c ≠ 0) (hM : 1 ≤ M)
    (hbd : ∀ z ∈ sphere c 6, ‖f z‖ ≤ M) :
    ∀ A : Finset ℂ, (∀ z ∈ A, z ∈ closedBall c 5) →
      ∑ z ∈ A, ((analyticOrderAt f z).toNat : ℝ) ≤
        Real.log (M / ‖f c‖) / Real.log (6 / 5 : ℝ) := by
  classical
  intro A hA
  let S := closedBall c 5
  let D := divisor f S
  have hDn : 0 ≤ D := (analyticOnNhd_bare.mono (subset_univ S)).divisor_nonneg
  have hf := D.finiteSupport (isCompact_closedBall c 5)
  -- Compare the given Finset with the full nonnegative divisor on the disk.
  let U := A ∪ hf.toFinset
  have hsum : ∑ᶠ z, D z = ∑ z ∈ U, D z :=
    finsum_eq_sum_of_support_subset _ fun _ hz ↦ Finset.subset_union_right (hf.mem_toFinset.mpr hz)
  have hcount : (∑ z ∈ A, ((analyticOrderAt f z).toNat : ℤ)) ≤ ∑ᶠ z, D z := by
    calc
      _ = ∑ z ∈ A, D z := Finset.sum_congr rfl fun z hz ↦ (bare_divisor_apply (hA z hz)).symm
      _ ≤ ∑ z ∈ U, D z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ ↦ hDn z)
      _ = _ := hsum.symm
  have hj := AnalyticOnNhd.sum_divisor_le («f» := f) (c := c) (r := 5) (R := 6)
    (by norm_num) (by norm_num) hM (analyticOnNhd_bare.mono (subset_univ _)) hc
    (by simpa using hbd)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at hj
  change ((∑ᶠ z, D z : ℤ) : ℝ) ≤ _ at hj
  exact (show _ ≤ ((∑ᶠ z, D z : ℤ) : ℝ) by exact_mod_cast hcount).trans hj

private theorem sum_bare_orders_le_linear_height :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, ∀ A : Finset ℂ,
    (∀ z ∈ A, z ∈ closedBall (2 + (t : ℂ) * I) 5) →
      ∑ z ∈ A, ((analyticOrderAt f z).toNat : ℝ) ≤ K * (1 + |t|) := by
  obtain ⟨C, hC, hG⟩ := exists_dirichlet_LFunction_growth_closed_halfPlane χ three_ne_one
  obtain ⟨b, hb, hB⟩ := exists_dirichlet_anchor_at (show (1 : ℝ) < 2 by norm_num)
  let d : ℝ := Real.log (6 / 5 : ℝ)
  have hd : 0 < d := Real.log_pos (by norm_num)
  let a := |Real.log C - Real.log b|
  have ha : 0 ≤ a := abs_nonneg _
  refine ⟨(a + 78) / d, by positivity, ?_⟩
  intro t A hA
  let c : ℂ := 2 + (t : ℂ) * I
  have hc : c.re = 2 := by simp [c]
  have hcen : ‖c‖ ≤ 2 + |t| := by simpa [c, norm_mul] using norm_add_le (2 : ℂ) ((t : ℂ) * I)
  have hcen' : b ≤ ‖f c‖ := hB χ hc.ge
  have hcn : 0 < ‖f c‖ := hb.trans_le hcen'
  let u : ℝ := 14 + |t|
  have hu : 1 ≤ u := by dsimp [u]; linarith [abs_nonneg t]
  have hu' : 0 < u := zero_lt_one.trans_le hu
  let M := C * u ^ 6
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hu)
  have hM' : 0 < M := zero_lt_one.trans_le hM
  have hbd : ∀ z ∈ sphere c 6, ‖f z‖ ≤ M := by
    intro z hz
    have h6 : ‖z - c‖ = 6 := by simpa [dist_eq_norm] using hz
    have hRe := Complex.abs_re_le_norm (z - c)
    rw [sub_re, hc, h6] at hRe
    have hn : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa using norm_add_le (z - c) c
    rw [h6] at hn
    have hzbound : ‖z‖ + 6 ≤ u := by dsimp [u]; linarith
    exact (hG z (by linarith [(abs_le.mp hRe).1])).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hzbound _) (by linarith))
  have hlog := Real.log_le_log hb hcen'
  have hlogu := Real.log_le_sub_one_of_pos hu'
  have hnum : Real.log (M / ‖f c‖) ≤ (a + 78) * (1 + |t|) := by
    rw [Real.log_div hM'.ne' hcn.ne']
    dsimp only [M]
    rw [Real.log_mul (zero_lt_one.trans_le hC).ne' (pow_ne_zero _ hu'.ne'), Real.log_pow]
    push_cast
    have habs : Real.log C - Real.log b ≤ a := le_abs_self _
    have hx := mul_nonneg ha (abs_nonneg t)
    dsimp [u] at hlogu
    nlinarith [abs_nonneg t]
  calc
    _ ≤ Real.log (M / ‖f c‖) / d := sum_bare_orders_le_jensen (norm_pos_iff.mp hcn) hM hbd A hA
    _ ≤ ((a + 78) * (1 + |t|)) / d := div_le_div_of_nonneg_right hnum hd.le
    _ = _ := by ring

private abbrev CompletedZeros := {z : ℂ // F z = 0}

private theorem completed_zero_re (z : CompletedZeros) : 0 < z.val.re ∧ z.val.re < 1 :=
  ⟨lt_of_not_ge fun h ↦ padicRamifiedThree_completed_ne_zero_of_re_nonpos h z.property,
    lt_of_not_ge fun h ↦ padicRamifiedThree_completed_ne_zero_of_one_le_re h z.property⟩

private noncomputable def ord (z : CompletedZeros) : ℕ := analyticOrderNatAt F z.val
private noncomputable def shell (z : CompletedZeros) : ℕ := ⌊|z.val.im|⌋₊

private noncomputable def signedHeight (z : CompletedZeros) (n : ℕ) : ℝ :=
  if 0 ≤ z.val.im then (n : ℝ) else -(n : ℝ)

private theorem disk_of_shell (z : CompletedZeros) (n : ℕ) (hs : shell z = n) :
    z.val ∈ closedBall (2 + ↑(signedHeight z n) * I) 5 := by
  let w := z.val
  let t : ℝ := signedHeight z n
  change w ∈ closedBall (2 + (t : ℂ) * I) 5
  have h0 := Nat.floor_le (abs_nonneg w.im)
  have h1 := Nat.lt_floor_add_one |w.im|
  change ⌊|w.im|⌋₊ = n at hs
  rw [hs] at h0 h1
  have him : |w.im - t| ≤ 1 := by
    change |w.im - (if 0 ≤ w.im then (n : ℝ) else -(n : ℝ))| ≤ 1
    split_ifs with h
    · rw [abs_of_nonneg h] at h0 h1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [abs_of_nonpos (le_of_not_ge h)] at h0 h1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [mem_closedBall, dist_eq_norm]
  apply (norm_le_abs_re_add_abs_im _).trans
  have hrw : (w - ((2 : ℂ) + (t : ℂ) * I)).re = w.re - 2 := by simp
  have hiw : (w - ((2 : ℂ) + (t : ℂ) * I)).im = w.im - t := by simp
  rw [hrw, hiw]
  obtain ⟨hl, hr⟩ := completed_zero_re z
  have hre : |w.re - 2| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

private theorem order_count_by_shell {K : ℝ}
    (hc : ∀ t : ℝ, ∀ A : Finset ℂ,
      (∀ z ∈ A, z ∈ closedBall (2 + (t : ℂ) * I) 5) →
        ∑ z ∈ A, ((analyticOrderAt f z).toNat : ℝ) ≤ K * (1 + |t|))
    (n : ℕ) (S : Finset CompletedZeros) (hS : ∀ z ∈ S, shell z = n) :
      ∑ z ∈ S, (ord z : ℝ) ≤ 2 * K * (1 + n) := by
  classical
  have hside (p : Bool) :
      (∑ z ∈ S with decide (0 ≤ z.val.im) = p, (ord z : ℝ)) ≤ K * (1 + n) := by
    let Q := S.filter (fun z ↦ decide (0 ≤ z.val.im) = p)
    let e : CompletedZeros ↪ ℂ := Function.Embedding.subtype _
    let t : ℝ := if p then (n : ℝ) else -(n : ℝ)
    have ht : |t| = n := by cases p <;> simp [t, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    have hQ (w : ℂ) (hw : w ∈ Q.map e) : w ∈ closedBall (2 + (t : ℂ) * I) 5 := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨hzS, hp⟩ := Finset.mem_filter.mp hz
      have ht' : signedHeight z n = t := by simp only [signedHeight, t, ← hp, decide_eq_true_eq]
      change z.val ∈ closedBall (2 + (t : ℂ) * I) 5
      rw [← ht']
      exact disk_of_shell z n (hS z hzS)
    rw [← ht]
    change (∑ z ∈ Q, (ord z : ℝ)) ≤ _
    refine le_trans ?_ (hc t (Q.map e) hQ)
    rw [Finset.sum_map]
    apply le_of_eq (Finset.sum_congr rfl fun z _ ↦ ?_)
    have hr : -1 < z.val.re := by linarith [(completed_zero_re z).1]
    rw [ord, analyticOrderNatAt, completed_order_eq_bare hr]
    rfl
  have hpart := Finset.sum_filter_add_sum_filter_not S
    (fun z : CompletedZeros ↦ decide (0 ≤ z.val.im) = true) (fun z ↦ (ord z : ℝ))
  have hfalse : (fun z : CompletedZeros ↦ ¬decide (0 ≤ z.val.im) = true) =
      (fun z : CompletedZeros ↦ decide (0 ≤ z.val.im) = false) := by
    funext z
    cases decide (0 ≤ z.val.im) <;> simp
  simp only [hfalse] at hpart
  rw [← hpart]
  linarith [hside true, hside false]

/-- The Mellin test is absolutely summable over all zeros of the completed
quadratic L-function modulo three, weighted by their full analytic orders. -/
public theorem summable_norm_padicRamifiedThree_completed_zero_test {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    Summable (fun z : {z : ℂ //
      DirichletCharacter.completedLFunction padicRamifiedThreeCharacter z = 0} ↦
      ‖(analyticOrderNatAt (DirichletCharacter.completedLFunction padicRamifiedThreeCharacter)
        (z : ℂ) : ℂ) * compactLogMellin g (z : ℂ)‖) := by
  classical
  obtain ⟨K, hK, hcount⟩ := sum_bare_orders_le_linear_height
  obtain ⟨B, hB, hdecay⟩ := compactLogMellin_vertical_decay hg hcg (3 / 2) 3
  let W (z : CompletedZeros) := ‖(ord z : ℂ) * compactLogMellin g z.val‖
  let P (n : ℕ) := (2 * K * B) * (1 / (↑(n + 1) : ℝ) ^ 2)
  have hP : Summable P := by
    have hh := Real.summable_one_div_nat_pow.mpr (show 1 < (2 : ℕ) by decide)
    exact (hh.comp_injective Nat.succ_injective).mul_left (2 * K * B)
  have hnP (n : ℕ) : 0 ≤ P n := by dsimp [P]; positivity
  have hblock (n : ℕ) (S : Finset CompletedZeros) (hS : ∀ z ∈ S, shell z = n) :
      ∑ z ∈ S, W z ≤ P n := by
    let d : ℝ := 1 + (n : ℝ)
    have hd : 0 < d := by dsimp [d]; positivity
    have hpoint (z : CompletedZeros) (hz : z ∈ S) : W z ≤ (ord z : ℝ) * (B / d ^ 3) := by
      obtain ⟨hl, hr⟩ := completed_zero_re z
      have habs : |z.val.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have htest := hdecay z.val.re z.val.im habs
      rw [Complex.re_add_im] at htest
      have hfloor := Nat.floor_le (abs_nonneg z.val.im)
      change (shell z : ℝ) ≤ |z.val.im| at hfloor
      rw [hS z hz] at hfloor
      dsimp [W]
      rw [norm_mul, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left (htest.trans ?_) (Nat.cast_nonneg _)
      apply div_le_div_of_nonneg_left hB.le (pow_pos hd _)
      dsimp [d]
      gcongr
    calc
      _ ≤ ∑ z ∈ S, (ord z : ℝ) * (B / d ^ 3) := Finset.sum_le_sum hpoint
      _ = (∑ z ∈ S, (ord z : ℝ)) * (B / d ^ 3) := Finset.sum_mul .. |>.symm
      _ ≤ 2 * K * d * (B / d ^ 3) :=
        mul_le_mul_of_nonneg_right (order_count_by_shell hcount n S hS) (by positivity)
      _ = P n := by
        dsimp [P]
        rw [show (↑(n + 1) : ℝ) = d by simp [d, add_comm]]
        field_simp
  -- Bound arbitrary finite subsets by the same p-series; there is no need
  -- to choose an enumeration of the zeros.
  apply summable_of_sum_le («f» := W) (c := ∑' n, P n) (fun _ ↦ norm_nonneg _)
  intro S
  calc
    ∑ z ∈ S, W z = ∑ n ∈ S.image shell, ∑ z ∈ S with shell z = n, W z :=
      (Finset.sum_fiberwise_of_maps_to (fun _ hz ↦ Finset.mem_image_of_mem shell hz) W).symm
    _ ≤ ∑ n ∈ S.image shell, P n :=
      Finset.sum_le_sum fun n _ ↦ hblock n _ (fun z hz ↦ (Finset.mem_filter.mp hz).2)
    _ ≤ ∑' n, P n := hP.sum_le_tsum _ (fun n _ ↦ hnP n)

end Masullo
