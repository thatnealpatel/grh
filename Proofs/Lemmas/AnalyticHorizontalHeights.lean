module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Finite interval exclusion and pole-factor removal for horizontal contour edges. -/

open Complex Filter MeasureTheory MeromorphicOn Metric Set
open scoped Topology

namespace Masullo

private theorem exists_diskZeros {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) {c : ℂ}
    (hc : f c ≠ 0) :
    ∃ A : Finset ℂ, (∀ ρ, ρ ∈ A ↔ ρ ∈ closedBall c 5 ∧ f ρ = 0) ∧
      (A.card : ℝ) ≤ ((∑ᶠ ρ, divisor f (closedBall c 5) ρ : ℤ) : ℝ) := by
  classical
  let D := divisor f (closedBall c 5)
  have hf' := hf.mono (subset_univ (closedBall c 5))
  have htop (z : ℂ) : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial
      (x := c) (by rw [(hf c trivial).analyticOrderAt_eq_zero.mpr hc]; simp)
  have hfin := D.finiteSupport (isCompact_closedBall c 5)
  refine ⟨hfin.toFinset, fun ρ ↦ ?_, ?_⟩
  · rw [hfin.mem_toFinset]
    have horder (hρ : ρ ∈ closedBall c 5) : D ρ ≠ 0 ↔ f ρ = 0 := by
      have hn := ENat.natCast_toNat (htop ρ)
      rw [show D ρ = _ from hf'.divisor_apply hρ, ← hn,
        ← (hf ρ trivial).analyticOrderAt_ne_zero, ← hn]
      simp
    exact ⟨fun hρ ↦ ⟨D.supportWithinDomain hρ, (horder (D.supportWithinDomain hρ)).mp hρ⟩,
      fun ⟨hρ, h⟩ ↦ (horder hρ).mpr h⟩
  · exact_mod_cast (show (hfin.toFinset.card : ℤ) ≤ ∑ᶠ ρ, D ρ from by
      rw [finsum_eq_sum_of_support_subset _ (fun _ h ↦ hfin.mem_toFinset.mpr h)]
      calc
        _ = ∑ ρ ∈ hfin.toFinset, (1 : ℤ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun ρ hρ ↦ by
          have hne : D ρ ≠ 0 := hfin.mem_toFinset.mp hρ
          have hnn : 0 ≤ D ρ := hf'.divisor_nonneg ρ
          omega)

private theorem exists_ordinate_avoiding (S : Finset ℝ) (x δ : ℝ)
    (hδ : 0 < δ) (hcard : 2 * δ * (S.card : ℝ) ≤ 1 / 2) :
    ∃ T ∈ Ioo x (x + 1), ∀ y ∈ S, δ ≤ |T - y| := by
  let J (y : ℝ) := Ioo (y - δ) (y + δ)
  let B := ⋃ y ∈ S, J y
  have hB : volume B ≤ ENNReal.ofReal (1 / 2) := by
    calc
      volume B ≤ ∑ y ∈ S, volume (J y) := measure_biUnion_finset_le S J
      _ = ENNReal.ofReal (2 * δ * (S.card : ℝ)) := by
        simp only [J, Real.volume_Ioo, show ∀ y : ℝ, y + δ - (y - δ) = 2 * δ by intro; ring]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
        simp [mul_comm]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hcard
  obtain ⟨T, hT, hTB⟩ : ∃ T ∈ Ioo x (x + 1), T ∉ B := by
    by_contra! h
    have hle := (measure_mono h).trans hB
    rw [Real.volume_Ioo, show x + 1 - x = 1 by ring] at hle
    exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 (by norm_num))) hle
  refine ⟨T, hT, fun y hy ↦ ?_⟩
  by_contra! hclose
  obtain ⟨hl, hu⟩ := abs_lt.mp hclose
  exact hTB (mem_biUnion hy ⟨by linarith, by linarith⟩)

private theorem mem_horizontal_disk {z : ℂ} (hzl : -1 ≤ z.re) (hzu : z.re ≤ 2) :
    z ∈ closedBall (2 + (z.im : ℂ) * I) 3 := by
  rw [mem_closedBall, dist_eq_norm]
  have heq : z - (2 + (z.im : ℂ) * I) = ((z.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hzu)]
  linarith

private theorem dist_horizontal_center (s t : ℝ) :
    dist (2 + (s : ℂ) * I) (2 + (t : ℂ) * I) = |s - t| := by
  rw [dist_eq_norm, show (2 + (s : ℂ) * I - (2 + (t : ℂ) * I)) =
    ((s - t : ℝ) : ℂ) * I by push_cast; ring, norm_mul, norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- Counts in two fixed disks give one height for both moving disks. The
margin is inverse linear in the height budget; zeros outside the fixed disks
are already far from the edges. -/
public theorem exists_symmetric_horizontal_separation {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {C : ℝ} (hC : 0 < C)
    (hcount : ∀ t : ℝ, let c : ℂ := 2 + (t : ℂ) * I
      f c ≠ 0 ∧ ((∑ᶠ ρ, divisor f (closedBall c 5) ρ : ℤ) : ℝ) ≤ C * (1 + |t|))
    {x : ℝ} (hx : 1 ≤ x) :
    ∃ T ∈ Ioo x (x + 1), ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
      z ∈ closedBall (2 + (z.im : ℂ) * I) 3 ∧
      ∀ ρ : ℂ, f ρ = 0 → 1 / (16 * (C + 1) * (1 + x)) ≤ ‖z - ρ‖ := by
  classical
  let a : ℝ := x + 1 / 2
  let δ : ℝ := 1 / (16 * (C + 1) * (1 + x))
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hden : 1 ≤ 16 * (C + 1) * (1 + x) := by nlinarith [mul_nonneg hC.le (show 0 ≤ x by linarith)]
  have hδ₁ : δ ≤ 1 := (div_le_one (zero_lt_one.trans_le hden)).mpr hden
  obtain ⟨A, hA, hAcount⟩ := exists_diskZeros hf (hcount a).1
  obtain ⟨B, hB, hBcount⟩ := exists_diskZeros hf (hcount (-a)).1
  let S := A.image Complex.im ∪ B.image (fun ρ ↦ -ρ.im)
  have hS : (S.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  have hA' := hAcount.trans (hcount a).2
  have hB' := hBcount.trans (hcount (-a)).2
  rw [abs_of_nonneg ha] at hA'
  rw [abs_neg, abs_of_nonneg ha] at hB'
  have hS' : (S.card : ℝ) ≤ 4 * C * (1 + x) := by
    have hax : 1 + a ≤ 2 * (1 + x) := by dsimp [a]; linarith
    have hm := mul_le_mul_of_nonneg_left hax hC.le
    linarith
  have hcard : 2 * δ * (S.card : ℝ) ≤ 1 / 2 := by
    calc
      _ ≤ 2 * δ * (4 * C * (1 + x)) := by gcongr
      _ = C / (2 * (C + 1)) := by dsimp [δ]; field_simp; ring
      _ ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨T, hT, hsep⟩ := exists_ordinate_avoiding S x δ hδ hcard
  refine ⟨T, hT, fun z hzl hzu hz ↦ ⟨mem_horizontal_disk hzl hzu, ?_⟩⟩
  have hmid : |T - a| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [a]; linarith [hT.1],
    by dsimp [a]; linarith [hT.2]⟩
  have hout (t : ℝ) (ht : |z.im - t| ≤ 1 / 2) {ρ : ℂ}
      (hρ : ρ ∉ closedBall (2 + (t : ℂ) * I) 5) : δ ≤ ‖z - ρ‖ := by
    have hzm := mem_horizontal_disk hzl hzu
    rw [mem_closedBall] at hzm hρ
    have hzc : dist z (2 + (t : ℂ) * I) ≤ 3 + 1 / 2 :=
      (dist_triangle z (2 + (z.im : ℂ) * I) _).trans
        (add_le_add hzm (by rwa [dist_horizontal_center]))
    have := dist_triangle ρ z (2 + (t : ℂ) * I)
    rw [dist_comm ρ z, dist_eq_norm z ρ] at this
    linarith [lt_of_not_ge hρ]
  intro ρ hρ
  have him := abs_im_le_norm (z - ρ)
  rw [sub_im] at him
  by_cases hzpos : 0 ≤ z.im
  · have hzt : z.im = T := by rwa [abs_of_nonneg hzpos] at hz
    by_cases hρA : ρ ∈ closedBall (2 + (a : ℂ) * I) 5
    · have hi : ρ.im ∈ S := Finset.mem_union_left _
        (Finset.mem_image_of_mem _ ((hA ρ).2 ⟨hρA, hρ⟩))
      exact (hzt ▸ hsep ρ.im hi).trans him
    · exact hout a (hzt.symm ▸ hmid) hρA
  · have hzt : z.im = -T := by rw [abs_of_neg (lt_of_not_ge hzpos)] at hz; linarith
    by_cases hρB : ρ ∈ closedBall (2 + ((-a : ℝ) : ℂ) * I) 5
    · have hi : -ρ.im ∈ S := Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun w : ℂ ↦ -w.im) ((hB ρ).2 ⟨hρB, hρ⟩))
      apply le_trans _ him
      rw [hzt, show -T - ρ.im = -(T - -ρ.im) by ring, abs_neg]
      exact hsep _ hi
    · apply hout (-a) _ hρB
      rw [hzt, show -T - -a = -(T - a) by ring, abs_neg]
      exact hmid

/-- Undo the pole clearing on either horizontal edge at height of modulus
at least one. Both rational logarithmic derivative terms cost at most one. -/
public theorem nonzero_and_norm_logDeriv_le_of_poleCleared {L H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (hclear : ∀ w, w ≠ 0 → w ≠ 1 → H w = (w - 1) * w * L w)
    {z : ℂ} (hz : H z ≠ 0) (ht : 1 ≤ |z.im|) :
    L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ ‖logDeriv H z‖ + 2 := by
  have h0 : z ≠ 0 := by rintro rfl; norm_num at ht
  have h1 : z ≠ 1 := by rintro rfl; norm_num at ht
  have hL : L z ≠ 0 := by intro h; exact hz (by rw [hclear z h0 h1, h, mul_zero])
  refine ⟨hL, ?_⟩
  have heq : L =ᶠ[𝓝 z] fun w ↦ H w / ((w - 1) * w) := by
    filter_upwards [eventually_ne_nhds h0, eventually_ne_nhds h1] with w hw0 hw1
    rw [hclear w hw0 hw1, mul_comm, mul_div_cancel_right₀ _ (mul_ne_zero (sub_ne_zero.mpr hw1) hw0)]
  have hs := sub_ne_zero.mpr h1
  have hlog : logDeriv L z = logDeriv H z - 1 / (z - 1) - 1 / z := by
    rw [(logDeriv_congr_nhds heq).eq_of_nhds,
      logDeriv_fun_div (g := fun w : ℂ ↦ (w - 1) * w) z hz (mul_ne_zero hs h0)
        (hH z) (by fun_prop),
      logDeriv_fun_mul (f := fun w : ℂ ↦ w - 1) (g := fun w : ℂ ↦ w) z hs h0
        (by fun_prop) (by fun_prop), logDeriv_id', logDeriv_apply (fun w : ℂ ↦ w - 1)]
    have hd : deriv (fun w : ℂ ↦ w - 1) z = 1 := by simp
    rw [hd, sub_add_eq_sub_sub]
  have hp (w : ℂ) (hw : 1 ≤ |w.im|) : ‖1 / w‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hn := hw.trans (abs_im_le_norm w)
    exact (div_le_one (zero_lt_one.trans_le hn)).mpr hn
  have h₀ := hp z ht
  have h₁ := hp (z - 1) (by simpa using ht)
  rw [hlog]
  exact (norm_sub_le _ _).trans (by linarith [norm_sub_le (logDeriv H z) (1 / (z - 1))])

end Masullo
