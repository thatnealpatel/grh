module

public import Examples.Chi8RectangleResidues
import Lemmas.AnalyticGoodHeightDisk
import Lemmas.AnalyticHorizontalHeights
import Lemmas.DirichletLRightLine
import Props.GammaRealLogDerivative

/-!
# Expanding residue rectangles for the conductor-eight endpoint budget

The two horizontal edges are estimated separately at a common good height.
On their fixed-width middle segment, moving-disk bounds control the bare
logarithmic derivative. The long shoulders and both moving vertical edges
instead use a uniform right-half-plane estimate for the completed derivative
and reflection. No cancellation between edges is required.
-/

open Complex Filter Set Metric DirichletCharacter MeasureTheory
open scoped Topology Interval

namespace Chi8ZeroBudget

local notation "χ" => Chi8Origin.χ
local notation "L" => LFunction χ
local notation "E" => Chi8Entire.Λ
local notation "D" => logDeriv E

private noncomputable def integrand (z : ℂ) : ℂ := D z / (z * (1 - z))

private theorem sqrt_four_mul {T : ℝ} : Real.sqrt (4 * T) = 2 * Real.sqrt T := by
  have h : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h]

-- Use the weaker linear count for the height selector, but retain a square-root
-- upper bound for the divisor mass when estimating the log derivative.
private theorem exists_good_middle : ∃ B : ℝ, 0 < B ∧ ∀ H : ℝ, 2 ≤ H →
    ∃ T ∈ Ioo H (H + 1), ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → |z.im| = T →
      L z ≠ 0 ∧ ‖logDeriv L z‖ ≤ B * (T * Real.sqrt T) := by
  obtain ⟨A, hA, hJ⟩ := Chi8Origin.exists_moving_disk_bounds
  let k := A + 12
  let l := Real.log (6 / 5 : ℝ)
  let C := k / l
  have hl : 0 < l := Real.log_pos (by norm_num)
  have hk : 0 < k := by dsimp [k]; linarith
  have hC : 0 < C := div_pos hk hl
  have hf : AnalyticOnNhd ℂ L univ := fun z _ ↦ (differentiable_LFunction Chi8Origin.χ_ne_one).analyticAt z
  have hU (t : ℝ) : A + 6 * Real.log (1 + |t|) ≤ k * Real.sqrt (1 + |t|) := by
    have hx : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hs := Real.sqrt_le_sqrt hx
    rw [Real.sqrt_one] at hs
    have h := Real.log_le_rpow_div (zero_le_one.trans hx) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    dsimp [k]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hs)]
  have hcount (t : ℝ) : let c : ℂ := 2 + (t : ℂ) * I
      L c ≠ 0 ∧ ((∑ᶠ ρ, MeromorphicOn.divisor L (closedBall c 5) ρ : ℤ) : ℝ) ≤
      C * (1 + |t|) := by
    obtain ⟨_, _, hc, _, _, hn⟩ := hJ t
    refine ⟨hc, hn.trans ?_⟩
    rw [show C * (1 + |t|) = k * (1 + |t|) / l by dsimp [C]; ring]
    apply div_le_div_of_nonneg_right _ hl.le
    refine (hU t).trans (mul_le_mul_of_nonneg_left ?_ hk.le)
    calc
      _ ≤ Real.sqrt ((1 + |t|) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg |t|, abs_nonneg t])
      _ = _ := Real.sqrt_sq (by positivity)
  refine ⟨8 * (2 * k + 2 * C * Real.log 5 + 1) + 64 * C * (C + 1), by positivity,
    fun H hH ↦ ?_⟩
  obtain ⟨T, hT, hsep⟩ := Masullo.exists_symmetric_horizontal_separation hf hC hcount
    (show 1 ≤ H by linarith)
  have hT₂ : 2 ≤ T := hH.trans hT.1.le
  have hST : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt (show 1 ≤ T by linarith)
  have hS : Real.sqrt (1 + T) ≤ 2 * Real.sqrt T := by
    calc
      _ ≤ Real.sqrt (4 * T) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := sqrt_four_mul
  let δ := 1 / (16 * (C + 1) * (1 + H))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨T, hT, fun z hz₁ hz₂ hzT ↦ ?_⟩
  obtain ⟨hz, hdist⟩ := hsep z hz₁ hz₂ hzT
  obtain ⟨M, hM, hc, hbd, hu, hn⟩ := hJ z.im
  have hu' : Real.log (M / ‖L (2 + (z.im : ℂ) * I)‖) ≤ 2 * k * Real.sqrt T := by
    refine hu.trans ((hU z.im).trans ?_)
    rw [hzT]
    nlinarith only [mul_le_mul_of_nonneg_left hS hk.le]
  have hn' : ((∑ᶠ ρ, MeromorphicOn.divisor L (closedBall (2 + (z.im : ℂ) * I) 5) ρ : ℤ) : ℝ) ≤
      2 * C * Real.sqrt T := by
    refine hn.trans ((div_le_iff₀ hl).mpr ?_)
    rw [hzT]
    have h := hU z.im
    rw [hzT] at h
    have hEq : (2 * C * Real.sqrt T) * l = k * (2 * Real.sqrt T) := by
      dsimp [C]; field_simp
    rw [hEq]
    exact h.trans (mul_le_mul_of_nonneg_left hS hk.le)
  refine ⟨fun h ↦ hδ.not_ge (show δ ≤ 0 by simpa only [sub_self, norm_zero] using hdist z h), ?_⟩
  refine (Masullo.norm_logDeriv_le_of_moving_disk_bounds hf hc hM hbd hu' hn' hz hδ
    (fun ρ _ h ↦ hdist ρ h)).trans ?_
  have h₁ : 8 * (2 * k * Real.sqrt T + 2 * C * Real.sqrt T * Real.log 5 + 1) ≤
      8 * (2 * k + 2 * C * Real.log 5 + 1) * (T * Real.sqrt T) := by
    have he : 8 * (2 * k * Real.sqrt T + 2 * C * Real.sqrt T * Real.log 5 + 1) ≤
        (8 * (2 * k + 2 * C * Real.log 5 + 1)) * Real.sqrt T := by nlinarith
    refine he.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact le_mul_of_one_le_left (by positivity) (by linarith)
  have h₂ : 2 * C * Real.sqrt T / δ ≤ 64 * C * (C + 1) * (T * Real.sqrt T) := by
    dsimp [δ]
    rw [div_div_eq_mul_div, div_one]
    calc
      _ = (32 * C * (C + 1) * Real.sqrt T) * (1 + H) := by ring
      _ ≤ (32 * C * (C + 1) * Real.sqrt T) * (2 * T) :=
        mul_le_mul_of_nonneg_left (by linarith [hT.1]) (by positivity)
      _ = _ := by ring
  linarith [add_le_add h₁ h₂]

private theorem norm_integrand_reflect (z : ℂ) : ‖integrand (1 - z)‖ = ‖integrand z‖ := by
  rw [integrand, integrand, Chi8Entire.logDeriv_one_sub, sub_sub_cancel, mul_comm (1 - z), neg_div, norm_neg]

private theorem norm_integrand_le {z : ℂ} {r M : ℝ} (hr : 0 < r) (hz : r ≤ ‖z‖)
    (h₁z : r ≤ ‖1 - z‖) (hM : ‖D z‖ ≤ M) : ‖integrand z‖ ≤ M / r ^ 2 := by
  rw [integrand, norm_div, norm_mul]
  exact div_le_div₀ ((norm_nonneg _).trans hM) hM (by positivity)
    (by simpa [pow_two] using mul_le_mul hz h₁z hr.le (norm_nonneg z))

private theorem norm_integrand_le_of_im {z : ℂ} {T M : ℝ} (hT : 0 < T)
    (hz : |z.im| = T) (hM : ‖D z‖ ≤ M) : ‖integrand z‖ ≤ M / T ^ 2 :=
  norm_integrand_le hT (hz ▸ abs_im_le_norm z)
    (by simpa [sub_im, hz] using abs_im_le_norm (1 - z)) hM

private theorem continuousAt_integrand {z : ℂ} (hE : E z ≠ 0) (hz : z ≠ 0) (h₁z : z ≠ 1) :
    ContinuousAt integrand z := by
  have h := Chi8Entire.differentiable.analyticAt z
  exact (h.deriv.div h hE |>.continuousAt).div (by fun_prop)
    (mul_ne_zero hz (sub_ne_zero.mpr h₁z.symm))

private theorem sqrt_coordinate_bound {T : ℝ} (hT : 2 ≤ T) {z : ℂ}
    (hr : |z.re| ≤ T) (hi : |z.im| ≤ T) :
    Real.sqrt (2 + |z.re| + |z.im|) ≤ 2 * Real.sqrt T := by
  calc
    _ ≤ Real.sqrt (4 * T) := Real.sqrt_le_sqrt (by linarith)
    _ = _ := sqrt_four_mul

private theorem exists_norm_logDeriv_completion_bounds :
    ∃ B G : ℝ, 0 < B ∧ 0 < G ∧ ∀ T : ℝ, 2 ≤ T → ∀ z : ℂ,
      (1 / 2 : ℝ) ≤ z.re → z.re ≤ T → |z.im| ≤ T →
      (2 ≤ z.re → ‖D z‖ ≤ B * Real.sqrt T) ∧
      (L z ≠ 0 → ‖D z‖ ≤ G * Real.sqrt T + ‖logDeriv L z‖) := by
  obtain ⟨g, hg, hΓ⟩ := Masullo.exists_norm_logDeriv_GammaReal_le_sqrt
  obtain ⟨b, hb, hL⟩ := Masullo.exists_norm_logDeriv_dirichletL_le χ (a := 2) (by norm_num)
  let A := ‖(Real.log 8 : ℂ) / 2‖
  let G := A + 2 * g
  have hG : 0 < G := by dsimp [G, A]; positivity
  refine ⟨G + b, G, by positivity, hG, fun T hT z h₁ h₂ hi ↦ ?_⟩
  have hs : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt (show 1 ≤ T by linarith)
  have hγ := (hΓ z h₁).trans (mul_le_mul_of_nonneg_left
    (sqrt_coordinate_bound hT (by rwa [abs_of_nonneg (by linarith)]) hi) hg.le)
  have hD (hz : L z ≠ 0) : ‖D z‖ ≤ G * Real.sqrt T + ‖logDeriv L z‖ := by
    rw [Chi8Entire.logDeriv_eq_of_re_pos (by linarith) hz]
    refine (norm_add_le _ _).trans ?_
    have hh := (norm_add_le ((Real.log 8 : ℂ) / 2) _).trans (by
      gcongr : A + ‖logDeriv Gammaℝ z‖ ≤ A + g * (2 * Real.sqrt T))
    dsimp [G]
    nlinarith only [hh, mul_nonneg (show 0 ≤ A from norm_nonneg _) (sub_nonneg.mpr hs)]
  refine ⟨fun hz ↦ ?_, hD⟩
  have h : ‖D z‖ ≤ G * Real.sqrt T + b := (hD (LFunction_ne_zero_of_one_le_re χ
    (Or.inl Chi8Origin.χ_ne_one) (by linarith))).trans (by gcongr; exact hL z hz)
  nlinarith only [h, mul_nonneg hb (sub_nonneg.mpr hs)]

private theorem horizontal_integral_le {T t B M : ℝ} (hT : 2 < T)
    (hB : 0 ≤ B)
    (hcont : ContinuousOn (fun x : ℝ ↦ integrand (x + t * I)) (Icc (1 - T) T))
    (hnear : ∀ x : ℝ, x ∈ Icc (-1) 2 → ‖integrand (x + t * I)‖ ≤ M / Real.sqrt T)
    (hleft : ∀ x ∈ Icc (1 - T) (-1), ‖integrand (x + t * I)‖ ≤ B / (T * Real.sqrt T))
    (hright : ∀ x ∈ Icc 2 T, ‖integrand (x + t * I)‖ ≤ B / (T * Real.sqrt T)) :
    ‖∫ x in (1 - T)..T, integrand (x + t * I)‖ ≤ (2 * B + 3 * M) / Real.sqrt T := by
  let f := fun x : ℝ ↦ integrand (x + t * I)
  have hT₁ : 1 - T ≤ -1 := by linarith
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 (by linarith)
  have i₁ : IntervalIntegrable f volume (1 - T) (-1) :=
    (hcont.mono (by rw [uIcc_of_le hT₁]; exact Icc_subset_Icc_right (by linarith))).intervalIntegrable
  have i₂ : IntervalIntegrable f volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
    exact hcont.mono (Icc_subset_Icc hT₁ hT.le)
  have i₃ : IntervalIntegrable f volume 2 T :=
    (hcont.mono (by rw [uIcc_of_le hT.le]; exact Icc_subset_Icc_left (by linarith))).intervalIntegrable
  have b₁ := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := 1 - T) (b := -1) fun x hx ↦
    hleft x (by simpa only [uIcc_of_le hT₁] using uIoc_subset_uIcc hx)
  have b₂ := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := -1) (b := 2) fun x hx ↦
    hnear x (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using uIoc_subset_uIcc hx)
  have b₃ := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := 2) (b := T) fun x hx ↦
    hright x (by simpa only [uIcc_of_le hT.le] using uIoc_subset_uIcc hx)
  change ‖∫ x in (1 - T)..T, f x‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (i₁.trans i₂) i₃,
    ← intervalIntegral.integral_add_adjacent_intervals i₁ i₂]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  refine (add_le_add (add_le_add b₁ b₂) b₃).trans ?_
  rw [abs_of_nonneg (show 0 ≤ -1 - (1 - T) by linarith),
    abs_of_nonneg (show 0 ≤ (2 : ℝ) - -1 by norm_num), abs_of_nonneg (sub_nonneg.mpr hT.le)]
  calc
    _ ≤ B / (T * Real.sqrt T) * T + M / Real.sqrt T * 3 + B / (T * Real.sqrt T) * T := by
      norm_num only [sub_neg_eq_add, Nat.reduceAdd]
      gcongr <;> linarith
    _ = _ := by field_simp [hs.ne', show T ≠ 0 by linarith]; ring

/-- One zero-free expanding rectangle for each height budget, with unconditional
boundary decay. Both vertical sides move, and the two horizontal edges share
the same absolute height. -/
public theorem exists_expanding_rectangle_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 2 ≤ H → ∃ T ∈ Ioo H (H + 1),
      (∀ z ∈ (Icc (1 - T) T ×ℂ Icc (-T) T) \ (Ioo (1 - T) T ×ℂ Ioo (-T) T), E z ≠ 0) ∧
      ‖Masullo.rectangleIntegral (1 - T) T (-T) T (fun s ↦ D s / (s * (1 - s)))‖ ≤
        K / Real.sqrt T := by
  obtain ⟨B, hB, hgood⟩ := exists_good_middle
  obtain ⟨A, G, hA, hG, hbounds⟩ := exists_norm_logDeriv_completion_bounds
  let M := G + B
  refine ⟨20 * A + 6 * M, by dsimp [M]; positivity, fun H hH ↦ ?_⟩
  obtain ⟨T, hT, hmiddle⟩ := hgood H hH
  have hT₂ : 2 < T := hH.trans_lt hT.1
  have hT₀ : 0 < T := by linarith
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT₀
  have hsq := Real.sq_sqrt hT₀.le
  have hnotH {z : ℂ} (hi : |z.im| = T) : E z ≠ 0 := by
    intro hz
    obtain ⟨h₁, h₂, hL⟩ := (Chi8Entire.zero_iff z).mp hz
    exact (hmiddle z (by linarith) (by linarith) hi).1 hL
  have hbd : ∀ z ∈ (Icc (1 - T) T ×ℂ Icc (-T) T) \ (Ioo (1 - T) T ×ℂ Ioo (-T) T), E z ≠ 0 := by
    intro z hz hE
    obtain ⟨h₁, h₂, _⟩ := (Chi8Entire.zero_iff z).mp hE
    obtain ⟨_, hi⟩ := mem_reProdIm.mp hz.1
    have hzi : |z.im| < T := lt_of_le_of_ne (abs_le.mpr hi) (fun he ↦ hnotH he hE)
    have hh := abs_lt.mp hzi
    exact hz.2 (mem_reProdIm.mpr ⟨⟨by linarith, by linarith⟩, hh⟩)
  refine ⟨T, hT, hbd, ?_⟩
  have hright {z : ℂ} (hr : 2 ≤ z.re) (hr' : z.re ≤ T) (hi : |z.im| ≤ T) :
      ‖D z‖ ≤ A * Real.sqrt T := (hbounds T hT₂.le z (by linarith) hr' hi).1 hr
  have hcore_pos {z : ℂ} (hr : (1 / 2 : ℝ) ≤ z.re) (hr' : z.re ≤ 2) (hi : |z.im| = T) :
      ‖integrand z‖ ≤ M / Real.sqrt T := by
    obtain ⟨hn, hl⟩ := hmiddle z (by linarith) hr' hi
    have hd := (hbounds T hT₂.le z hr (hr'.trans hT₂.le) hi.le).2 hn
    have hd' : ‖D z‖ ≤ M * (T * Real.sqrt T) := by
      have h : Real.sqrt T ≤ T * Real.sqrt T := le_mul_of_one_le_left hs.le (by linarith)
      dsimp [M]
      nlinarith only [hd, hl, mul_le_mul_of_nonneg_left h hG.le]
    refine (norm_integrand_le_of_im hT₀ hi hd').trans_eq ?_
    field_simp [hT₀.ne', hs.ne']
    ring_nf
    rw [hsq]
  have hcore {z : ℂ} (hr : -1 ≤ z.re) (hr' : z.re ≤ 2) (hi : |z.im| = T) :
      ‖integrand z‖ ≤ M / Real.sqrt T := by
    by_cases hz : (1 / 2 : ℝ) ≤ z.re
    · exact hcore_pos hz hr' hi
    · rw [← norm_integrand_reflect z]
      apply hcore_pos
      · simp only [sub_re, one_re]; linarith
      · simp only [sub_re, one_re]; linarith
      · simpa [sub_im] using hi
  have hshoulder {z : ℂ} (hr : 2 ≤ z.re) (hr' : z.re ≤ T) (hi : |z.im| = T) :
      ‖integrand z‖ ≤ A / (T * Real.sqrt T) := by
    refine (norm_integrand_le_of_im hT₀ hi (hright hr hr' hi.le)).trans_eq ?_
    field_simp [hT₀.ne', hs.ne']
    ring_nf
    rw [hsq]
  have hHorizontal (t : ℝ) (ht : |t| = T) :
      ‖∫ x in (1 - T)..T, integrand (x + t * I)‖ ≤ (2 * A + 3 * M) / Real.sqrt T := by
    have ht₀ : t ≠ 0 := fun h ↦ hT₀.ne' (by simpa [h] using ht.symm)
    apply horizontal_integral_le hT₂ hA.le
    · intro x _
      let z : ℂ := x + t * I
      have hi : |z.im| = T := by simpa [z] using ht
      have hz₀ : z ≠ 0 := fun h ↦ ht₀ (by simpa [z] using congrArg im h)
      have hz₁ : z ≠ 1 := fun h ↦ ht₀ (by simpa [z] using congrArg im h)
      have hp : ContinuousAt (fun x : ℝ ↦ (x : ℂ) + (t : ℂ) * I) x := by fun_prop
      exact ((continuousAt_integrand (hnotH hi) hz₀ hz₁).comp (x := x) hp).continuousWithinAt
    · intro x hx
      exact hcore (by simpa using hx.1) (by simpa using hx.2) (by simpa using ht)
    · intro x hx
      rw [← norm_integrand_reflect]
      apply hshoulder
      · simp; linarith [hx.2]
      · simp; linarith [hx.1]
      · simpa [sub_im] using ht
    · intro x hx
      exact hshoulder (by simpa using hx.1) (by simpa using hx.2) (by simpa using ht)
  have hV {z : ℂ} (hr : z.re = T) (hi : |z.im| ≤ T) :
      ‖integrand z‖ ≤ 4 * A / (T * Real.sqrt T) := by
    have hd := hright (hr ▸ hT₂.le) hr.le hi
    have hl := (show T / 2 ≤ |z.re| by rw [hr, abs_of_pos hT₀]; linarith).trans (abs_re_le_norm z)
    have hl' := (show T / 2 ≤ |(1 - z).re| by
      rw [sub_re, one_re, hr, abs_of_neg (by linarith)]; linarith).trans (abs_re_le_norm (1 - z))
    refine (norm_integrand_le (by positivity) hl hl' hd).trans_eq ?_
    field_simp [hT₀.ne', hs.ne']
    ring_nf
    rw [hsq]
  have hVertical {x : ℝ} (hx : x = T ∨ x = 1 - T) :
      ‖∫ y in -T..T, integrand (x + y * I)‖ ≤ 8 * A / Real.sqrt T := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * A / (T * Real.sqrt T))
      (fun y hy ↦ ?_)).trans_eq ?_
    · have hy' := uIoc_subset_uIcc hy
      rw [uIcc_of_le (show -T ≤ T by linarith)] at hy'
      have hi : |y| ≤ T := abs_le.mpr hy'
      rcases hx with rfl | rfl
      · exact hV (by simp) (by simpa using hi)
      · rw [← norm_integrand_reflect]
        exact hV (by simp) (by simpa [sub_im] using hi)
    · rw [abs_of_nonneg (show 0 ≤ T - -T by linarith)]
      field_simp [hT₀.ne', hs.ne']
      norm_num
  have hb := hHorizontal (-T) (by rw [abs_neg, abs_of_pos hT₀])
  have ht := hHorizontal T (abs_of_pos hT₀)
  have hr := hVertical (Or.inl rfl)
  have hl := hVertical (Or.inr rfl)
  change ‖Masullo.rectangleIntegral (1 - T) T (-T) T integrand‖ ≤ _
  rw [Masullo.rectangleIntegral]
  have hr' := norm_mul I (∫ y in -T..T, integrand (T + y * I))
  have hl' := norm_mul I (∫ y in -T..T, integrand (((1 - T : ℝ) : ℂ) + y * I))
  rw [norm_I, one_mul] at hr' hl'
  refine (norm_sub_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add hb ht)) (hr'.trans_le hr)))
    (hl'.trans_le hl)).trans ?_)
  apply le_of_eq
  ring

/-- The rectangles at heights in `(n+2,n+3)` have zero-free boundaries and
vanishing normalized contour integrals. Their widths grow with their heights. -/
public theorem exists_expanding_rectangles :
    ∃ T : ℕ → ℝ, (∀ n : ℕ, T n ∈ Ioo ((n : ℝ) + 2) ((n : ℝ) + 3)) ∧
      (∀ n : ℕ, ∀ z ∈ (Icc (1 - T n) (T n) ×ℂ Icc (-T n) (T n)) \
        (Ioo (1 - T n) (T n) ×ℂ Ioo (-T n) (T n)), E z ≠ 0) ∧
      Tendsto (fun n ↦ Masullo.rectangleIntegral (1 - T n) (T n) (-T n) (T n)
        (fun s ↦ D s / (s * (1 - s))) / (2 * Real.pi * I)) atTop (𝓝 0) := by
  obtain ⟨K, _, h⟩ := exists_expanding_rectangle_bound
  have hex (n : ℕ) := h ((n : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  choose T hT hbd hbound using hex
  refine ⟨T, fun n ↦ ?_, hbd, ?_⟩
  · exact ⟨(hT n).1, by linarith [(hT n).2]⟩
  have htop : Tendsto T atTop atTop := tendsto_atTop_mono
    (fun n ↦ by linarith [(hT n).1]) tendsto_natCast_atTop_atTop
  have h₀ : Tendsto (fun n ↦ K / Real.sqrt (T n)) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, Function.comp_apply, div_eq_mul_inv, mul_zero] using
      ((Real.tendsto_sqrt_atTop.comp htop).inv_tendsto_atTop.const_mul K)
  have hnorm := squeeze_zero (fun _ ↦ norm_nonneg _) hbound h₀
  have hlim : Tendsto (fun n ↦ Masullo.rectangleIntegral (1 - T n) (T n) (-T n) (T n)
      (fun s ↦ D s / (s * (1 - s)))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at hnorm ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hnorm ε hε
    exact ⟨N, fun n hn ↦ by simpa [dist_zero_right, Real.norm_eq_abs] using hN n hn⟩
  simpa only [zero_div] using hlim.div_const (2 * (Real.pi : ℂ) * I)

/-- Under the critical-line hypothesis alone, the unordered inverse-square
zero weights sum to the conductor-eight endpoint budget. -/
public theorem hasSum_weight_of_criticalLine
    (hline : ∀ ρ : Chi8ZeroKernel.Zero, (ρ : ℂ).re = 1 / 2) :
    HasSum Chi8ZeroKernel.weight C := by
  obtain ⟨T, hT, hbd, hlim⟩ := exists_expanding_rectangles
  let S (n : ℕ) := rectangleZeros (1 - T n) (T n) (-T n) (T n)
  have htop : Tendsto T atTop atTop := tendsto_atTop_mono
    (fun n ↦ by linarith [(hT n).1]) tendsto_natCast_atTop_atTop
  -- Cofinality for arbitrary finite subsets, rather than a height-ordered series.
  have hcofinal : Tendsto S atTop atTop := tendsto_atTop_atTop.mpr fun U ↦ by
    classical
    let A := 2 + ∑ ρ ∈ U, |(ρ : ℂ).im|
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp htop A
    refine ⟨N, fun n hn ρ hρ ↦ ?_⟩
    have hAbs : |(ρ : ℂ).im| ≤ ∑ ρ ∈ U, |(ρ : ℂ).im| :=
      Finset.single_le_sum (f := fun ρ : Chi8ZeroKernel.Zero ↦ |(ρ : ℂ).im|)
        (fun _ _ ↦ abs_nonneg _) hρ
    have hi : |(ρ : ℂ).im| < T n := by linarith [hN n hn]
    have ht : 2 < T n := by linarith [(hT n).1, Nat.cast_nonneg (α := ℝ) n]
    exact mem_rectangleZeros.mpr (mem_reProdIm.mpr
      ⟨⟨by linarith [ρ.property.1], by linarith [ρ.property.2.1]⟩, abs_lt.mp hi⟩)
  have hsum := summable_weight.hasSum
  have hs : Tendsto (fun U : Finset Chi8ZeroKernel.Zero ↦ ∑ ρ ∈ U, Chi8ZeroKernel.weight ρ)
      atTop (𝓝 (∑' ρ, Chi8ZeroKernel.weight ρ)) := hsum
  have hpartial := hs.comp hcofinal
  have hreal := (Complex.continuous_re.continuousAt (x := (0 : ℂ))).tendsto.comp hlim
  have hfinite (n : ℕ) : (Masullo.rectangleIntegral (1 - T n) (T n) (-T n) (T n)
        (fun s ↦ D s / (s * (1 - s))) / (2 * Real.pi * I)).re =
        (∑ ρ ∈ S n, Chi8ZeroKernel.weight ρ) - C := by
    have ht : 2 < T n := by linarith [(hT n).1, Nat.cast_nonneg (α := ℝ) n]
    exact re_rectangleIntegral_eq_sum_weight_sub_budget (by linarith) (by linarith)
      (by linarith) (by linarith) (hbd n) (fun ρ _ ↦ hline ρ)
  have hpartial' : Tendsto (fun n ↦ ∑ ρ ∈ S n, Chi8ZeroKernel.weight ρ) atTop (𝓝 C) := by
    have hreal' : Tendsto (fun n ↦ (∑ ρ ∈ S n, Chi8ZeroKernel.weight ρ) - C) atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_re, hfinite] using hreal
    simpa only [zero_add, sub_add_cancel] using hreal'.add_const C
  exact (tendsto_nhds_unique hpartial hpartial') ▸ hsum

end Chi8ZeroBudget
