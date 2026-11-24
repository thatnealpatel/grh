module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The short-cell LCM moment

Source: `8058479edd84:.godel/bob/short-cell-weil-list.md:33–37`, checked at
`52090c0259f5`. This is the arithmetic factor for applying (3) to the expanded
square. The moment includes every pair, even when `d = e`; the estimate does
not assume a character-sum bound or include the diagonal normalization in (2).

Owning check session: `01a20f88-43d7-7049-9647-cb18c5a08d70`.
-/

open Finset
open scoped BigOperators

namespace ShortCellLcmMoment

/-- The derivative of the concave power at the right endpoint is at most the
unit secant slope. Summing these inequalities gives the power-sum bound. -/
private theorem sum_rpow_sub_one_le {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (M : ℕ) :
    (∑ a ∈ Icc 1 M, (a : ℝ) ^ (s - 1)) ≤ (M : ℝ) ^ s / s := by
  have hstep (i : ℕ) :
      s * ((i + 1 : ℕ) : ℝ) ^ (s - 1) ≤ ((i + 1 : ℕ) : ℝ) ^ s - (i : ℝ) ^ s := by
    have hy : 0 < (i : ℝ) + 1 := by positivity
    have h := (Real.concaveOn_rpow hs.le hs₁).le_slope_of_hasDerivAt
      (x := (i : ℝ)) (y := (i : ℝ) + 1) (Nat.cast_nonneg _) hy.le (lt_add_one _)
      (Real.hasDerivAt_rpow_const (p := s) (Or.inl hy.ne'))
    simpa only [slope_def_field, add_sub_cancel_left, div_one, Nat.cast_add, Nat.cast_one] using h
  have hshift (f : ℕ → ℝ) : (∑ a ∈ Icc 1 M, f a) = ∑ i ∈ range M, f (i + 1) := by
    have hIcc : Icc 1 M = Ico 1 (M + 1) := by
      ext a
      simp
    rw [hIcc, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  apply (le_div_iff₀' hs).2
  rw [hshift, mul_sum]
  calc
    _ ≤ ∑ i ∈ range M, (((i + 1 : ℕ) : ℝ) ^ s - (i : ℝ) ^ s) :=
      sum_le_sum fun i _ ↦ hstep i
    _ = (M : ℝ) ^ s := by
      have hrange : range M = Ico 0 M := by
        ext i
        simp
      rw [hrange, sum_Ico_sub (fun i : ℕ ↦ (i : ℝ) ^ s) (Nat.zero_le M)]
      simp [Real.zero_rpow hs.ne']

private theorem lcm_eq_gcd_mul_divs {d e : ℕ} (hd : 0 < d) :
    d.lcm e = d.gcd e * (d / d.gcd e) * (e / d.gcd e) := by
  let g := d.gcd e
  change d.lcm e = g * (d / g) * (e / g)
  apply Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_left e hd)
  calc
    d.lcm e * g = d * e := Nat.lcm_mul_gcd d e
    _ = (d / g * g) * (e / g * g) := by
      rw [Nat.div_mul_cancel (show g ∣ d from Nat.gcd_dvd_left d e),
        Nat.div_mul_cancel (show g ∣ e from Nat.gcd_dvd_right d e)]
    _ = _ := by ac_rfl

/-- Reindex each pair by its gcd and reduced coordinates, then enlarge the
image to all positive reduced coordinates in the appropriate box. -/
private theorem moment_le_gcd_sum (s : ℝ) (N : ℕ) :
    (∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N, (d.lcm e : ℝ) ^ (s - 1)) ≤
      ∑ g ∈ Icc 1 N, (g : ℝ) ^ (s - 1) * (∑ a ∈ Icc 1 (N / g), (a : ℝ) ^ (s - 1)) ^ 2 := by
  let S := Icc 1 N
  let T (g : ℕ) := Icc 1 (N / g) ×ˢ Icc 1 (N / g)
  let F (p : ℕ × ℕ) : Σ _ : ℕ, ℕ × ℕ :=
    ⟨p.1.gcd p.2, (p.1 / p.1.gcd p.2, p.2 / p.1.gcd p.2)⟩
  let W (q : Σ _ : ℕ, ℕ × ℕ) : ℝ :=
    (q.1 : ℝ) ^ (s - 1) * ((q.2.1 : ℝ) ^ (s - 1) * (q.2.2 : ℝ) ^ (s - 1))
  calc
    _ = ∑ p ∈ S ×ˢ S, (p.1.lcm p.2 : ℝ) ^ (s - 1) :=
      (sum_product S S (fun p ↦ (p.1.lcm p.2 : ℝ) ^ (s - 1))).symm
    _ ≤ ∑ q ∈ S.sigma T, W q := by
      apply sum_le_sum_of_injOn F
      · intro p _ q _ hpq
        have h := congrArg (fun t : Σ _ : ℕ, ℕ × ℕ ↦ (t.2.1 * t.1, t.2.2 * t.1)) hpq
        simpa only [F, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _),
          Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), Prod.eta] using h
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
        obtain ⟨hd, hdN⟩ := mem_Icc.mp (mem_product.mp hp).1
        obtain ⟨he, heN⟩ := mem_Icc.mp (mem_product.mp hp).2
        have hg := Nat.gcd_pos_of_pos_left p.2 hd
        have hgd := Nat.gcd_le_left p.2 hd
        have hge := Nat.gcd_le_right p.1 he
        exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hg, hgd.trans hdN⟩, mem_product.mpr
          ⟨mem_Icc.mpr ⟨Nat.div_pos hgd hg, Nat.div_le_div_right hdN⟩,
           mem_Icc.mpr ⟨Nat.div_pos hge hg, Nat.div_le_div_right heN⟩⟩⟩
      · intro p hp
        have hd := (mem_Icc.mp (mem_product.mp hp).1).1
        dsimp only [F, W]
        rw [lcm_eq_gcd_mul_divs hd, Nat.cast_mul, Nat.cast_mul,
          Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), mul_assoc]
      · intro q _ _
        dsimp only [W]
        positivity
    _ = _ := by
      rw [sum_sigma]
      apply sum_congr rfl
      intro g _
      simp only [T, sum_product, W, ← mul_sum, ← sum_mul, pow_two]

private theorem gcd_term_le {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) {N g : ℕ}
    (hN : 1 ≤ N) (hg : 1 ≤ g) :
    (g : ℝ) ^ (s - 1) * (∑ a ∈ Icc 1 (N / g), (a : ℝ) ^ (s - 1)) ^ 2 ≤
      ((N : ℝ) ^ (2 * s) / s ^ 2) * (g : ℝ) ^ (-1 - s) := by
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0 < g from hg)
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N from hN)
  have hcast : ((N / g : ℕ) : ℝ) ≤ (N : ℝ) / (g : ℝ) := by
    apply (le_div_iff₀ hgR).2
    exact_mod_cast Nat.div_mul_le_self N g
  have hsum : (∑ a ∈ Icc 1 (N / g), (a : ℝ) ^ (s - 1)) ≤
      ((N : ℝ) / (g : ℝ)) ^ s / s :=
    (sum_rpow_sub_one_le hs hs₁ (N / g)).trans
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hcast hs.le) hs.le)
  calc
    _ ≤ (g : ℝ) ^ (s - 1) * (((N : ℝ) / (g : ℝ)) ^ s / s) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum 2) (by positivity)
    _ = _ := by
      rw [Real.div_rpow hNR.le hgR.le, div_eq_mul_inv ((N : ℝ) ^ s), ← Real.rpow_neg hgR.le]
      calc
        _ = (((N : ℝ) ^ s * (N : ℝ) ^ s) / s ^ 2) *
              (((g : ℝ) ^ (s - 1) * (g : ℝ) ^ (-s)) * (g : ℝ) ^ (-s)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hNR, ← Real.rpow_add hgR, ← Real.rpow_add hgR,
            show s + s = 2 * s by ring, show (s - 1 + -s) + -s = -1 - s by ring]

public section

/-- The unconditional LCM moment at positive natural cutoffs, with one
positive real constant for each integer `r ≥ 2`. -/
theorem lcm_moment_natCutoff (r : ℤ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 N, (d.lcm e : ℝ) ^ (-1 + 1 / (r : ℝ))) ≤
        C * (N : ℝ) ^ (2 / (r : ℝ)) := by
  let s : ℝ := 1 / (r : ℝ)
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have hs : 0 < s := one_div_pos.mpr hrpos
  have hs₁ : s ≤ 1 := (div_le_iff₀ hrpos).2 (by linarith)
  let f (g : ℕ) : ℝ := (g : ℝ) ^ (-1 - s)
  have hf : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have hf₀ (g : ℕ) : 0 ≤ f g := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let A : ℝ := ∑' g : ℕ, f g
  have hA : 0 ≤ A := tsum_nonneg hf₀
  refine ⟨(A + 1) / s ^ 2, by positivity, ?_⟩
  intro N hN
  rw [show -1 + 1 / (r : ℝ) = s - 1 by dsimp [s]; ring,
    show 2 / (r : ℝ) = 2 * s by dsimp [s]; ring]
  calc
    _ ≤ ∑ g ∈ Icc 1 N, (g : ℝ) ^ (s - 1) * (∑ a ∈ Icc 1 (N / g), (a : ℝ) ^ (s - 1)) ^ 2 :=
      moment_le_gcd_sum s N
    _ ≤ ∑ g ∈ Icc 1 N, ((N : ℝ) ^ (2 * s) / s ^ 2) * f g :=
      sum_le_sum fun g hg ↦ gcd_term_le hs hs₁ hN (mem_Icc.mp hg).1
    _ = ((N : ℝ) ^ (2 * s) / s ^ 2) * ∑ g ∈ Icc 1 N, f g := by rw [mul_sum]
    _ ≤ ((N : ℝ) ^ (2 * s) / s ^ 2) * (A + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (hf.sum_le_tsum (Icc 1 N) (fun g _ ↦ hf₀ g)).trans (by linarith)
    _ = _ := by ring

/-- The short-cell LCM moment for real cutoffs `z ≥ 1`. The interval ending at
`⌊z⌋₊` contains exactly the positive natural numbers at most `z`. -/
theorem lcm_moment_realCutoff (r : ℤ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z →
      (∑ d ∈ Icc 1 ⌊z⌋₊, ∑ e ∈ Icc 1 ⌊z⌋₊, (d.lcm e : ℝ) ^ (-1 + 1 / (r : ℝ))) ≤
        C * z ^ (2 / (r : ℝ)) := by
  obtain ⟨C, hC, hmoment⟩ := lcm_moment_natCutoff r hr
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hz₀ : 0 ≤ z := zero_le_one.trans hz
  have hfloor : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hz)
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  exact (hmoment ⌊z⌋₊ hfloor).trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hz₀) (by positivity)) hC.le

end

end ShortCellLcmMoment
