module

public import Lemmas.SignedSuccessorGrid
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cutoff-independent signed successor price

Source: `ac8b771857b16d36dcc380c4ca3990f33a4f5e1d:.godel/bob/finite-successor-cap.md`,
lines 30 and 36–40, with `.godel/bob/check-finite-successor-cap.py`, lines 25–60.
The local inequality is used in the averaging argument at lines 42–49, which
feeds the comparison in `.godel/bob/selected-cell-comparison.md`, lines 25–27.

Scope: only the pointwise price on the full closed square `|a|, |b| ≤ π/2`.
The mesh has width `π/96`; all 97 × 97 nodes are checked using integers.
The kernel also checks the cosine table against a rational Taylor polynomial,
whose real error is bounded analytically. No rounded floating-point values
are trusted. This does not formalize averaging, PNT, or a finite cutoff fixture.

Owning check session: `01a20bcd-0340-73f5-9604-3b5724a0ee86`.
-/

namespace Masullo.SignedSuccessorCertificate

open Masullo.SignedSuccessorPrice (U phase deficit)
open scoped Nat

private noncomputable def branch (s t : ℝ) (a b : ℝ) : ℂ :=
  ((3 / 10 * s : ℝ) : ℂ) * phase (-a) + ((4 / 10 : ℝ) : ℂ) +
    ((3 / 10 * t : ℝ) : ℂ) * phase b

private theorem branch_sq (s t a b : ℝ) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) :
    ‖branch s t a b‖ ^ 2 = (34 + 24 * s * Real.cos a + 24 * t * Real.cos b +
      18 * s * t * Real.cos (a + b)) / 100 := by
  rw [Complex.sq_norm, Complex.normSq_apply, branch]
  simp only [phase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Real.cos_add]
  linear_combination (9 / 100 * s ^ 2) * Real.sin_sq_add_cos_sq a +
    (9 / 100 * t ^ 2) * Real.sin_sq_add_cos_sq b + (9 / 100) * hs + (9 / 100) * ht

private theorem U_le_of_branches (a b R : ℝ)
    (h : ∀ s t : ℝ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) → ‖branch s t a b‖ ≤ R) :
    U a b ≤ R := by
  unfold U
  dsimp only
  simp only [max_le_iff]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa [branch] using h 1 1 (Or.inl rfl) (Or.inl rfl)
  · simpa [branch, sub_eq_add_neg] using h 1 (-1) (Or.inl rfl) (Or.inr rfl)
  · simpa [branch, sub_eq_add_neg] using h (-1) 1 (Or.inr rfl) (Or.inl rfl)
  · simpa [branch, sub_eq_add_neg] using h (-1) (-1) (Or.inr rfl) (Or.inr rfl)

private noncomputable def step : ℝ := Real.pi / 96

private noncomputable def node (p : ℤ) : ℝ := (p : ℝ) * step

private theorem step_pos : 0 < step := by unfold step; positivity

private theorem node_succ (p : ℤ) : node (p + 1) = node p + step := by
  unfold node
  push_cast
  ring

private theorem exists_cell {a : ℝ} (ha : |a| ≤ Real.pi / 2) :
    ∃ p : ℤ, -48 ≤ p ∧ p ≤ 47 ∧ a ∈ Set.Icc (node p) (node p + step) := by
  -- At the right endpoint, use cell 47, whose upper node is 48.
  let f := ⌊a / step⌋
  let p := min f 47
  have hleft : (-48 : ℝ) ≤ a / step := by
    rw [le_div_iff₀ step_pos]
    linarith only [(abs_le.mp ha).1, show step = Real.pi / 96 from rfl]
  have hright : a / step ≤ (48 : ℝ) := by
    rw [div_le_iff₀ step_pos]
    linarith only [(abs_le.mp ha).2, show step = Real.pi / 96 from rfl]
  refine ⟨p, ?_, min_le_right _ _, ?_⟩
  · exact le_min (Int.le_floor.mpr (by exact_mod_cast hleft)) (by norm_num)
  · have hpf : p ≤ f := min_le_left _ _
    have hple : (p : ℝ) ≤ a / step :=
      (Int.cast_le.mpr hpf).trans (Int.floor_le _)
    have hpge : a / step ≤ (p : ℝ) + 1 := by
      rcases le_total f 47 with h | h
      · simpa only [p, min_eq_left h] using (Int.lt_floor_add_one (a / step)).le
      · norm_num [p, min_eq_right h]; exact hright
    refine ⟨(le_div_iff₀ step_pos).mp hple, ?_⟩
    convert (div_le_iff₀ step_pos).mp hpge using 1
    unfold node
    ring

private theorem interpolation_error :
    step ^ 2 * (3 * (1 : ℝ) / 5 + (473 / 1000 + 473 / 1000) / 4 + 8 * (315 / 10000)) / 8
      ≤ 1 / 5000 := by
  have hh : step ≤ 33 / 1000 := by unfold step; linarith only [Real.pi_lt_d20]
  have hh2 : step ^ 2 ≤ (33 / 1000 : ℝ) ^ 2 := by gcongr; exact step_pos.le
  nlinarith only [hh2]

private noncomputable def taylor (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
    x ^ 12 / 479001600 - x ^ 14 / 87178291200

private theorem taylor_error {x : ℝ} (hx : x ∈ Set.Icc 0 (8 / 5)) :
    |Real.cos x - taylor x| ≤ 1 / 10000000 := by
  let I := Set.Icc (0 : ℝ) (8 / 5)
  have hwithin (n : ℕ) {y : ℝ} (hy : y ∈ I) :
      iteratedDerivWithin n Real.cos I y = iteratedDeriv n Real.cos y :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      Real.contDiff_cos.contDiffAt hy
  have hzero : (0 : ℝ) ∈ I := by norm_num [I]
  have hTaylor : taylorWithinEval Real.cos 14 I 0 x = taylor x := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hwithin _ hzero, iteratedDeriv_eq_iterate,
      Function.iterate_succ_apply', Real.deriv_cos, Real.deriv_sin, deriv.neg, Nat.factorial,
      taylor]; ring
  have hderiv (y : ℝ) (hy : y ∈ I) : ‖iteratedDerivWithin 15 Real.cos I y‖ ≤ 1 := by
    rw [hwithin _ hy, iteratedDeriv_eq_iterate]
    simpa [Function.iterate_succ_apply', Real.deriv_cos, Real.deriv_sin, deriv.neg,
      Real.norm_eq_abs] using Real.abs_sin_le_one y
  have hrem := taylor_mean_remainder_bound (n := 14) (C := 1)
    Real.contDiff_cos.contDiffOn hx hderiv
  rw [Real.norm_eq_abs, hTaylor, sub_zero, one_mul] at hrem
  refine hrem.trans ((?_: x ^ 15 / (14 ! : ℝ) ≤ (8 / 5) ^ 15 / (14 ! : ℝ)).trans ?_)
  · gcongr
    · exact hx.1
    · exact hx.2
  · norm_num [Nat.factorial]

-- A rational approximation to nπ/192, with a uniform argument error on 0 ≤ n ≤ 96.
private noncomputable def approxArg (n : ℕ) : ℝ := 163624617 * (n : ℝ) / 10000000000

private def taylorDen : ℤ := 87178291200 * 10000000000 ^ 14

private def taylorNum (n : ℕ) : ℤ :=
  let y := (163624617 * (n : ℤ)) ^ 2
  let d : ℤ := 10000000000 ^ 2
  87178291200 * d ^ 7 - 43589145600 * y * d ^ 6 + 3632428800 * y ^ 2 * d ^ 5 -
    121080960 * y ^ 3 * d ^ 4 + 2162160 * y ^ 4 * d ^ 3 - 24024 * y ^ 5 * d ^ 2 +
    182 * y ^ 6 * d - y ^ 7

private theorem taylorNum_eq (n : ℕ) :
    (taylorNum n : ℝ) = (taylorDen : ℝ) * taylor (approxArg n) := by
  push_cast [taylorNum, taylorDen]
  unfold taylor approxArg
  ring

-- The 20-bit fields encode integer approximations to 10^6 cos(nπ/192),
-- in increasing n from the least significant field. Packing keeps reduction
-- of table lookups small; `taylorTest_verified` checks every field used.
private def cosPacked : ℕ :=
  1481934395659057203501459752724880013215483793323570241815642086330947812293519635175416077358015967921272620012626349678191813439689895896289073231760947733753872492042944193290997735585068292771519904044047009056859739845686584314164502053661222181738848375664660131491213503606615738520339708638412828625876350760892739715136494727331269224519135233869554876643403446639028822710090006774034330834917430696037435069104157542452329390560565471564313965134521270060888754107361206497691670127509139406914186914446752217042720537343529592489100252159577927251980406836857619008

private def cosEntry (n : ℕ) : ℤ := ((cosPacked >>> (20 * n)) % 1048576 : ℕ)

-- Translate into [-96, 96) at a cost of a sign, then use cosine evenness.
private def cosCode (i : ℤ) : ℤ :=
  let j := (i + 96) % 192 - 96
  let c := cosEntry j.natAbs
  if (i + 96) / 192 % 2 = 0 then c else -c

private def taylorCheck (N C D : ℤ) : Bool :=
  decide (4 * |1000000 * N - C * D| ≤ 3 * D)

private abbrev taylorTest (n : ℕ) : Bool := taylorCheck (taylorNum n) (cosEntry n) taylorDen

set_option maxRecDepth 3000 in
set_option maxHeartbeats 0 in
private theorem taylorTest_verified (n : ℕ) (hn : n ≤ 96) : taylorTest n = true := by
  interval_cases n <;> decide +kernel

private theorem add_abs_errors {a b c r s : ℝ} (h₁ : |a - b| ≤ r) (h₂ : |b - c| ≤ s) :
    |a - c| ≤ r + s := by
  exact (abs_sub_le a b c).trans (add_le_add h₁ h₂)

private theorem cosine_errors {x y z : ℝ} (h₁ : |x - y| ≤ 1 / 10000000)
    (h₂ : y ∈ Set.Icc 0 (8 / 5)) (h₃ : |taylor y - z| ≤ 3 / 4000000) :
    |Real.cos x - z| ≤ 1 / 1000000 := by
  have hc : |Real.cos x - Real.cos y| ≤ 1 / 10000000 :=
    (Real.abs_cos_sub_cos_le x y).trans h₁
  have hct : |Real.cos y - z| ≤ (1 / 10000000 : ℝ) + 3 / 4000000 :=
    add_abs_errors (taylor_error h₂) h₃
  exact (add_abs_errors hc hct).trans (by norm_num)

private theorem taylorTest_sound (N C D : ℤ) (f : ℝ)
    (hb : taylorCheck N C D = true)
    (hD : 0 < (D : ℝ)) (hN : (N : ℝ) = (D : ℝ) * f) :
    |f - (C : ℝ) / 1000000| ≤ 3 / 4000000 := by
  have hnum : 4 * |1000000 * N - C * D| ≤ 3 * D := of_decide_eq_true hb
  have hu : 4 * |1000000 * (N : ℝ) - (C : ℝ) * (D : ℝ)| ≤ 3 * (D : ℝ) := by
    exact_mod_cast hnum
  rw [hN, show (1000000 : ℝ) * ((D : ℝ) * f) - (C : ℝ) * (D : ℝ) =
      (D : ℝ) * (1000000 * (f - (C : ℝ) / 1000000)) by ring,
    abs_mul, abs_of_pos hD, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000000)] at hu
  by_contra! h
  have hm := mul_lt_mul_of_pos_left h hD
  nlinarith only [hu, hm]

private theorem approxArg_in_Icc (n : ℕ) (hn : n ≤ 96) : approxArg n ∈ Set.Icc 0 (8 / 5) := by
  have hn' : (n : ℝ) ≤ 96 := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  constructor <;> dsimp [approxArg] <;> linarith only [hn0, hn']

private theorem approxArg_error (n : ℕ) (hn : n ≤ 96) :
    |(n : ℝ) * (Real.pi / 192) - approxArg n| ≤ 1 / 10000000 := by
  have hn' : (n : ℝ) ≤ 96 := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hstep : -(1 / 1000000000) ≤ Real.pi / 192 - (163624617 / 10000000000) ∧
      Real.pi / 192 - (163624617 / 10000000000) ≤ 1 / 1000000000 := by
    constructor <;> linarith only [Real.pi_gt_d20, Real.pi_lt_d20]
  rw [show (n : ℝ) * (Real.pi / 192) - approxArg n = (n : ℝ) *
    (Real.pi / 192 - 163624617 / 10000000000) by unfold approxArg; ring]
  rw [abs_mul, abs_of_nonneg hn0]
  calc
    _ ≤ (n : ℝ) * (1 / 1000000000) := mul_le_mul_of_nonneg_left (abs_le.mpr hstep) hn0
    _ ≤ _ := by linarith only [hn']

private theorem taylorDen_pos : 0 < (taylorDen : ℝ) := by norm_num [taylorDen]

private theorem cosTable_error (n : ℕ) (hn : n ≤ 96) :
    |Real.cos ((n : ℝ) * (Real.pi / 192)) - (cosEntry n : ℝ) / 1000000| ≤ 1 / 1000000 :=
  @cosine_errors ((n : ℝ) * (Real.pi / 192)) (approxArg n) ((cosEntry n : ℝ) / 1000000)
    (approxArg_error n hn) (approxArg_in_Icc n hn)
    (taylorTest_sound (taylorNum n) (cosEntry n) taylorDen (taylor (approxArg n))
      (taylorTest_verified n hn) taylorDen_pos (taylorNum_eq n))

private theorem cosine_natAbs (j : ℤ) (w : ℝ) :
    Real.cos ((j : ℝ) * w) = Real.cos ((j.natAbs : ℝ) * w) := by
  rcases Int.natAbs_eq j with hp | hm
  · have h := congrArg (fun k : ℤ ↦ (k : ℝ)) hp
    simpa only [Int.cast_natCast] using congrArg (fun z : ℝ ↦ Real.cos (z * w)) h
  · have h := congrArg (fun k : ℤ ↦ (k : ℝ)) hm
    simp only [Int.cast_neg, Int.cast_natCast] at h
    rw [h, neg_mul, Real.cos_neg]

private theorem cosine_shift (i j q : ℤ) (h : i = j + 192 * q) :
    Real.cos ((i : ℝ) * (Real.pi / 192)) =
      (-1 : ℝ) ^ q * Real.cos ((j.natAbs : ℝ) * (Real.pi / 192)) := by
  rw [h]
  push_cast
  rw [show ((j : ℝ) + 192 * (q : ℝ)) * (Real.pi / 192) =
    (j : ℝ) * (Real.pi / 192) + (q : ℝ) * Real.pi by ring,
    Real.cos_add_int_mul_pi, cosine_natAbs]

private theorem fold_abs_error (q c : ℤ) (x e : ℝ) (h : |x - (c : ℝ) / 1000000| ≤ e) :
    |(-1 : ℝ) ^ q * x - ((if q % 2 = 0 then c else -c : ℤ) : ℝ) /
      1000000| ≤ e := by
  by_cases he : q % 2 = 0
  · rw [ite_eq_left he, (Int.even_iff.mpr he).neg_one_zpow, one_mul]
    exact h
  · have ho : Odd q := Int.odd_iff.mpr (by omega)
    rw [ite_eq_right he, ho.neg_one_zpow, neg_one_mul, Int.cast_neg, neg_div,
      show -x - -((c : ℝ) / 1000000) = -(x - (c : ℝ) / 1000000) by ring, abs_neg]
    exact h

private theorem cosCode_error (i : ℤ) :
    |Real.cos ((i : ℝ) * (Real.pi / 192)) - (cosCode i : ℝ) / 1000000| ≤ 1 / 1000000 := by
  let j := (i + 96) % 192 - 96
  let q := (i + 96) / 192
  have hj : -96 ≤ j ∧ j ≤ 96 := by dsimp [j]; omega
  have hn : j.natAbs ≤ 96 := by omega
  have hsplit : i = j + 192 * q := by
    have he := Int.emod_add_mul_ediv (i + 96) 192
    dsimp [j, q]
    omega
  rw [cosine_shift i j q hsplit]
  exact fold_abs_error q (cosEntry j.natAbs) _ _ (cosTable_error _ hn)

-- The node price is targetCode / (2 * 10^9). Subtract one integer unit
-- from each cosine code so that the node test uses a lower price.
private def targetCode (p q : ℤ) : ℤ :=
  53600000 + 946 * (cosCode p + cosCode q - 2) + 63 * (cosCode (4 * (p + q)) - 1)

-- The squared norm is bounded above by radiusCode / 10^8: the extra
-- 66 units account for the three cosine errors, with weights 24, 24, 18.
private def radiusCode (p q s t : ℤ) : ℤ :=
  34000066 + 24 * s * cosCode (2 * p) + 24 * t * cosCode (2 * q) +
    18 * s * t * cosCode (2 * (p + q))

private def cornerTest (p q : ℤ) : Bool :=
  let r := targetCode p q
  let a := 24 * cosCode (2 * p)
  let b := 24 * cosCode (2 * q)
  let c := 18 * cosCode (2 * (p + q))
  -- Group the four branches by whether their flank signs agree.
  let m := max (|a + b| + c) (|a - b| - c)
  decide (0 ≤ r) && decide (40000000000 * (34000066 + m) ≤ r ^ 2)

-- Check all 97 columns in each row, in separate kernel reductions.
private def rowTest (i : ℕ) : Bool :=
  (List.range 97).all fun j ↦ cornerTest ((i : ℤ) - 48) ((j : ℤ) - 48)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
private theorem rowTest_verified (i : ℕ) (hi : i < 97) : rowTest i = true := by
  interval_cases i <;> decide +kernel

private theorem cornerTest_verified (p q : ℤ) (hp : -48 ≤ p ∧ p ≤ 48)
    (hq : -48 ≤ q ∧ q ≤ 48) : cornerTest p q = true := by
  let i := (p + 48).natAbs
  let j := (q + 48).natAbs
  have hi : i < 97 := by dsimp [i]; omega
  have hj : j ∈ List.range 97 := by rw [List.mem_range]; dsimp [j]; omega
  have h := List.all_eq_true.mp (rowTest_verified i hi) j hj
  have ip : (i : ℤ) - 48 = p := by dsimp [i]; omega
  have jq : (j : ℤ) - 48 = q := by dsimp [j]; omega
  simpa only [ip, jq] using h

private theorem radiusCode_le_max (A B C s t : ℤ) (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) :
    s * A + t * B + s * t * C ≤ max (|A + B| + C) (|A - B| - C) := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · have h := (add_le_add_left (le_abs_self (A + B)) C).trans
      (le_max_left (|A + B| + C) (|A - B| - C))
    simpa only [one_mul] using h
  · have h := (sub_le_sub_right (le_abs_self (A - B)) C).trans
      (le_max_right (|A + B| + C) (|A - B| - C))
    convert h using 1; ring
  · have h := (sub_le_sub_right (neg_le_abs (A - B)) C).trans
      (le_max_right (|A + B| + C) (|A - B| - C))
    convert h using 1; ring
  · have h := (add_le_add_left (neg_le_abs (A + B)) C).trans
      (le_max_left (|A + B| + C) (|A - B| - C))
    convert h using 1; ring

private theorem radiusCode_verified (p q s t : ℤ) (hp : -48 ≤ p ∧ p ≤ 48)
    (hq : -48 ≤ q ∧ q ≤ 48) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    0 ≤ targetCode p q ∧ 40000000000 * radiusCode p q s t ≤ targetCode p q ^ 2 := by
  obtain ⟨h0, h1⟩ := Bool.and_eq_true_iff.mp (cornerTest_verified p q hp hq)
  refine ⟨of_decide_eq_true h0, ?_⟩
  have hle := radiusCode_le_max (24 * cosCode (2 * p)) (24 * cosCode (2 * q))
    (18 * cosCode (2 * (p + q))) s t hs ht
  have hle' := add_le_add_right hle 34000066
  have hc := (mul_le_mul_of_nonneg_left hle' (by norm_num : (0 : ℤ) ≤ 40000000000)).trans
    (of_decide_eq_true h1)
  convert hc using 1
  unfold radiusCode
  ring

private theorem node_cos_error (i : ℤ) (x : ℝ)
    (hx : x = (i : ℝ) * (Real.pi / 192)) :
    |Real.cos x - (cosCode i : ℝ) / 1000000| ≤ 1 / 1000000 :=
  hx ▸ cosCode_error i

private theorem branch_node_sq_le (p q s t : ℤ) (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) :
    ‖branch s t (node p) (node q)‖ ^ 2 ≤ (radiusCode p q s t : ℝ) / 100000000 := by
  have ha := node_cos_error (2 * p) (node p) (by unfold node step; push_cast; ring)
  have hb := node_cos_error (2 * q) (node q) (by unfold node step; push_cast; ring)
  have hab := node_cos_error (2 * (p + q)) (node p + node q)
    (by unfold node step; push_cast; ring)
  rw [branch_sq _ _ _ _ (by rcases hs with rfl | rfl <;> norm_num)
    (by rcases ht with rfl | rfl <;> norm_num)]
  have hpa := abs_le.mp ha
  have hpb := abs_le.mp hb
  have hpab := abs_le.mp hab
  unfold radiusCode
  push_cast
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    norm_num at * <;> linarith only [hpa.1, hpa.2, hpb.1, hpb.2, hpab.1, hpab.2]

private theorem branch_node_le (p q s t : ℤ) (hp : -48 ≤ p ∧ p ≤ 48)
    (hq : -48 ≤ q ∧ q ≤ 48) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    ‖branch s t (node p) (node q)‖ ≤ (targetCode p q : ℝ) / 2000000000 := by
  obtain ⟨hR, hsq⟩ := radiusCode_verified p q s t hp hq hs ht
  have hR' : (0 : ℝ) ≤ (targetCode p q : ℝ) := by exact_mod_cast hR
  have hsq' : 40000000000 * (radiusCode p q s t : ℝ) ≤ (targetCode p q : ℝ) ^ 2 := by
    exact_mod_cast hsq
  rw [← sq_le_sq₀ (norm_nonneg _) (div_nonneg hR' (by norm_num))]
  refine (branch_node_sq_le p q s t hs ht).trans ?_
  nlinarith only [hsq']

private theorem node_bound (p q : ℤ) (hp : -48 ≤ p ∧ p ≤ 48)
    (hq : -48 ≤ q ∧ q ≤ 48) :
    U (node p) (node q) ≤ 268 / 10000 +
      946 / 1000 * (Real.cos (node p / 2) + Real.cos (node q / 2)) / 2 +
      315 / 10000 * Real.cos (2 * (node p + node q)) := by
  have hU : U (node p) (node q) ≤ (targetCode p q : ℝ) / 2000000000 := by
    apply U_le_of_branches
    intro s t hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · simpa using branch_node_le p q 1 1 hp hq (Or.inl rfl) (Or.inl rfl)
    · simpa using branch_node_le p q 1 (-1) hp hq (Or.inl rfl) (Or.inr rfl)
    · simpa using branch_node_le p q (-1) 1 hp hq (Or.inr rfl) (Or.inl rfl)
    · simpa using branch_node_le p q (-1) (-1) hp hq (Or.inr rfl) (Or.inr rfl)
  apply hU.trans
  have ha := node_cos_error p (node p / 2) (by unfold node step; ring)
  have hb := node_cos_error q (node q / 2) (by unfold node step; ring)
  have hc := node_cos_error (4 * (p + q)) (2 * (node p + node q))
    (by unfold node step; push_cast; ring)
  unfold targetCode
  push_cast
  linarith only [(abs_le.mp ha).1, (abs_le.mp hb).1, (abs_le.mp hc).1]

private theorem node_score_le (p q : ℤ) (hp : -48 ≤ p ∧ p ≤ 48)
    (hq : -48 ≤ q ∧ q ≤ 48) :
    SignedSuccessorGrid.score 1 (473 / 1000) (473 / 1000) (315 / 10000) (node p) (node q) ≤
      -(272 / 10000) := by
  unfold SignedSuccessorGrid.score deficit
  linarith only [node_bound p q hp hq]

/-- The cutoff-independent signed successor price on the closed angular square.
The certified grid intercept `0.0268` plus the interpolation error `0.0002`
gives the stated intercept `0.027`. -/
public theorem upper_of_abs_le_pi_div_two (a b : ℝ) (ha : |a| ≤ Real.pi / 2)
    (hb : |b| ≤ Real.pi / 2) :
    U a b ≤ 27 / 1000 + 946 / 1000 * (Real.cos (a / 2) + Real.cos (b / 2)) / 2 +
      315 / 10000 * Real.cos (2 * (a + b)) := by
  obtain ⟨p, hp0, hp1, hpa⟩ := exists_cell ha
  obtain ⟨q, hq0, hq1, hqb⟩ := exists_cell hb
  have hgrid := SignedSuccessorGrid.score_le_corner_max_add_error
    (c := 1) (A := 473 / 1000) (B := 473 / 1000) (T := 315 / 10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) step_pos hpa hqb
  rw [← node_succ p, ← node_succ q] at hgrid
  have hc : ∀ P Q : ℤ, -48 ≤ P ∧ P ≤ 48 → -48 ≤ Q ∧ Q ≤ 48 → _ := node_score_le
  have hm := max_le (max_le (hc p q (by omega) (by omega)) (hc p (q + 1) (by omega) (by omega)))
    (max_le (hc (p + 1) q (by omega) (by omega)) (hc (p + 1) (q + 1) (by omega) (by omega)))
  have hscore := hgrid.trans (add_le_add hm interpolation_error)
  unfold SignedSuccessorGrid.score deficit at hscore
  linarith only [hscore]

end Masullo.SignedSuccessorCertificate
