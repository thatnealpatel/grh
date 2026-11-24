module

public import Lemmas.SignedCubeShell
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Frequency bound for the signed integer cube

Source: `dcc11ec5:.godel/bob/signed-gap-cube-screen.md:42–48`.
Owning check session: `01a20d4e-3533-70d0-b28a-ab27fa9217cc`.

The signed shifts here are the differences of the two ordered draws. The
lower band on the integer corners controls all the intervening segments,
including for negative shifts. This is the finite frequency estimate for
midpoint-cell screening, independent of cyclic-average identification or
asymptotic estimates.
-/

open scoped BigOperators
open Set

namespace Masullo.SignedCubeShell

open TriangularCubeDeletion TriangularCubeCoefficients

private def shiftSum {k : ℕ} (h : Fin k → ℝ) (s : Fin k → Bool) : ℝ :=
  ∑ i, if s i then h i else 0

private theorem shiftSum_cons {k : ℕ} (h : Fin (k + 1) → ℝ) (b : Bool)
    (s : Fin k → Bool) :
    shiftSum h (Fin.cons b s) = (if b then h 0 else 0) + shiftSum (Fin.tail h) s := by
  simp only [shiftSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail_def]

private noncomputable def cubeDiff : {k : ℕ} → (Fin k → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, f, p => f p
  | _ + 1, h, f, p => cubeDiff (Fin.tail h) f (p + h 0) - cubeDiff (Fin.tail h) f p

private def falseCount {k : ℕ} (s : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => s i = false)).card

private theorem falseCount_cons {k : ℕ} (b : Bool) (s : Fin k → Bool) :
    falseCount (Fin.cons b s) = (if b = false then 1 else 0) + falseCount s := by
  have hcount {m : ℕ} (c : Fin m → Bool) :
      falseCount c = ∑ i, if c i = false then (1 : ℕ) else 0 :=
    (Finset.sum_boole (R := ℕ) (fun i => c i = false) Finset.univ).symm
  rw [hcount (Fin.cons b s), hcount s]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

private theorem cubeDiff_eq_sum {k : ℕ} (h : Fin k → ℝ) (f : ℝ → ℝ) (p : ℝ) :
    cubeDiff h f p = ∑ s : Fin k → Bool, (-1 : ℝ) ^ falseCount s * f (p + shiftSum h s) := by
  induction k generalizing p with
  | zero => simp [cubeDiff, falseCount, shiftSum]
  | succ k ih =>
    rw [cubeDiff, ih, ih, ← (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, falseCount_cons, shiftSum_cons,
      Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, zero_add, Nat.one_add,
      pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib, ← add_assoc, sub_eq_add_neg]

private theorem labelVertex_real {G H k : ℕ} (d : ℤ) (x : Label G H k)
    (s : Fin k → Bool) (e b : Bool) :
    (labelVertex d x (s, e, b) : ℝ) = (x.1.val : ℝ) +
      shiftSum (fun i => (intShift (x.2.2 i) : ℝ)) s +
      (if e then (x.2.1.val : ℝ) + 1 else 0) + (if b then (d : ℝ) else 0) := by
  cases e <;> cases b <;>
    simp [labelVertex, vertex, subsetShift, shiftSum, Int.cast_sum, apply_ite]

private noncomputable def logShift (d t : ℝ) : ℝ := Real.log (t + d) - Real.log t

private theorem cubeFrequency_eq_cubeDiff {G H k : ℕ} (d : ℤ) (x : Label G H k)
    (hpos : ∀ v, 0 < (labelVertex d x v : ℝ)) :
    let h : Fin k → ℝ := fun i => (intShift (x.2.2 i) : ℝ)
    let p : ℝ := x.1.val
    let g : ℝ := (x.2.1.val : ℝ) + 1
    cubeFrequency d x = cubeDiff h (logShift d) p - cubeDiff h (logShift d) (p + g) := by
  dsimp only
  rw [cubeDiff_eq_sum, cubeDiff_eq_sum, ← Finset.sum_sub_distrib]
  unfold cubeFrequency
  apply Finset.sum_congr rfl
  intro s _
  rw [Real.log_div (hpos _).ne' (hpos _).ne', Real.log_div (hpos _).ne' (hpos _).ne']
  simp only [falseCount, Int.cast_pow, Int.cast_neg, Int.cast_one, mul_sub, labelVertex_real,
    logShift, Bool.false_eq_true, ↓reduceIte, add_zero]
  simp only [add_right_comm (x.1.val : ℝ) ((x.2.1.val : ℝ) + 1)]

private theorem abs_sub_le_mul_of_hasDerivAt {f f' : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hM : ∀ t ∈ uIcc a b, |f' t| ≤ M) : |f b - f a| ≤ M * |b - a| := by
  simpa only [Real.norm_eq_abs] using
    (convex_uIcc (𝕜 := ℝ) a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hf t ht).hasDerivWithinAt) (by simpa only [Real.norm_eq_abs] using hM)
      left_mem_uIcc right_mem_uIcc

-- The zeroth entry is the logarithm; the next entries are the reciprocal and its derivatives.
private noncomputable def logJet : ℕ → ℝ → ℝ
  | 0 => Real.log
  | n + 1 => fun t => (-1 : ℝ) ^ n * (n.factorial : ℝ) * t ^ (-((n + 1 : ℕ) : ℤ))

private theorem logJet_hasDerivAt (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (logJet n) (logJet (n + 1) t) t := by
  cases n with
  | zero => simpa [logJet, zpow_neg] using Real.hasDerivAt_log ht.ne'
  | succ n =>
    have h := (hasDerivAt_zpow (-((n + 1 : ℕ) : ℤ)) t (Or.inl ht.ne')).const_mul
      ((-1 : ℝ) ^ n * (n.factorial : ℝ))
    rw [show -((n + 1 : ℕ) : ℤ) - 1 = -((n + 1 + 1 : ℕ) : ℤ) by omega] at h
    rw [Int.cast_neg, Int.cast_natCast] at h
    have hc : (-1 : ℝ) ^ n * (n.factorial : ℝ) * -((n + 1 : ℕ) : ℝ) =
        (-1 : ℝ) ^ (n + 1) * ((n + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      ring
    rw [← mul_assoc, hc] at h
    exact h

private theorem abs_logJet_succ_le (n : ℕ) {L t : ℝ} (hL : 0 < L) (ht : L ≤ t) :
    |logJet (n + 1) t| ≤ (n.factorial : ℝ) / L ^ (n + 1) := by
  rw [logJet, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), zpow_neg, zpow_natCast,
    abs_of_pos (inv_pos.mpr (pow_pos (hL.trans_le ht) _)), ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hL _)
    (pow_le_pow_left₀ hL.le ht _)

private noncomputable def logShiftJet (d : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  logJet n (t + d) - logJet n t

private theorem logShiftJet_hasDerivAt (n : ℕ) {d t : ℝ} (hd : 0 ≤ d) (ht : 0 < t) :
    HasDerivAt (logShiftJet d n) (logShiftJet d (n + 1) t) t :=
  ((logJet_hasDerivAt n (add_pos_of_pos_of_nonneg ht hd)).comp_add_const t d).sub
    (logJet_hasDerivAt n ht)

private theorem abs_logShiftJet_le (n : ℕ) {L d t : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (ht : L ≤ t) : |logShiftJet d n t| ≤ d * (n.factorial : ℝ) / L ^ (n + 1) := by
  have hseg (u : ℝ) (hu : u ∈ uIcc t (t + d)) : L ≤ u := by
    rw [uIcc_of_le (le_add_of_nonneg_right hd)] at hu
    exact ht.trans hu.1
  have hb := abs_sub_le_mul_of_hasDerivAt
    (fun u hu => logJet_hasDerivAt n (hL.trans_le (hseg u hu)))
    (fun u hu => abs_logJet_succ_le n hL (hseg u hu))
  simpa only [logShiftJet, add_sub_cancel_left, abs_of_nonneg hd, div_mul_eq_mul_div,
    mul_comm (n.factorial : ℝ) d] using hb

private def CornersAbove {k : ℕ} (L : ℝ) (h : Fin k → ℝ) (p : ℝ) : Prop :=
  ∀ s, L ≤ p + shiftSum h s

-- Both endpoint cubes control the entire segment, regardless of the sign of the first shift.
private theorem cornersAbove_tail {k : ℕ} {L p t : ℝ} {h : Fin (k + 1) → ℝ}
    (hband : CornersAbove L h p) (ht : t ∈ uIcc p (p + h 0)) :
    CornersAbove L (Fin.tail h) t := by
  intro s
  have hleft := hband (Fin.cons false s)
  have hright := hband (Fin.cons true s)
  simp only [shiftSum_cons, Bool.false_eq_true, ↓reduceIte, zero_add, ← add_assoc] at hleft hright
  exact sub_le_iff_le_add.mp
    ((le_min (sub_le_iff_le_add.mpr hleft) (sub_le_iff_le_add.mpr hright)).trans ht.1)

private theorem cubeDiff_hasDerivAt {k : ℕ} (h : Fin k → ℝ) (n : ℕ) {L d p : ℝ}
    (hL : 0 < L) (hd : 0 ≤ d) (hband : CornersAbove L h p) :
    HasDerivAt (cubeDiff h (logShiftJet d n)) (cubeDiff h (logShiftJet d (n + 1)) p) p := by
  induction k generalizing p with
  | zero =>
    have hp : L ≤ p := by simpa [shiftSum] using hband (fun _ => false)
    exact logShiftJet_hasDerivAt n hd (hL.trans_le hp)
  | succ k ih =>
    exact ((ih (Fin.tail h) (cornersAbove_tail hband right_mem_uIcc)).comp_add_const p (h 0)).sub
      (ih (Fin.tail h) (cornersAbove_tail hband left_mem_uIcc))

private theorem abs_cubeDiff_logShiftJet_le {k : ℕ} (h : Fin k → ℝ) (n : ℕ) {L d p : ℝ}
    (hL : 0 < L) (hd : 0 ≤ d) (hband : CornersAbove L h p) :
    |cubeDiff h (logShiftJet d n) p| ≤
      d * ((n + k).factorial : ℝ) / L ^ (n + k + 1) * (∏ i, |h i|) := by
  induction k generalizing n p with
  | zero =>
    have hp : L ≤ p := by simpa [shiftSum] using hband (fun _ => false)
    simpa [cubeDiff] using abs_logShiftJet_le n hL hd hp
  | succ k ih =>
    have hb := abs_sub_le_mul_of_hasDerivAt
      (fun _ ht => cubeDiff_hasDerivAt (Fin.tail h) n hL hd (cornersAbove_tail hband ht))
      (fun _ ht => ih (Fin.tail h) (n + 1) (cornersAbove_tail hband ht))
    rw [cubeDiff]
    refine hb.trans_eq ?_
    rw [Fin.prod_univ_succ, show n + 1 + k = n + (k + 1) by omega]
    simp only [Fin.tail_def, add_sub_cancel_left]
    ring

/-- The signed frequency on the integer lift is bounded by the directed difference
volume times `2 * d * k! / L^(k+1)`. No survival or cyclic-average hypothesis is needed. -/
public theorem abs_cubeFrequency_le {G H k : ℕ} {d : ℤ} {L : ℝ}
    (x : Label G H k) (hd : 0 ≤ d) (hL : 0 < L)
    (hband : ∀ v, L ≤ (labelVertex d x v : ℝ)) :
    |cubeFrequency d x| ≤
      2 * (d : ℝ) * (k.factorial : ℝ) * (∏ i, |(intShift (x.2.2 i) : ℝ)|) / L ^ (k + 1) := by
  let h : Fin k → ℝ := fun i => (intShift (x.2.2 i) : ℝ)
  let p : ℝ := x.1.val
  let g : ℝ := (x.2.1.val : ℝ) + 1
  have hb₀ : CornersAbove L h p := by
    intro s
    simpa only [labelVertex_real, Bool.false_eq_true, ↓reduceIte, add_zero] using
      hband (s, false, false)
  have hb₁ : CornersAbove L h (p + g) := by
    intro s
    simpa only [labelVertex_real, Bool.false_eq_true, ↓reduceIte, add_zero,
      add_right_comm p g] using hband (s, true, false)
  have hd' : 0 ≤ (d : ℝ) := by exact_mod_cast hd
  rw [cubeFrequency_eq_cubeDiff d x (fun v => hL.trans_le (hband v))]
  change |cubeDiff h (logShiftJet d 0) p - cubeDiff h (logShiftJet d 0) (p + g)| ≤ _
  calc
    _ ≤ |cubeDiff h (logShiftJet d 0) p| + |cubeDiff h (logShiftJet d 0) (p + g)| := abs_sub _ _
    _ ≤ _ := add_le_add (abs_cubeDiff_logShiftJet_le h 0 hL hd' hb₀)
      (abs_cubeDiff_logShiftJet_le h 0 hL hd' hb₁)
    _ = _ := by simp only [Nat.zero_add]; ring

/-- The uniform ordered-draw bound. Taking `L = exp (-8) * X` for `X > 0`
gives the reciprocal factor `(exp 8 / X)^(k+1)` in the source. -/
public theorem abs_cubeFrequency_le_uniform {G H k : ℕ} {d : ℤ} {L : ℝ}
    (x : Label G H k) (hd : 0 ≤ d) (hL : 0 < L)
    (hband : ∀ v, L ≤ (labelVertex d x v : ℝ)) :
    |cubeFrequency d x| ≤ 2 * (d : ℝ) * (k.factorial : ℝ) * (H : ℝ) ^ k / L ^ (k + 1) := by
  have hshift (i : Fin k) : |(intShift (x.2.2 i) : ℝ)| ≤ (H : ℝ) := by
    have ha := (x.2.2 i).1.isLt
    have hb := (x.2.2 i).2.isLt
    have h : |intShift (x.2.2 i)| ≤ (H : ℤ) := by
      rw [abs_le, intShift]
      omega
    exact_mod_cast h
  have hprod : (∏ i, |(intShift (x.2.2 i) : ℝ)|) ≤ (H : ℝ) ^ k := by
    calc
      _ ≤ ∏ _ : Fin k, (H : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hshift i)
      _ = _ := by simp
  have hd' : 0 ≤ (d : ℝ) := by exact_mod_cast hd
  exact (abs_cubeFrequency_le x hd hL hband).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity))
      (pow_nonneg hL.le _))

/-- The frequency bound on a band with lower cutoff `exp (-8) * X`, in the
normalization of the signed-gap cube estimate. -/
public theorem abs_cubeFrequency_le_exp_band {G H k : ℕ} {d : ℤ} {X : ℝ}
    (x : Label G H k) (hd : 0 ≤ d) (hX : 0 < X)
    (hband : ∀ v, Real.exp (-8) * X ≤ (labelVertex d x v : ℝ)) :
    |cubeFrequency d x| ≤
      2 * (d : ℝ) * (k.factorial : ℝ) * (H : ℝ) ^ k * (Real.exp 8 / X) ^ (k + 1) := by
  have hcut : 0 < Real.exp (-8) * X := mul_pos (Real.exp_pos _) hX
  have hinv : (Real.exp (-8) * X)⁻¹ = Real.exp 8 / X := by
    rw [mul_inv, Real.exp_neg, inv_inv, div_eq_mul_inv]
  simpa only [div_eq_mul_inv, ← inv_pow, hinv] using
    abs_cubeFrequency_le_uniform x hd hcut hband

end Masullo.SignedCubeShell
