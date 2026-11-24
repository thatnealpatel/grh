module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Totient
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Selberg interval diagonal

Source: `8058479edd84:.godel/bob/short-cell-weil-list.md:21–27`, used at
lines 33–37 and 49; see also `.godel/bob/sieved-height-gram.md:27–29` at
pin `52090c0259f5`. This proves the finite arithmetic normalizations and the
absolute interval error with constant `z²`. It does not use the harmonic
lower bound or address the off-diagonal estimate or prime trace.

Owning check session: `01a20f88-43d7-7049-9647-cb18c5a08d70`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace SelbergIntervalDiagonal

@[expose] public section

noncomputable section

/-- Positive indices up to the integer cutoff, represented by naturals. -/
def cutoff (z : ℤ) : Finset ℕ := Icc 1 z.toNat

theorem mem_cutoff {z : ℤ} (hz : 1 ≤ z) {j : ℕ} :
    j ∈ cutoff z ↔ 1 ≤ (j : ℤ) ∧ (j : ℤ) ≤ z := by
  rw [cutoff, Finset.mem_Icc, ← Int.toNat_of_nonneg (show 0 ≤ z by omega)]
  exact_mod_cast Iff.rfl

/-- The natural indices enumerate every integer index in the source, once. -/
theorem cutoff_image_int {z : ℤ} (hz : 1 ≤ z) :
    (cutoff z).image (fun j : ℕ ↦ (j : ℤ)) = Icc 1 z := by
  ext j
  rw [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_cutoff hz).mp hk
  · intro hj
    have hc : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
    exact ⟨j.toNat, (mem_cutoff hz).mpr (hc ▸ hj), hc⟩

/-- The divisibility filter also agrees with the integer one. Quotients are
compatible with this representation by `Int.natCast_div`. -/
theorem mem_cutoff_dvd {z : ℤ} (hz : 1 ≤ z) {k j : ℕ} :
    j ∈ (cutoff z).filter (fun j ↦ k ∣ j) ↔
      (1 ≤ (j : ℤ) ∧ (j : ℤ) ≤ z) ∧ (k : ℤ) ∣ (j : ℤ) := by
  rw [Finset.mem_filter, mem_cutoff hz, Int.natCast_dvd_natCast]

/-- The source's normalizing sum. -/
def J (z : ℤ) : ℝ := ∑ j ∈ cutoff z, (μ j : ℝ) ^ 2 / (j.totient : ℝ)

/-- The diagonal coordinates, with the sign of the Möbius function. -/
def y (z : ℤ) (j : ℕ) : ℝ := (μ j : ℝ) / (J z * (j.totient : ℝ))

/-- The source's coefficients, obtained by inversion over cutoff multiples. -/
def lambda (z : ℤ) (k : ℕ) : ℝ :=
  (k : ℝ) * ∑ j ∈ (cutoff z).filter (fun j ↦ k ∣ j), (μ (j / k) : ℝ) * y z j

private theorem pos_of_mem_cutoff {z : ℤ} {j : ℕ} (hj : j ∈ cutoff z) : 0 < j :=
  (Finset.mem_Icc.mp hj).1

private theorem totient_pos_real {j : ℕ} (hj : 0 < j) : 0 < (j.totient : ℝ) := by
  exact_mod_cast Nat.totient_pos.mpr hj

theorem J_pos {z : ℤ} (hz : 1 ≤ z) : 0 < J z := by
  have h1 : 1 ∈ cutoff z := (mem_cutoff hz).mpr (by simpa using hz)
  have h := Finset.single_le_sum (f := fun j : ℕ ↦ (μ j : ℝ) ^ 2 / (j.totient : ℝ))
    (fun j _ ↦ by positivity) h1
  have hone : (μ 1 : ℝ) ^ 2 / ((1 : ℕ).totient : ℝ) = 1 := by norm_num
  rw [hone] at h
  exact zero_lt_one.trans_le h

theorem lambda_one {z : ℤ} (hz : 1 ≤ z) : lambda z 1 = 1 := by
  have hJ := (J_pos hz).ne'
  rw [lambda]
  simp only [Nat.cast_one, Nat.one_dvd, Finset.filter_true, Nat.div_one, one_mul, y]
  calc
    _ = ∑ j ∈ cutoff z, (J z)⁻¹ * ((μ j : ℝ) ^ 2 / (j.totient : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have ht := (totient_pos_real (pos_of_mem_cutoff hj)).ne'
      field_simp
    _ = 1 := by rw [← Finset.mul_sum, ← J, inv_mul_cancel₀ hJ]

private theorem sum_cutoff_multiples (z : ℤ) {k : ℕ} (hk : 0 < k) (f : ℕ → ℝ) :
    (∑ j ∈ (cutoff z).filter (fun j ↦ k ∣ j), f j) =
      ∑ m ∈ Icc 1 (z.toNat / k), f (k * m) := by
  symm
  refine Finset.sum_bij (fun m _ ↦ k * m) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro m hm
    obtain ⟨hm₀, hmz⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hk hm₀, by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).mp hmz⟩,
      dvd_mul_right k m⟩
  · exact fun _ _ _ _ h ↦ Nat.mul_left_cancel hk h
  · intro j hj
    obtain ⟨hj, m, rfl⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj₀, hjz⟩ := Finset.mem_Icc.mp hj
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hj₀)
    exact ⟨m, Finset.mem_Icc.mpr ⟨hm, (Nat.le_div_iff_mul_le hk).mpr
      (by simpa [Nat.mul_comm] using hjz)⟩, rfl⟩

private theorem lambda_of_not_squarefree (z : ℤ) {k : ℕ} (hk : ¬Squarefree k) :
    lambda z k = 0 := by
  rw [lambda]
  suffices h : (∑ j ∈ (cutoff z).filter (fun j ↦ k ∣ j), (μ (j / k) : ℝ) * y z j) = 0 by
    rw [h, mul_zero]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : ¬Squarefree j := fun h ↦ hk (h.squarefree_of_dvd (Finset.mem_filter.mp hj).2)
  simp [y, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hj']

private def coprimeCutoff (z : ℤ) (k : ℕ) : Finset ℕ :=
  (Icc 1 (z.toNat / k)).filter (fun m ↦ k.Coprime m)

private theorem lambda_factor {z : ℤ} {k : ℕ} (hz : 1 ≤ z) (hk₀ : 0 < k) :
    lambda z k = (μ k : ℝ) * ((k : ℝ) / (k.totient : ℝ) *
      ∑ m ∈ coprimeCutoff z k, (μ m : ℝ) ^ 2 / (m.totient : ℝ)) / J z := by
  have hJ := (J_pos hz).ne'
  have hφk := (totient_pos_real hk₀).ne'
  rw [lambda, sum_cutoff_multiples z hk₀, coprimeCutoff]
  simp only [Nat.mul_div_cancel_left _ hk₀]
  calc
    _ = (k : ℝ) * ∑ m ∈ Icc 1 (z.toNat / k), if k.Coprime m then
          (μ k : ℝ) / (J z * (k.totient : ℝ)) * ((μ m : ℝ) ^ 2 / (m.totient : ℝ))
        else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hc : k.Coprime m
      · have hφm := (totient_pos_real (Finset.mem_Icc.mp hm).1).ne'
        rw [ite_eq_left hc, y, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
          Nat.totient_mul hc, Int.cast_mul, Nat.cast_mul]
        field_simp
      · have hkm : ¬Squarefree (k * m) := fun h ↦ hc (Nat.coprime_of_squarefree_mul h)
        simp [hc, y, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hkm]
    _ = _ := by rw [← Finset.sum_filter, ← Finset.mul_sum]; ring

private theorem coefficient_mass_le_J {z : ℤ} {k : ℕ} (hk : Squarefree k) :
    (k : ℝ) / (k.totient : ℝ) *
      (∑ m ∈ coprimeCutoff z k, (μ m : ℝ) ^ 2 / (m.totient : ℝ)) ≤ J z := by
  have hk₀ := Nat.pos_of_ne_zero hk.ne_zero
  let S := k.divisors ×ˢ coprimeCutoff z k
  let f : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  have props {p : ℕ × ℕ} (hp : p ∈ S) :
      p.1 ∣ k ∧ 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ z.toNat / k ∧ k.Coprime p.2 := by
    obtain ⟨hd, hm⟩ := Finset.mem_product.mp hp
    obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hm
    exact ⟨Nat.dvd_of_mem_divisors hd, Nat.pos_of_mem_divisors hd,
      (Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2, hc⟩
  have hsub : S.image f ⊆ cutoff z := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hd, hd₀, hm₀, hmz, _⟩ := props hp
    refine Finset.mem_Icc.mpr ⟨Nat.mul_pos hd₀ hm₀, ?_⟩
    exact (Nat.mul_le_mul_right _ (Nat.le_of_dvd hk₀ hd)).trans
      (by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk₀).mp hmz)
  have hrecover (p : ℕ × ℕ) (hp : p ∈ S) : Nat.gcd k (f p) = p.1 := by
    obtain ⟨hd, _, _, _, hc⟩ := props hp
    exact (hc.symm.gcd_mul_right_cancel_right p.1).trans (Nat.gcd_eq_right hd)
  have hinj : Set.InjOn f (↑S : Set (ℕ × ℕ)) := by
    intro p hp q hq h
    have hd : p.1 = q.1 := (hrecover p hp).symm.trans ((congrArg (Nat.gcd k) h).trans (hrecover q hq))
    apply Prod.ext hd
    apply Nat.mul_left_cancel (props hp).2.1
    simpa only [f, ← hd] using h
  let A (j : ℕ) : ℝ := (μ j : ℝ) ^ 2 / (j.totient : ℝ)
  have htot : (∑ d ∈ k.divisors, ((k / d).totient : ℝ)) = (k : ℝ) := by
    rw [Nat.sum_div_divisors k (fun d ↦ (d.totient : ℝ))]
    exact_mod_cast Nat.sum_totient k
  calc
    _ = ∑ d ∈ k.divisors, ∑ m ∈ coprimeCutoff z k,
        ((k / d).totient : ℝ) / (k.totient : ℝ) * A m := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, A, div_eq_mul_inv, htot]
    _ = ∑ p ∈ S, A (f p) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro m hm
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hco := (Finset.mem_filter.mp hm).2
      have hdc := hco.of_dvd_left hdvd
      have hdsq := hk.squarefree_of_dvd hdvd
      have hμd : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsq
      have hcomp : (k / d).totient * d.totient = k.totient := by
        rw [← Nat.totient_mul (Nat.coprime_of_squarefree_mul
          (show Squarefree (k / d * d) by simpa [Nat.div_mul_cancel hdvd] using hk)),
          Nat.div_mul_cancel hdvd]
      have hφd := (totient_pos_real (Nat.pos_of_mem_divisors hd)).ne'
      have hφm := (totient_pos_real (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1).ne'
      have hφk := (totient_pos_real hk₀).ne'
      have hcompR : ((k / d).totient : ℝ) * (d.totient : ℝ) = (k.totient : ℝ) := by
        exact_mod_cast hcomp
      dsimp [A, f]
      rw [Nat.totient_mul hdc, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hdc,
        Int.cast_mul, Nat.cast_mul, mul_pow, hμd, one_mul]
      have hr : ((k / d).totient : ℝ) / (k.totient : ℝ) = (d.totient : ℝ)⁻¹ := by
        field_simp
        exact hcompR
      rw [hr]
      field_simp
    _ = ∑ j ∈ S.image f, A j := (Finset.sum_image hinj).symm
    _ ≤ J z := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ ↦ by dsimp [A]; positivity)

theorem abs_lambda_le_one {z : ℤ} (hz : 1 ≤ z) {k : ℕ} (hk : k ∈ cutoff z) :
    |lambda z k| ≤ 1 := by
  by_cases hs : Squarefree k
  · have hμ : |(μ k : ℝ)| = 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs
    have hA : 0 ≤ (k : ℝ) / (k.totient : ℝ) *
        (∑ m ∈ coprimeCutoff z k, (μ m : ℝ) ^ 2 / (m.totient : ℝ)) := by positivity
    rw [lambda_factor hz (pos_of_mem_cutoff hk), abs_div, abs_mul, hμ, one_mul, abs_of_nonneg hA,
      abs_of_pos (J_pos hz), div_le_iff₀ (J_pos hz), one_mul]
    exact coefficient_mass_le_J hs
  · simp [lambda_of_not_squarefree z hs]

private theorem sum_moebius_divisors (q : ℕ) :
    (∑ b ∈ q.divisors, (μ (q / b) : ℝ)) = if q = 1 then 1 else 0 := by
  rw [Nat.sum_div_divisors q (fun b ↦ (μ b : ℝ))]
  have h : (∑ b ∈ q.divisors, μ b) = if q = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  apply_fun (fun n : ℤ ↦ (n : ℝ)) at h
  simpa only [Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero] using h

-- The divisibility interval r ∣ d ∣ j is the divisor set of j/r.
private theorem sum_between {z : ℤ} {r j : ℕ} (hr : 0 < r) (hj : j ∈ cutoff z)
    (hrj : r ∣ j) :
    (∑ d ∈ (cutoff z).filter (fun d ↦ r ∣ d ∧ d ∣ j), (μ (j / d) : ℝ)) =
      if j = r then 1 else 0 := by
  have hj₀ := pos_of_mem_cutoff hj
  have hq₀ : j / r ≠ 0 := by
    intro h
    have he := Nat.mul_div_cancel' hrj
    rw [h, mul_zero] at he
    exact hj₀.ne' he.symm
  have hq1 : j / r = 1 ↔ j = r := by
    rw [Nat.div_eq_iff_eq_mul_right hr hrj, mul_one]
  have hsum : (∑ b ∈ (j / r).divisors, (μ (j / r / b) : ℝ)) = if j = r then 1 else 0 := by
    simpa only [hq1] using sum_moebius_divisors (j / r)
  rw [← hsum]
  symm
  refine Finset.sum_bij (fun b _ ↦ r * b) ?_ ?_ ?_ ?_
  · intro b hb
    have hdj := Nat.mul_dvd_of_dvd_div hrj (Nat.dvd_of_mem_divisors hb)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hr (Nat.pos_of_mem_divisors hb),
        (Nat.le_of_dvd hj₀ hdj).trans (Finset.mem_Icc.mp hj).2⟩, dvd_mul_right r b, hdj⟩
  · exact fun _ _ _ _ h ↦ Nat.mul_left_cancel hr h
  · intro d hd
    obtain ⟨_, hd₁, hd₂⟩ := Finset.mem_filter.mp hd
    refine ⟨d / r, Nat.mem_divisors.mpr ⟨?_, hq₀⟩, Nat.mul_div_cancel' hd₁⟩
    apply Nat.dvd_div_of_mul_dvd
    rwa [Nat.mul_div_cancel' hd₁]
  · intro b _
    rw [Nat.div_div_eq_div_mul]

/-- The chosen coefficients recover the source's diagonal coordinates on the cutoff. -/
theorem sum_lambda_div_eq_y {z : ℤ} {r : ℕ} (hr : r ∈ cutoff z) :
    (∑ d ∈ (cutoff z).filter (fun d ↦ r ∣ d), lambda z d / (d : ℝ)) = y z r := by
  have hcancel {d : ℕ} (hd : d ∈ cutoff z) : lambda z d / (d : ℝ) =
      ∑ j ∈ (cutoff z).filter (fun j ↦ d ∣ j), (μ (j / d) : ℝ) * y z j := by
    have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast (pos_of_mem_cutoff hd).ne'
    rw [lambda]
    field_simp
  calc
    _ = ∑ d ∈ (cutoff z).filter (fun d ↦ r ∣ d),
         ∑ j ∈ (cutoff z).filter (fun j ↦ d ∣ j), (μ (j / d) : ℝ) * y z j := by
      exact Finset.sum_congr rfl fun d hd ↦ hcancel (Finset.mem_filter.mp hd).1
    _ = ∑ j ∈ cutoff z,
         (∑ d ∈ (cutoff z).filter (fun d ↦ r ∣ d ∧ d ∣ j), (μ (j / d) : ℝ)) * y z j := by
      simp only [Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
      simp_rw [Finset.ite_sum_zero, ← ite_and]
      exact Finset.sum_comm
    _ = ∑ j ∈ cutoff z, if j = r then y z j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hd : r ∣ j
      · rw [sum_between (pos_of_mem_cutoff hr) hj hd, ite_mul, one_mul, zero_mul]
      · have hempty : (cutoff z).filter (fun d ↦ r ∣ d ∧ d ∣ j) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro d h
          obtain ⟨_, hrd, hdj⟩ := Finset.mem_filter.mp h
          exact hd (hrd.trans hdj)
        have hne : j ≠ r := fun h ↦ hd (h ▸ dvd_rfl)
        simp [hempty, hne]
    _ = _ := by rw [Finset.sum_ite_eq', ite_eq_left hr]

private theorem sum_totient_common {z : ℤ} {d e : ℕ} (hd : d ∈ cutoff z) :
    (∑ r ∈ (cutoff z).filter (fun r ↦ r ∣ d ∧ r ∣ e), (r.totient : ℝ)) = (d.gcd e : ℝ) := by
  have hd₀ := pos_of_mem_cutoff hd
  have hg₀ : d.gcd e ≠ 0 := (Nat.gcd_pos_of_pos_left e hd₀).ne'
  have hset : (cutoff z).filter (fun r ↦ r ∣ d ∧ r ∣ e) = (d.gcd e).divisors := by
    ext r
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, and_iff_left hg₀]
    refine and_iff_right_of_imp fun h ↦ ?_
    have hrdiv : r ∈ d.divisors := Nat.mem_divisors.mpr ⟨h.1, hd₀.ne'⟩
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hrdiv,
      (Nat.le_of_dvd hd₀ h.1).trans (Finset.mem_Icc.mp hd).2⟩
  rw [hset]
  exact_mod_cast Nat.sum_totient (d.gcd e)

/-- The reciprocal-lcm form diagonalizes by the divisor sum of the totient.
Here that direct argument works on the entire positive cutoff, without
embedding it into the divisors of a squarefree prime product. -/
theorem quadratic_diagonal {z : ℤ} (hz : 1 ≤ z) :
    (∑ d ∈ cutoff z, ∑ e ∈ cutoff z, lambda z d * lambda z e / (d.lcm e : ℝ)) = 1 / J z := by
  let v (d : ℕ) := lambda z d / (d : ℝ)
  have hkernel {d e : ℕ} (hd : d ∈ cutoff z) (he : e ∈ cutoff z) :
      lambda z d * lambda z e / (d.lcm e : ℝ) = (d.gcd e : ℝ) * v d * v e := by
    have hd₀ := pos_of_mem_cutoff hd
    have he₀ := pos_of_mem_cutoff he
    have hl : ((d.lcm e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hd₀ he₀).ne'
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd₀.ne'
    have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he₀.ne'
    have hg : (d.gcd e : ℝ) * (d.lcm e : ℝ) = (d : ℝ) * (e : ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    dsimp [v]
    field_simp
    rw [mul_assoc (lambda z d * lambda z e), ← hg]
    ring
  calc
    _ = ∑ d ∈ cutoff z, ∑ e ∈ cutoff z, ∑ r ∈ cutoff z,
          if r ∣ d ∧ r ∣ e then (r.totient : ℝ) * v d * v e else 0 := by
      refine Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun e he ↦ ?_
      rw [hkernel hd he, ← sum_totient_common (e := e) hd]
      simp only [Finset.sum_mul, Finset.sum_filter, ite_mul, zero_mul]
    _ = ∑ r ∈ cutoff z, ∑ d ∈ cutoff z, ∑ e ∈ cutoff z,
          if r ∣ d ∧ r ∣ e then (r.totient : ℝ) * v d * v e else 0 := by
      trans ∑ d ∈ cutoff z, ∑ r ∈ cutoff z, ∑ e ∈ cutoff z,
          if r ∣ d ∧ r ∣ e then (r.totient : ℝ) * v d * v e else 0
      · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      · exact Finset.sum_comm
    _ = ∑ r ∈ cutoff z, (r.totient : ℝ) * (y z r) ^ 2 := by
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      rw [← sum_lambda_div_eq_y hr, pow_two]
      change _ = (r.totient : ℝ) * ((∑ d ∈ (cutoff z).filter (fun d ↦ r ∣ d), v d) *
        ∑ e ∈ (cutoff z).filter (fun e ↦ r ∣ e), v e)
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_filter, mul_ite, ite_mul,
        Finset.ite_sum_zero, mul_zero, zero_mul, ← ite_and, mul_assoc]
      refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
      rw [mul_comm (v d) (v e)]
    _ = (J z)⁻¹ ^ 2 * (∑ r ∈ cutoff z, (μ r : ℝ) ^ 2 / (r.totient : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hJ := (J_pos hz).ne'
      have ht := (totient_pos_real (pos_of_mem_cutoff hr)).ne'
      rw [y]
      field_simp
    _ = (J z)⁻¹ ^ 2 * J z := rfl
    _ = 1 / J z := by
      have hJ := (J_pos hz).ne'
      field_simp

-- Multiplication by m is a bijection from the quotient interval to the multiples.
private theorem count_multiples (a h : ℕ) {m : ℕ} (hm : 0 < m) :
    ((Ioc a (a + h)).filter (fun n ↦ m ∣ n)).card = (a + h) / m - a / m := by
  rw [← Nat.card_Ioc]
  symm
  refine Finset.card_bij (fun q _ ↦ m * q) ?_ ?_ ?_
  · intro q hq
    obtain ⟨ha, hb⟩ := Finset.mem_Ioc.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨by simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hm).mp ha,
       by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp hb⟩, dvd_mul_right m q⟩
  · exact fun _ _ _ _ h ↦ Nat.mul_left_cancel hm h
  · intro n hn
    obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
    obtain ⟨ha, hb⟩ := Finset.mem_Ioc.mp hn
    refine ⟨n / m, Finset.mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hb⟩, Nat.mul_div_cancel' hd⟩
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    rwa [Nat.div_mul_cancel hd]

private theorem quotient_bounds (n : ℕ) {m : ℕ} (hm : 0 < m) :
    (↑(n / m) : ℝ) ≤ (n : ℝ) / m ∧ (n : ℝ) / m < (↑(n / m) : ℝ) + 1 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  constructor
  · apply (le_div_iff₀ hmR).mpr
    exact_mod_cast Nat.div_mul_le_self n m
  · apply (div_lt_iff₀ hmR).mpr
    exact_mod_cast (show n < (n / m + 1) * m by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ n hm)

private theorem multiple_count_error (a h : ℕ) {m : ℕ} (hm : 0 < m) :
    |(((Ioc a (a + h)).filter (fun n ↦ m ∣ n)).card : ℝ) - (h : ℝ) / m| ≤ 1 := by
  rw [count_multiples a h hm, Nat.cast_sub (Nat.div_le_div_right (Nat.le_add_right a h)), abs_le]
  obtain ⟨ha₁, ha₂⟩ := quotient_bounds a hm
  obtain ⟨hb₁, hb₂⟩ := quotient_bounds (a + h) hm
  simp only [Nat.cast_add, add_div] at hb₁ hb₂
  constructor <;> linarith

/-- The Selberg square on the strict-lower, inclusive-upper interval has
main term `h / J z` and absolute remainder at most `z²`. -/
theorem interval_error_le {z : ℤ} (hz : 1 ≤ z) (a h : ℕ) :
    |(∑ n ∈ Ioc a (a + h), (∑ k ∈ (cutoff z).filter (fun k ↦ k ∣ n), lambda z k) ^ 2) -
      (h : ℝ) / J z| ≤ (z : ℝ) ^ 2 := by
  let C (m : ℕ) : ℝ := ((Ioc a (a + h)).filter (fun n ↦ m ∣ n)).card
  have hexpand :
      (∑ n ∈ Ioc a (a + h), (∑ k ∈ (cutoff z).filter (fun k ↦ k ∣ n), lambda z k) ^ 2) =
        ∑ d ∈ cutoff z, ∑ e ∈ cutoff z, lambda z d * lambda z e * C (d.lcm e) := by
    calc
      _ = ∑ n ∈ Ioc a (a + h), ∑ d ∈ cutoff z, ∑ e ∈ cutoff z,
            if d.lcm e ∣ n then lambda z d * lambda z e else 0 := by
        simp only [pow_two, Finset.sum_filter, Finset.sum_mul_sum, mul_ite, ite_mul, mul_zero,
          zero_mul, ← ite_and, Nat.lcm_dvd_iff]
        refine Finset.sum_congr rfl fun n _ ↦ Finset.sum_congr rfl fun d _ ↦
          Finset.sum_congr rfl fun e _ ↦ ?_
        simp only [(and_comm : (e ∣ n ∧ d ∣ n) ↔ (d ∣ n ∧ e ∣ n))]
      _ = ∑ d ∈ cutoff z, ∑ e ∈ cutoff z, ∑ n ∈ Ioc a (a + h),
            if d.lcm e ∣ n then lambda z d * lambda z e else 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = _ := by
        simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, C, mul_comm]
  have hmain : (h : ℝ) / J z =
      ∑ d ∈ cutoff z, ∑ e ∈ cutoff z, lambda z d * lambda z e * ((h : ℝ) / (d.lcm e : ℝ)) := by
    calc
      _ = (h : ℝ) * (1 / J z) := by ring
      _ = _ := by
        rw [← quadratic_diagonal hz]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
        ring
  rw [hexpand, hmain]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  let E (d e : ℕ) := lambda z d * lambda z e * (C (d.lcm e) - (h : ℝ) / (d.lcm e : ℝ))
  change |∑ d ∈ cutoff z, ∑ e ∈ cutoff z, E d e| ≤ _
  calc
    _ ≤ ∑ d ∈ cutoff z, |∑ e ∈ cutoff z, E d e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ cutoff z, ∑ e ∈ cutoff z, |E d e| :=
      Finset.sum_le_sum fun d _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ cutoff z, ∑ _e ∈ cutoff z, (1 : ℝ) := by
      refine Finset.sum_le_sum fun d hd ↦ Finset.sum_le_sum fun e he ↦ ?_
      have hl := Nat.lcm_pos (pos_of_mem_cutoff hd) (pos_of_mem_cutoff he)
      simp only [E, abs_mul]
      have hprod : |lambda z d| * |lambda z e| ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (abs_lambda_le_one hz hd)
          (abs_lambda_le_one hz he) (abs_nonneg _) zero_le_one
      simpa only [one_mul] using mul_le_mul hprod (multiple_count_error a h hl)
        (abs_nonneg _) zero_le_one
    _ = (z : ℝ) ^ 2 := by
      have hcard : (cutoff z).card = z.toNat := by simp [cutoff, Nat.card_Icc]
      have hzcast : (z.toNat : ℝ) = (z : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ z by omega)
      simp [hcard, hzcast, nsmul_eq_mul, pow_two]

end

end

end SelbergIntervalDiagonal
