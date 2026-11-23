module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-!
# Smooth values on a finite affine line

Source: `472c8e5d:.godel/alice/adaptive-complement-interval.md`, exceptional direction
(parameter length `R/k`), citing `.godel/alice/rich-column-rows.md`, “Affine directions.”
This is the per-interval sieve used in `1d3802f7:.godel/alice/two-cofactor-strips.md`,
benefit 3, and `5e6920d1:.godel/alice/modular-complement-bands.md`, cut 2.
It does not estimate a dictionary of intervals, identify ambient points with actual columns,
or use an asymptotic estimate for the smooth-number counting function.

Owning check session: `01a20938-230d-71be-9082-772ff1e0dec6`.
-/

namespace AffineSmoothInterval

-- Take the largest divisor at most D. If it has not crossed D/X, a prime of
-- the remaining quotient gives a strictly larger eligible divisor.
private theorem exists_crossing_divisor {X D n : ℕ} (hD : 1 ≤ D) (hnD : D < n)
    (hn : n ∈ Nat.smoothNumbers (X + 1)) :
    ∃ d ∈ Nat.smoothNumbersUpTo D (X + 1), D < X * d ∧ d ∣ n := by
  let t := (Finset.Icc 1 D).filter (· ∣ n)
  have ht : t.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hD⟩,
    one_dvd n⟩⟩
  let d := t.max' ht
  obtain ⟨hdI, hdvd⟩ := Finset.mem_filter.mp (t.max'_mem ht)
  obtain ⟨hdpos, hdD⟩ := Finset.mem_Icc.mp hdI
  refine ⟨d, Nat.mem_smoothNumbersUpTo.mpr ⟨hdD, Nat.mem_smoothNumbers_of_dvd hn hdvd⟩,
    ?_, hdvd⟩
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : q ≠ 1 := by
    intro h
    rw [h, mul_one] at hq
    exact (not_le_of_gt hnD) (hq.symm ▸ hdD)
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
  have hdp : d * p ∣ n := hq ▸ Nat.mul_dvd_mul_left d hpq
  have hpX : p ≤ X := by
    have := Nat.mem_smoothNumbers'.mp hn p hp ((Nat.dvd_mul_left p d).trans hdp)
    omega
  by_contra! hXd
  have hdpD : d * p ≤ D := by
    rw [mul_comm d p]
    exact (Nat.mul_le_mul_right d hpX).trans hXd
  have hdlt : d < d * p := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt (by omega : 0 < d)
  have hmem : d * p ∈ t :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos.trans hdlt.le, hdpD⟩, hdp⟩
  exact (not_le_of_gt hdlt) (t.le_max' _ hmem)

-- Map a nonempty residue-class fiber to the consecutive indices measured from
-- its least parameter. There are at most X+1 indices, endpoints included.
private theorem card_le_of_crossing_spacing {X D d : ℕ} {s : Finset ℤ} (hs : s.Nonempty)
    (hd : 0 < d) (hcross : D < X * d)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, j - i ≤ (D : ℤ))
    (hdiv : ∀ i ∈ s, ∀ j ∈ s, (d : ℤ) ∣ j - i) :
    s.card ≤ X + 1 := by
  let j₀ := s.min' hs
  have hj₀ : j₀ ∈ s := s.min'_mem hs
  let idx (j : ℤ) := (j - j₀) / (d : ℤ)
  have hidx (j : ℤ) (hj : j ∈ s) : idx j * (d : ℤ) = j - j₀ :=
    Int.ediv_mul_cancel (hdiv j₀ hj₀ j hj)
  have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hcrossZ : (D : ℤ) < (X : ℤ) * (d : ℤ) := by exact_mod_cast hcross
  have hcard : s.card ≤ (Finset.Icc (0 : ℤ) (X : ℤ)).card := by
    apply Finset.card_le_card_of_injOn idx
    · intro j hj
      change j ∈ s at hj
      apply Finset.mem_Icc.mpr
      refine ⟨Int.ediv_nonneg (sub_nonneg.mpr (s.min'_le j hj)) hdZ.le, ?_⟩
      by_contra! h
      have hle := mul_le_mul_of_nonneg_right h.le hdZ.le
      rw [hidx j hj] at hle
      exact (not_le_of_gt hcrossZ) (hle.trans (hdiam j₀ hj₀ j hj))
    · intro i hi j hj hij
      change i ∈ s at hi
      change j ∈ s at hj
      have heq : i - j₀ = j - j₀ := by rw [← hidx i hi, ← hidx j hj, hij]
      exact sub_left_inj.mp heq
  rw [Int.card_Icc, sub_zero, ← Nat.cast_one, ← Nat.cast_add, Int.toNat_natCast] at hcard
  exact hcard

private theorem card_le_of_coprime {X D : ℕ} {a b : ℤ} {s : Finset ℤ} (hD : 1 ≤ D)
    (ha : a ≠ 0) (hab : IsCoprime a b)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, j - i ≤ (D : ℤ))
    (hs : ∀ j ∈ s, 0 < b + a * j ∧ (b + a * j).natAbs ∈ Nat.smoothNumbers (X + 1)) :
    s.card ≤ (X + 2) * (Nat.smoothNumbersUpTo D (X + 1)).card := by
  let n (j : ℤ) := (b + a * j).natAbs
  let t := Nat.smoothNumbersUpTo D (X + 1)
  let small := s.filter (fun j ↦ n j ≤ D)
  let large := s.filter (fun j ↦ ¬ n j ≤ D)
  have hn (j : ℤ) (hj : j ∈ s) : (n j : ℤ) = b + a * j :=
    Int.natAbs_of_nonneg (hs j hj).1.le
  have hsmall : small.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn n
    · intro j hj
      obtain ⟨hjs, hjD⟩ := Finset.mem_filter.mp hj
      exact Nat.mem_smoothNumbersUpTo.mpr ⟨hjD, (hs j hjs).2⟩
    · intro i hi j hj hij
      have h := congrArg (fun k : ℕ ↦ (k : ℤ)) hij
      rw [hn i (Finset.mem_filter.mp hi).1, hn j (Finset.mem_filter.mp hj).1] at h
      exact mul_left_cancel₀ ha (add_left_cancel h)
  have hchoose (j : ℤ) (hj : j ∈ large) : ∃ d ∈ t, D < X * d ∧ d ∣ n j := by
    obtain ⟨hjs, hjD⟩ := Finset.mem_filter.mp hj
    exact exists_crossing_divisor hD (lt_of_not_ge hjD) (hs j hjs).2
  classical
  let f (j : ℤ) := if hj : j ∈ large then (hchoose j hj).choose else 1
  have hf (j : ℤ) (hj : j ∈ large) : f j ∈ t ∧ D < X * f j ∧ f j ∣ n j := by
    simpa only [f, dite_eq_left hj] using (hchoose j hj).choose_spec
  have hlarge : large.card ≤ (X + 1) * t.card := by
    refine Finset.card_le_mul_card_image_of_maps_to (fun j hj ↦ (hf j hj).1) (X + 1) ?_
    intro d hd
    let fiber := large.filter (fun j ↦ f j = d)
    change fiber.card ≤ X + 1
    by_cases hne : fiber.Nonempty
    · have hfiber (j : ℤ) (hj : j ∈ fiber) : j ∈ s ∧ D < X * d ∧ (d : ℤ) ∣ b + a * j := by
        obtain ⟨hjlarge, hfd⟩ := Finset.mem_filter.mp hj
        have hjs : j ∈ s := (Finset.mem_filter.mp hjlarge).1
        obtain ⟨_, hcross, hdvd⟩ := hf j hjlarge
        rw [hfd] at hcross hdvd
        exact ⟨hjs, hcross, hn j hjs ▸ Int.natCast_dvd_natCast.mpr hdvd⟩
      obtain ⟨j, hj⟩ := hne
      have hpos : 0 < d := Nat.pos_of_ne_zero (Nat.mem_smoothNumbersUpTo.mp hd).2.1
      refine card_le_of_crossing_spacing ⟨j, hj⟩ hpos (hfiber j hj).2.1 ?_ ?_
      · intro i hi k hk
        exact hdiam i (hfiber i hi).1 k (hfiber k hk).1
      · intro i hi k hk
        have hdi := (hfiber i hi).2.2
        have hdk := (hfiber k hk).2.2
        have hcop := (hab.symm.add_mul_left_left i).of_isCoprime_of_dvd_left hdi
        apply hcop.dvd_of_dvd_mul_left
        convert dvd_sub hdk hdi using 1
        ring
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  calc
    s.card = small.card + large.card :=
      (Finset.card_filter_add_card_filter_not (fun j ↦ n j ≤ D)).symm
    _ ≤ t.card + (X + 1) * t.card := Nat.add_le_add hsmall hlarge
    _ = (X + 2) * t.card := by ring

/-- Count the integer parameters in the inclusive translated interval `[u,v]` having a
positive `X`-smooth value `b + a*j`. There is no condition on the sign of the nonzero
slope or on the coefficient gcd. Mathlib uses a strict prime cutoff, so
`Nat.smoothNumbersUpTo D (X + 1)` counts the positive integers at most `D` with all
prime factors at most `X`, including powers. -/
public theorem card_smooth_affine_int_interval_le {X D : ℕ} {a b u v : ℤ}
    (_hX : 2 ≤ X) (hD : 1 ≤ D) (ha : a ≠ 0) (huv : v - u ≤ (D : ℤ)) :
    ((Finset.Icc u v).filter (fun j ↦ 0 < b + a * j ∧
      (b + a * j).natAbs ∈ Nat.smoothNumbers (X + 1))).card ≤
      (X + 2) * (Nat.smoothNumbersUpTo D (X + 1)).card := by
  let s := (Finset.Icc u v).filter (fun j ↦ 0 < b + a * j ∧
    (b + a * j).natAbs ∈ Nat.smoothNumbers (X + 1))
  have hg : 0 < a.gcd b := Int.gcd_pos_of_ne_zero_left b ha
  have hgZ : 0 < (a.gcd b : ℤ) := by exact_mod_cast hg
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  have ha'ne : a' ≠ 0 := by
    intro h
    apply ha
    rw [ha', h, mul_zero]
  have hab' : IsCoprime a' b' := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    have heq := congrArg₂ Int.gcd ha' hb'
    rw [Int.gcd_mul_left, Int.natAbs_natCast] at heq
    exact Nat.eq_of_mul_eq_mul_left hg (heq.symm.trans (Nat.mul_one _).symm)
  have hfac (j : ℤ) : b + a * j = (a.gcd b : ℤ) * (b' + a' * j) := by
    calc
      _ = (a.gcd b : ℤ) * b' + ((a.gcd b : ℤ) * a') * j :=
        congrArg₂ (fun x y ↦ x + y * j) hb' ha'
      _ = _ := by ring
  refine card_le_of_coprime (s := s) hD ha'ne hab' ?_ ?_
  · intro i hi j hj
    have hlow := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).1
    have hhigh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
    exact (sub_le_sub hhigh hlow).trans huv
  · intro j hj
    have ⟨hpos, hsmooth⟩ := (Finset.mem_filter.mp hj).2
    rw [hfac j] at hpos hsmooth
    refine ⟨pos_of_mul_pos_right hpos hgZ.le, Nat.mem_smoothNumbers_of_dvd hsmooth ?_⟩
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.dvd_mul_left _ _

/-- Real endpoints are allowed: `Icc ⌈L⌉ ⌊U⌋` contains exactly the integer parameters
in the closed interval `[L,U]`, even when there are none. Apply the sieve with any
natural bound `D ≥ 1` on the interval length, for example its ceiling when `U - L ≥ 1`. -/
public theorem card_smooth_affine_interval_le {X D : ℕ} {a b : ℤ} {L U : ℝ}
    (hX : 2 ≤ X) (hD : 1 ≤ D) (ha : a ≠ 0) (hLU : U - L ≤ (D : ℝ)) :
    ((Finset.Icc ⌈L⌉ ⌊U⌋).filter (fun j ↦ 0 < b + a * j ∧
      (b + a * j).natAbs ∈ Nat.smoothNumbers (X + 1))).card ≤
      (X + 2) * (Nat.smoothNumbersUpTo D (X + 1)).card := by
  apply card_smooth_affine_int_interval_le hX hD ha
  have h := (sub_le_sub (Int.floor_le U) (Int.le_ceil L)).trans hLU
  exact_mod_cast h

end AffineSmoothInterval
