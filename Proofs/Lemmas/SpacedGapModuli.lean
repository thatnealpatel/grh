module

public import Lemmas.SpacedGapOccupancy
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting occupied spaced-gap crossing moduli

Source: `a9dedc89666e:.godel/alice/spaced-product-cut.md:15–23`, unchanged at
`a433ed178`; consumer: `.godel/alice/forced-output-cuts.md:57`.

Scope: the finite `s ≤ L` branch with `m ≥ 2`. The bound counts distinct smooth
crossing moduli using actual affine solution sets in the translated box. It
includes the second crossing, the two signed primitive directions, and divisor
recovery; it does not estimate the smooth menus or the divisor bound analytically.

Owning check session: `01a20f6c-c41c-70db-8373-949d4b4e2596`.
-/

open scoped BigOperators

namespace SpacedGapModuli

/-- Integer points in the closed translated rectangle of half-widths `U,V`. -/
@[expose] public noncomputable def integerBox (j₀ b₀ U V : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc ⌈j₀ - U⌉ ⌊j₀ + U⌋ ×ˢ Finset.Icc ⌈b₀ - V⌉ ⌊b₀ + V⌋

public theorem mem_integerBox {j₀ b₀ U V : ℝ} {p : ℤ × ℤ} :
    p ∈ integerBox j₀ b₀ U V ↔ |(p.1 : ℝ) - j₀| ≤ U ∧ |(p.2 : ℝ) - b₀| ≤ V := by
  simp only [integerBox, Finset.mem_product, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Actual nonvanishing affine solutions for `f` in the spaced coordinates `(j,b)`. -/
@[expose] public noncomputable def affineSolutions (a₀ s A B : ℤ) (j₀ b₀ L H : ℝ)
    (f : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact (integerBox j₀ b₀ (L / (s : ℝ)) H).filter fun p =>
    let N := A * (a₀ + s * p.1) - B * p.2
    N ≠ 0 ∧ (f : ℤ) ∣ N

public theorem mem_affineSolutions {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {f : ℕ} {p : ℤ × ℤ} :
    p ∈ affineSolutions a₀ s A B j₀ b₀ L H f ↔
      (|(p.1 : ℝ) - j₀| ≤ L / (s : ℝ) ∧ |(p.2 : ℝ) - b₀| ≤ H) ∧
      A * (a₀ + s * p.1) - B * p.2 ≠ 0 ∧ (f : ℤ) ∣ A * (a₀ + s * p.1) - B * p.2 := by
  simp only [affineSolutions, Finset.mem_filter, mem_integerBox]

/-- The moduli `8UV < f ≤ 8XUV` coprime to `AB` with at least `m+1` affine solutions.
Here and below `X`-smooth means all prime factors are at most `X`. -/
@[expose] public noncomputable def crossingModuli (a₀ s A B : ℤ) (j₀ b₀ L H : ℝ)
    (X m : ℕ) : Finset ℕ := by
  classical
  let U := L / (s : ℝ)
  exact (Nat.smoothNumbersUpTo ⌊8 * (X : ℝ) * U * H⌋₊ (X + 1)).filter fun f =>
    8 * U * H < (f : ℝ) ∧ IsCoprime (f : ℤ) (A * B) ∧
      m + 1 ≤ (affineSolutions a₀ s A B j₀ b₀ L H f).card

public theorem mem_crossingModuli {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {X m f : ℕ} :
    let U := L / (s : ℝ)
    f ∈ crossingModuli a₀ s A B j₀ b₀ L H X m ↔
      ((f : ℝ) ≤ 8 * (X : ℝ) * U * H ∧ f ∈ Nat.smoothNumbers (X + 1)) ∧
      8 * U * H < (f : ℝ) ∧ IsCoprime (f : ℤ) (A * B) ∧
      m + 1 ≤ (affineSolutions a₀ s A B j₀ b₀ L H f).card := by
  simp only [crossingModuli, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
  constructor
  · rintro ⟨⟨hf, hsm⟩, h⟩
    exact ⟨⟨(Nat.le_floor_iff' hsm.1).mp hf, hsm⟩, h⟩
  · rintro ⟨⟨hf, hsm⟩, h⟩
    exact ⟨⟨Nat.le_floor hf, hsm⟩, h⟩

/-- Positive eligible values of `k = gcd(f,n)`. -/
@[expose] public noncomputable def multiplierMenu (U : ℝ) (m : ℕ) : Finset ℕ :=
  Finset.Icc 1 ⌊2 * U / (m : ℝ)⌋₊

/-- The strict determinant threshold for a second crossing at multiplier `k`. -/
@[expose] public noncomputable def threshold (U V : ℝ) (m k : ℕ) : ℝ :=
  8 * U * V / ((m : ℝ) * (k : ℝ)) ^ 2

/-- The smooth second crossings with `B` a unit and overshoot at most `X`. -/
@[expose] public noncomputable def crossingMenu (B : ℤ) (U V : ℝ) (X m k : ℕ) : Finset ℕ := by
  classical
  let T := threshold U V m k
  exact (Nat.smoothNumbersUpTo ⌊(X : ℝ) * T⌋₊ (X + 1)).filter fun t =>
    T < (t : ℝ) ∧ IsCoprime (t : ℤ) B

public theorem mem_crossingMenu {B : ℤ} {U V : ℝ} {X m k t : ℕ} :
    let T := threshold U V m k
    t ∈ crossingMenu B U V X m k ↔
      ((t : ℝ) ≤ (X : ℝ) * T ∧ t ∈ Nat.smoothNumbers (X + 1)) ∧
      T < (t : ℝ) ∧ IsCoprime (t : ℤ) B := by
  simp only [crossingMenu, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
  constructor
  · rintro ⟨⟨ht, hsm⟩, h⟩
    exact ⟨⟨(Nat.le_floor_iff' hsm.1).mp ht, hsm⟩, h⟩
  · rintro ⟨⟨ht, hsm⟩, h⟩
    exact ⟨⟨Nat.le_floor ht, hsm⟩, h⟩

/-- The primitive linear form whose nonzero absolute value supplies the divisor bound. -/
@[expose] public def directionForm (A B s : ℤ) (v : ℤ × ℤ) : ℤ :=
  A * s * v.1 - B * v.2

/-- Primitivity is `gcd(v₁,v₂) = 1`, with both orientations allowed. -/
public structure Direction (A B s : ℤ) (U V : ℝ) (m k t : ℕ) (v : ℤ × ℤ) : Prop where
  primitive : Int.gcd v.1 v.2 = 1
  fst_ne : v.1 ≠ 0
  snd_ne : v.2 ≠ 0
  fst_bound : |(v.1 : ℝ)| ≤ 2 * U / ((m : ℝ) * (k : ℝ))
  snd_bound : |(v.2 : ℝ)| ≤ 2 * V / ((m : ℝ) * (k : ℝ))
  dvd : (t : ℤ) ∣ directionForm A B s v
  form_ne : directionForm A B s v ≠ 0

/-- A smooth `g` above a threshold `T ≥ 1` has a smooth divisor crossing it with
overshoot at most `X`. A least crossing divisor proves this for any factor order of
that divisor: removing one prime factor puts it back at or below the threshold. -/
public theorem exists_smooth_crossing_divisor {g X : ℕ} {T : ℝ}
    (hg : g ∈ Nat.smoothNumbers (X + 1)) (hT : 1 ≤ T) (hTg : T < (g : ℝ)) :
    ∃ t : ℕ, t ∣ g ∧ t ∈ Nat.smoothNumbers (X + 1) ∧ T < (t : ℝ) ∧
      (t : ℝ) ≤ (X : ℝ) * T := by
  let h : ∃ t : ℕ, t ∣ g ∧ T < (t : ℝ) := ⟨g, dvd_rfl, hTg⟩
  let t := Nat.find h
  have ht : t ∣ g ∧ T < (t : ℝ) := Nat.find_spec h
  have hts := Nat.mem_smoothNumbers_of_dvd hg ht.1
  have ht₁ : t ≠ 1 := by
    intro he
    simpa only [he, Nat.cast_one, not_lt_of_ge hT] using ht.2
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht₁
  have hpt' : t / p * p = t := Nat.div_mul_cancel hpt
  have hsmall : t / p < t := Nat.div_lt_self (Nat.pos_of_ne_zero hts.1) hp.one_lt
  have hsmallT : ((t / p : ℕ) : ℝ) ≤ T := by
    apply le_of_not_gt
    intro hgt
    exact Nat.find_min h hsmall ⟨(show t / p ∣ t from ⟨p, hpt'.symm⟩).trans ht.1, hgt⟩
  have hpX : p ≤ X := Nat.lt_succ_iff.mp (Nat.mem_smoothNumbers'.mp hts p hp hpt)
  refine ⟨t, ht.1, hts, ht.2, ?_⟩
  calc
    (t : ℝ) = ((t / p : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast hpt'.symm
    _ ≤ T * (X : ℝ) := mul_le_mul hsmallT (by exact_mod_cast hpX) (Nat.cast_nonneg _) (by linarith)
    _ = (X : ℝ) * T := mul_comm _ _

/-- An occupied smooth crossing modulus has a second crossing `t` of its smooth
quotient `f/k`. Its actual short pair supplies a signed primitive direction in the
strict determinant box, with nonzero form divisible by that quotient. -/
public theorem exists_crossingModulus_direction
    {S : Finset (ℤ × ℤ)} {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {f X m : ℕ}
    (hL : 1 ≤ L) (hLH : L ≤ H) (hs : 1 ≤ s) (hsL : (s : ℝ) ≤ L)
    (hA : 2 * H < (A : ℝ)) (hB : B ≠ 0) (hAB : IsCoprime A B)
    (hf : 8 * (L / (s : ℝ)) * H < (f : ℝ)) (hfAB : IsCoprime (f : ℤ) (A * B))
    (hfs : f ∈ Nat.smoothNumbers (X + 1)) (hm : 2 ≤ m) (hcard : m + 1 ≤ S.card)
    (hbox : ∀ p ∈ S, |(p.1 : ℝ) - j₀| ≤ L / (s : ℝ) ∧ |(p.2 : ℝ) - b₀| ≤ H)
    (hcong : ∀ p ∈ S, (f : ℤ) ∣ A * (a₀ + s * p.1) - B * p.2) :
    ∃ k ∈ multiplierMenu (L / (s : ℝ)) m, ∃ t ∈ crossingMenu B (L / (s : ℝ)) H X m k,
      ∃ v, Direction A B s (L / (s : ℝ)) H m k t v ∧ k ∣ f ∧ t ∣ f / k ∧
        ((f / k : ℕ) : ℤ) ∣ directionForm A B s v ∧ f / k ∈ Nat.smoothNumbers (X + 1) := by
  obtain ⟨S', hS', hcS'⟩ := Finset.exists_subset_card_eq hcard
  have hf' : 8 * (L / (s : ℝ)) * H < ((f : ℤ) : ℝ) := by simpa using hf
  obtain ⟨_, _, _, _, n, v, k', _, hn, _, _, hp, hv₁, hv₂, hgap₁, hgap₂, hk', hk₁',
    hkU', hfdvd', hne⟩ := SpacedGapOccupancy.spacedGapRectangle_occupancy
      (S := S') hL hLH hs hsL hA hB hAB hf' hfAB (by omega) hcS'
        (fun p hp => hbox p (hS' hp)) (fun p hp => hcong p (hS' hp))
  let U := L / (s : ℝ)
  let k := Int.gcd (f : ℤ) n
  have hkcast : (k : ℤ) = k' := hk'.symm
  have hk₁ : 1 ≤ k := by exact_mod_cast (hkcast ▸ hk₁')
  have hkU : (k : ℝ) ≤ 2 * U / (m : ℝ) := by simpa only [← hkcast, Int.cast_natCast] using hkU'
  have hkInt : (k : ℤ) ∣ (f : ℤ) := Int.gcd_dvd_left (f : ℤ) n
  have hkf : k ∣ f := Int.natCast_dvd_natCast.mp hkInt
  have hkn : (k : ℝ) ≤ (n : ℝ) := by
    have hi : (k : ℤ) ≤ n := Int.le_of_dvd hn (Int.gcd_dvd_right (f : ℤ) n)
    exact_mod_cast hi
  have hfdvd : ((f / k : ℕ) : ℤ) ∣ directionForm A B s v := by
    simpa only [← hkcast, Int.natCast_ediv, directionForm] using hfdvd'
  have hg : f / k ∈ Nat.smoothNumbers (X + 1) :=
    Nat.mem_smoothNumbers_of_dvd hfs ⟨k, (Nat.div_mul_cancel hkf).symm⟩
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hU : 1 ≤ U := (le_div_iff₀ (zero_lt_one.trans_le hsR)).mpr (by simpa only [one_mul] using hsL)
  have hUV : U ≤ H := (div_le_self (zero_le_one.trans hL) hsR).trans hLH
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk₁
  let d : ℝ := (m : ℝ) * (k : ℝ)
  have hmpos : (0 : ℝ) < m := zero_lt_two.trans_le hmR
  have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hkR
  have hdpos : 0 < d := mul_pos hmpos hkpos
  have hdU : d ≤ 2 * U := by rw [show d = (k : ℝ) * (m : ℝ) by exact mul_comm _ _]; exact (le_div_iff₀ hmpos).mp hkU
  have hdsq : 0 < d ^ 2 := pow_pos hdpos _
  have hT₂ : 2 ≤ threshold U H m k := (le_div_iff₀ hdsq).mpr (calc
    2 * d ^ 2 ≤ 2 * (2 * U) ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hdpos.le hdU 2) zero_le_two
    _ = (8 * U) * U := by ring
    _ ≤ 8 * U * H := mul_le_mul_of_nonneg_left hUV (mul_nonneg (by norm_num) (zero_le_one.trans hU)))
  have hkd : (k : ℝ) ≤ d := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_two.trans hmR) hkpos.le
  have hkdsq : (k : ℝ) ≤ d ^ 2 := hkd.trans (le_self_pow₀ (hkR.trans hkd) (by decide))
  have h8U : 0 ≤ 8 * U := mul_nonneg (by norm_num) (zero_le_one.trans hU)
  have hH : 0 ≤ H := zero_le_one.trans (hL.trans hLH)
  have hTg : threshold U H m k < ((f / k : ℕ) : ℝ) := calc
    _ ≤ 8 * U * H / (k : ℝ) := div_le_div_of_nonneg_left (mul_nonneg h8U hH) hkpos hkdsq
    _ < _ := (div_lt_iff₀ hkpos).mpr (by
      rw [show ((f / k : ℕ) : ℝ) * (k : ℝ) = (f : ℝ) by exact_mod_cast Nat.div_mul_cancel hkf]
      exact hf)
  obtain ⟨t, htg, hts, hTt, htX⟩ := exists_smooth_crossing_divisor hg (one_le_two.trans hT₂) hTg
  have htf : (t : ℤ) ∣ (f : ℤ) := Int.natCast_dvd_natCast.mpr
    (htg.trans ⟨k, (Nat.div_mul_cancel hkf).symm⟩)
  have htB : IsCoprime (t : ℤ) B := hfAB.of_mul_right_right.of_isCoprime_of_dvd_left htf
  have hbound {a : ℤ} {W : ℝ} (h : |((n * a : ℤ) : ℝ)| ≤ 2 * W / (m : ℝ)) :
      |(a : ℝ)| ≤ 2 * W / d := by
    rw [Int.cast_mul, abs_mul, abs_of_pos (Int.cast_pos.mpr hn)] at h
    apply (le_div_iff₀ hdpos).mpr
    calc
      |(a : ℝ)| * d = (m : ℝ) * ((k : ℝ) * |(a : ℝ)|) := by dsimp [d]; ring
      _ ≤ (m : ℝ) * ((n : ℝ) * |(a : ℝ)|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkn (abs_nonneg _)) hmpos.le
      _ ≤ 2 * W := by rw [mul_comm (m : ℝ)]; exact (le_div_iff₀ hmpos).mp h
  refine ⟨k, Finset.mem_Icc.mpr ⟨hk₁, Nat.le_floor hkU⟩, t, ?_, v, ?_, hkf, htg, hfdvd, hg⟩
  · exact mem_crossingMenu.mpr ⟨⟨htX, hts⟩, hTt, htB⟩
  · exact ⟨hp, hv₁, hv₂, hbound hgap₁, hbound hgap₂,
      (Int.natCast_dvd_natCast.mpr htg).trans hfdvd, hne⟩

private theorem eq_or_eq_neg_of_det_zero {v w : ℤ × ℤ}
    (hv : Int.gcd v.1 v.2 = 1) (hw : Int.gcd w.1 w.2 = 1)
    (he : v.1 * w.2 = w.1 * v.2) : w = v ∨ w = (-v.1, -v.2) := by
  obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hv
  obtain ⟨c, d, hcd⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hw
  let z := a * w.1 + b * w.2
  have hw₁ : w.1 = z * v.1 := calc
    w.1 = (a * v.1 + b * v.2) * w.1 := by rw [hab, one_mul]
    _ = a * (v.1 * w.1) + b * (w.1 * v.2) := by ring
    _ = _ := by rw [← he]; dsimp [z]; ring
  have hw₂ : w.2 = z * v.2 := calc
    w.2 = (a * v.1 + b * v.2) * w.2 := by rw [hab, one_mul]
    _ = a * (v.1 * w.2) + b * (v.2 * w.2) := by ring
    _ = _ := by rw [he]; dsimp [z]; ring
  have hz : z ∣ (1 : ℤ) := ⟨c * v.1 + d * v.2, by rw [← hcd, hw₁, hw₂]; ring⟩
  rcases Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr hz) with hz | hz
  · exact Or.inl (Prod.ext (by rw [hw₁, hz, one_mul]) (by rw [hw₂, hz, one_mul]))
  · exact Or.inr (Prod.ext (by rw [hw₁, hz, neg_one_mul]) (by rw [hw₂, hz, neg_one_mul]))

/-- Above the strict determinant threshold, two eligible signed primitive vectors
are equal up to sign. The modulus need only be coprime to `B`, not to `s`. -/
public theorem direction_eq_or_eq_neg {A B s : ℤ} {U V : ℝ} {m k t : ℕ} {v w : ℤ × ℤ}
    (hT : threshold U V m k < (t : ℝ)) (htB : IsCoprime (t : ℤ) B)
    (hv : Direction A B s U V m k t v) (hw : Direction A B s U V m k t w) :
    w = v ∨ w = (-v.1, -v.2) := by
  let D : ℤ := v.1 * w.2 - w.1 * v.2
  have hBdet : B * D = w.1 * directionForm A B s v - v.1 * directionForm A B s w := by
    dsimp [D, directionForm]
    ring
  have hdvd : (t : ℤ) ∣ D := htB.dvd_of_dvd_mul_left (by
    rw [hBdet]
    exact dvd_sub (hv.dvd.mul_left _) (hw.dvd.mul_left _))
  let d : ℝ := (m : ℝ) * (k : ℝ)
  let x : ℝ := 2 * U / d
  let y : ℝ := 2 * V / d
  have hx : 0 ≤ x := (abs_nonneg _).trans hv.fst_bound
  have habs : |(D : ℝ)| ≤ threshold U V m k := calc
    |(D : ℝ)| ≤ |(v.1 : ℝ) * (w.2 : ℝ)| + |(w.1 : ℝ) * (v.2 : ℝ)| := by
      simp only [D, Int.cast_sub, Int.cast_mul]
      exact abs_sub _ _
    _ ≤ x * y + x * y := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hv.fst_bound hw.snd_bound (abs_nonneg _) hx)
        (mul_le_mul hw.fst_bound hv.snd_bound (abs_nonneg _) hx)
    _ = threshold U V m k := by
      change 2 * U / d * (2 * V / d) + 2 * U / d * (2 * V / d) = 8 * U * V / d ^ 2
      rw [div_mul_div_comm, ← pow_two, ← add_div]
      congr 1
      ring
  have hD : D = 0 := by
    by_contra hne
    have hlarge : (t : ℤ) ≤ |D| := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
    have hlargeR : (t : ℝ) ≤ |(D : ℝ)| := by exact_mod_cast hlarge
    exact (not_lt_of_ge (hlargeR.trans habs)) hT
  exact eq_or_eq_neg_of_det_zero hv.primitive hw.primitive (sub_eq_zero.mp hD)

/-- Any finite set of eligible directions at fixed `k,t` has at most two elements,
with the two possible elements corresponding to opposite orientations. -/
public theorem card_le_two_of_directions {A B s : ℤ} {U V : ℝ} {m k t : ℕ}
    {P : Finset (ℤ × ℤ)} (hT : threshold U V m k < (t : ℝ)) (htB : IsCoprime (t : ℤ) B)
    (hP : ∀ v ∈ P, Direction A B s U V m k t v) : P.card ≤ 2 := by
  classical
  by_cases h : P.Nonempty
  · obtain ⟨v, hv⟩ := h
    apply le_trans (Finset.card_le_card (t := {v, (-v.1, -v.2)}) ?_) Finset.card_le_two
    intro w hw
    rcases direction_eq_or_eq_neg hT htB (hP v hv) (hP w hw) with rfl | he
    · exact Finset.mem_insert_self _ _
    · rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

/-- The distinct moduli in `F` that are recovered through `k,t` and some eligible
primitive vector. Membership requires exact divisibility by `k` before recovery. -/
@[expose] public noncomputable def modulusFiber (F : Finset ℕ) (A B s : ℤ) (U V : ℝ)
    (m k t : ℕ) : Finset ℕ := by
  classical
  exact F.filter fun f => ∃ v, Direction A B s U V m k t v ∧ k ∣ f ∧ t ∣ f / k ∧
    ((f / k : ℕ) : ℤ) ∣ directionForm A B s v

private noncomputable def quotientFiber (F : Finset ℕ) (k t : ℕ) (N : ℤ) : Finset ℕ := by
  classical
  exact F.filter fun f => k ∣ f ∧ t ∣ f / k ∧ f / k ∈ N.natAbs.divisors

private theorem card_quotientFiber_le (F : Finset ℕ) (k t : ℕ) (N : ℤ) :
    (quotientFiber F k t N).card ≤ N.natAbs.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun f : ℕ => f / k)
  · intro f hf
    exact (Finset.mem_filter.mp hf).2.2.2
  · intro f hf g hg heq
    calc
      f = f / k * k := (Nat.div_mul_cancel (Finset.mem_filter.mp hf).2.1).symm
      _ = g / k * k := congrArg (· * k) heq
      _ = g := Nat.div_mul_cancel (Finset.mem_filter.mp hg).2.1

/-- For fixed `k,t`, the two possible signed directions contribute at most `2 * D`
distinct moduli. Once `k` is fixed, the recovered quotient determines `f`. -/
public theorem card_modulusFiber_le {F : Finset ℕ} {A B s : ℤ} {U V : ℝ} {m k t D : ℕ}
    (hT : threshold U V m k < (t : ℝ)) (htB : IsCoprime (t : ℤ) B)
    (hD : ∀ v, Direction A B s U V m k t v → (directionForm A B s v).natAbs.divisors.card ≤ D) :
    (modulusFiber F A B s U V m k t).card ≤ 2 * D := by
  classical
  let P := (integerBox 0 0 (2 * U / ((m : ℝ) * (k : ℝ))) (2 * V / ((m : ℝ) * (k : ℝ)))).filter
    (Direction A B s U V m k t)
  have hP : ∀ v ∈ P, Direction A B s U V m k t v := fun _ hv => (Finset.mem_filter.mp hv).2
  have hcover : modulusFiber F A B s U V m k t ⊆
      P.biUnion (fun v => quotientFiber F k t (directionForm A B s v)) := by
    intro f hf
    obtain ⟨hfF, v, hv, hkf, htg, hfdvd⟩ := Finset.mem_filter.mp hf
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨mem_integerBox.mpr ?_, hv⟩, Finset.mem_filter.mpr ⟨hfF, hkf, htg, ?_⟩⟩
    · simpa only [sub_zero] using And.intro hv.fst_bound hv.snd_bound
    · exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hfdvd, Int.natAbs_ne_zero.mpr hv.form_ne⟩
  calc
    _ ≤ (P.biUnion (fun v => quotientFiber F k t (directionForm A B s v))).card := Finset.card_le_card hcover
    _ ≤ ∑ v ∈ P, (quotientFiber F k t (directionForm A B s v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ P, D := Finset.sum_le_sum fun v hv =>
      (card_quotientFiber_le F k t _).trans (hD v (hP v hv))
    _ ≤ 2 * D := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_le_mul_right D (card_le_two_of_directions hT htB hP)

/-- The actual occupied crossing moduli are covered by the union of the eligible
`k,t` fibers. Multiple witnesses do not require disjoint fibers. -/
public theorem crossingModuli_subset_fibers
    {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {X m : ℕ}
    (hL : 1 ≤ L) (hLH : L ≤ H) (hs : 1 ≤ s) (hsL : (s : ℝ) ≤ L)
    (hA : 2 * H < (A : ℝ)) (hB : B ≠ 0) (hAB : IsCoprime A B) (hm : 2 ≤ m) :
    let U := L / (s : ℝ)
    let F := crossingModuli a₀ s A B j₀ b₀ L H X m
    F ⊆ (multiplierMenu U m).biUnion (fun k =>
      (crossingMenu B U H X m k).biUnion (fun t => modulusFiber F A B s U H m k t)) := by
  classical
  dsimp only
  intro f hf
  obtain ⟨⟨_, hfsm⟩, hfU, hfAB, hfcard⟩ := mem_crossingModuli.mp hf
  obtain ⟨k, hk, t, ht, v, hv, hkf, htg, hfdvd, _⟩ := exists_crossingModulus_direction
    hL hLH hs hsL hA hB hAB hfU hfAB hfsm hm hfcard
    (fun _ hp => (mem_affineSolutions.mp hp).1)
    (fun _ hp => (mem_affineSolutions.mp hp).2.2)
  exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_biUnion.mpr
    ⟨t, ht, Finset.mem_filter.mpr ⟨hf, v, hv, hkf, htg, hfdvd⟩⟩⟩

/-- Finite spaced-gap crossing-modulus count. The sum uses the actual smooth
`t` menus and a uniform divisor-count bound `D` on the nonzero form. It counts
moduli, not directions, witnesses, or incidences. -/
public theorem card_crossingModuli_le
    {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {X m D : ℕ}
    (hL : 1 ≤ L) (hLH : L ≤ H) (hs : 1 ≤ s) (hsL : (s : ℝ) ≤ L)
    (hA : 2 * H < (A : ℝ)) (hB : B ≠ 0) (hAB : IsCoprime A B) (hm : 2 ≤ m)
    (hD : ∀ k ∈ multiplierMenu (L / (s : ℝ)) m, ∀ t ∈ crossingMenu B (L / (s : ℝ)) H X m k,
      ∀ v, Direction A B s (L / (s : ℝ)) H m k t v →
        (directionForm A B s v).natAbs.divisors.card ≤ D) :
    (crossingModuli a₀ s A B j₀ b₀ L H X m).card ≤
      ∑ k ∈ multiplierMenu (L / (s : ℝ)) m, (crossingMenu B (L / (s : ℝ)) H X m k).card * 2 * D := by
  classical
  let U := L / (s : ℝ)
  let F := crossingModuli a₀ s A B j₀ b₀ L H X m
  let M := multiplierMenu U m
  let T k := crossingMenu B U H X m k
  let G k t := modulusFiber F A B s U H m k t
  calc
    F.card ≤ (M.biUnion (fun k => (T k).biUnion (G k))).card := Finset.card_le_card
      (crossingModuli_subset_fibers hL hLH hs hsL hA hB hAB hm)
    _ ≤ ∑ k ∈ M, ((T k).biUnion (G k)).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ M, ∑ t ∈ T k, (G k t).card := Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
    _ ≤ ∑ k ∈ M, (T k).card * 2 * D := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ∑ _t ∈ T k, 2 * D := by
          apply Finset.sum_le_sum
          intro t ht
          have h := (mem_crossingMenu.mp ht).2
          exact card_modulusFiber_le h.1 h.2 (hD k hk t ht)
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_assoc]

end SpacedGapModuli
