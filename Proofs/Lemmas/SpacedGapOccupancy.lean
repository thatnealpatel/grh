module

public import Lemmas.SpacedGapCollinearity
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Occupancy in a spaced gap rectangle

Source: `db84b3c3:.godel/alice/spaced-product-cut.md:15–23`, used by
`.godel/alice/forced-output-cuts.md:57`; the source passage is unchanged at
writing pin `4fc0c11e733130fcdf9bfcd06551f27df43e744d`.

Scope: the occupied-rectangle primitive-direction certificate in the branch
`s ≤ L`, including the reduced divisibility and the nonvanishing of the
primitive linear form. This does not count smooth divisors or moduli.

Owning check session: `01a20f51-211d-73b8-9726-8aa026238fa2`.
-/

open scoped BigOperators

namespace SpacedGapOccupancy

private theorem exists_adjacent_gap_le_average {m : ℕ} (hm : 0 < m)
    (x : Fin (m + 1) → ℝ) :
    ∃ i : Fin m, x i.succ - x i.castSucc ≤ (x (Fin.last m) - x 0) / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hsum : ∑ i : Fin m, (x i.succ - x i.castSucc) = x (Fin.last m) - x 0 := by
    rw [Finset.sum_sub_distrib]
    have h := (Fin.sum_univ_succ x).symm.trans (Fin.sum_univ_castSucc x)
    linarith only [h]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le
    (f := fun i : Fin m => x i.succ - x i.castSucc)
    (g := fun _ => (x (Fin.last m) - x 0) / (m : ℝ)) hnonempty (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum,
        mul_comm (m : ℝ), div_mul_cancel₀ _ hmR.ne'])
  exact ⟨i, hi⟩

private theorem abs_sub_le_of_center {x y c W : ℝ}
    (hx : |x - c| ≤ W) (hy : |y - c| ≤ W) : |x - y| ≤ 2 * W := by
  calc
    |x - y| = |(x - c) - (y - c)| := by rw [sub_sub_sub_cancel_right]
    _ ≤ |x - c| + |y - c| := abs_sub _ _
    _ ≤ 2 * W := by simpa only [two_mul] using add_le_add hx hy

private theorem exists_short_collinear_pair
    {S : Finset (ℤ × ℤ)} {m : ℕ} {j₀ b₀ U V : ℝ} (hm : 0 < m) (hcard : S.card = m + 1)
    (hbox : ∀ p ∈ S, |(p.1 : ℝ) - j₀| ≤ U ∧ |(p.2 : ℝ) - b₀| ≤ V)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → q.1 - p.1 ≠ 0)
    (hdet : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
      (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2) = 0) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
      |((q.1 - p.1 : ℤ) : ℝ)| ≤ 2 * U / (m : ℝ) ∧
      |((q.2 - p.2 : ℤ) : ℝ)| ≤ 2 * V / (m : ℝ) := by
  let T := S.image Prod.fst
  have hinj : Set.InjOn Prod.fst (S : Set (ℤ × ℤ)) := by
    intro p hp q hq heq
    by_contra hpq
    exact hsep p hp q hq hpq (sub_eq_zero.mpr heq.symm)
  have hcardT : T.card = m + 1 := (Finset.card_image_of_injOn hinj).trans hcard
  let x := T.orderEmbOfFin hcardT
  have hlift (i : Fin (m + 1)) : ∃ p ∈ S, p.1 = x i :=
    Finset.mem_image.mp (T.orderEmbOfFin_mem hcardT i)
  choose P hPS hPx using hlift
  let J (i : Fin (m + 1)) : ℝ := (P i).1
  let Y (i : Fin (m + 1)) : ℝ := (P i).2
  have hJ : StrictMono J := by
    intro i j hij
    apply Int.cast_lt.mpr
    rw [hPx i, hPx j]
    exact x.strictMono hij
  let l : Fin (m + 1) := 0
  let r : Fin (m + 1) := Fin.last m
  have hspan_pos : 0 < J r - J l := sub_pos.mpr (hJ (Fin.lt_def.mpr hm))
  obtain ⟨i, hi⟩ := exists_adjacent_gap_le_average hm J
  change J i.succ - J i.castSucc ≤ (J r - J l) / (m : ℝ) at hi
  have hgap_pos : 0 < J i.succ - J i.castSucc := sub_pos.mpr (hJ Fin.castSucc_lt_succ)
  have hspanJ : J r - J l ≤ 2 * U := (le_abs_self _).trans
    (abs_sub_le_of_center (hbox _ (hPS r)).1 (hbox _ (hPS l)).1)
  have hspanY : |Y r - Y l| ≤ 2 * V :=
    abs_sub_le_of_center (hbox _ (hPS r)).2 (hbox _ (hPS l)).2
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- The smaller first-coordinate gap scales by the same ratio in the second coordinate.
  have hline (j : Fin (m + 1)) :
      (J r - J l) * (Y j - Y l) = (J j - J l) * (Y r - Y l) := by
    have hj := sub_eq_zero.mp (hdet _ (hPS l) _ (hPS r) _ (hPS j))
    simpa only [Int.cast_mul, Int.cast_sub, J, Y] using congrArg (fun z : ℤ => (z : ℝ)) hj
  have hdiff : (J r - J l) * (Y i.succ - Y i.castSucc) =
      (J i.succ - J i.castSucc) * (Y r - Y l) := calc
    _ = (J r - J l) * (Y i.succ - Y l) - (J r - J l) * (Y i.castSucc - Y l) := by ring
    _ = _ := by rw [hline i.succ, hline i.castSucc]; ring
  have habs := congrArg abs hdiff
  simp only [abs_mul, abs_of_pos hspan_pos, abs_of_pos hgap_pos] at habs
  have hYgap : |Y i.succ - Y i.castSucc| ≤ |Y r - Y l| / (m : ℝ) := by
    apply le_of_mul_le_mul_left _ hspan_pos
    calc
      _ = (J i.succ - J i.castSucc) * |Y r - Y l| := habs
      _ ≤ ((J r - J l) / (m : ℝ)) * |Y r - Y l| :=
        mul_le_mul_of_nonneg_right hi (abs_nonneg _)
      _ = (J r - J l) * (|Y r - Y l| / (m : ℝ)) := by ring
  refine ⟨P i.castSucc, hPS _, P i.succ, hPS _, ?_, ?_, ?_⟩
  · intro heq
    exact (hJ Fin.castSucc_lt_succ).ne (congrArg (fun p : ℤ × ℤ => (p.1 : ℝ)) heq)
  · rw [Int.cast_sub, show |J i.succ - J i.castSucc| = J i.succ - J i.castSucc from
      abs_of_pos hgap_pos]
    exact hi.trans (div_le_div_of_nonneg_right hspanJ hmR)
  · rw [Int.cast_sub]
    exact hYgap.trans (div_le_div_of_nonneg_right hspanY hmR)

/-- Among `m + 1` distinct solutions in a translated box of half-widths `L / s` and
`H`, there is an actual pair difference `n * v`, with `n > 0` and `v` primitive
and nonzero in both coordinates. Both gaps are at most the corresponding side
length divided by `m`. The reduced modulus `f / gcd(f,n)` divides the nonzero
primitive linear form, without requiring coprimality of `s` and `f`. -/
public theorem spacedGapRectangle_occupancy
    {S : Finset (ℤ × ℤ)} {a₀ s A B f : ℤ} {j₀ b₀ L H : ℝ} {m : ℕ}
    (hL : 1 ≤ L) (hLH : L ≤ H) (hs : 1 ≤ s) (hsL : (s : ℝ) ≤ L)
    (hA : 2 * H < (A : ℝ)) (_hB : B ≠ 0) (hAB : IsCoprime A B)
    (hf : 8 * (L / (s : ℝ)) * H < (f : ℝ)) (hfAB : IsCoprime f (A * B))
    (hm : 1 ≤ m) (hcard : S.card = m + 1)
    (hbox : ∀ p ∈ S, |(p.1 : ℝ) - j₀| ≤ L / (s : ℝ) ∧ |(p.2 : ℝ) - b₀| ≤ H)
    (hcong : ∀ p ∈ S, f ∣ A * (a₀ + s * p.1) - B * p.2) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ (n : ℤ) (v : ℤ × ℤ) (k : ℤ),
      p ≠ q ∧ 0 < n ∧ q.1 - p.1 = n * v.1 ∧ q.2 - p.2 = n * v.2 ∧
      Int.gcd v.1 v.2 = 1 ∧ v.1 ≠ 0 ∧ v.2 ≠ 0 ∧
      |((n * v.1 : ℤ) : ℝ)| ≤ 2 * (L / (s : ℝ)) / (m : ℝ) ∧
      |((n * v.2 : ℤ) : ℝ)| ≤ 2 * H / (m : ℝ) ∧
      k = (Int.gcd f n : ℤ) ∧ 1 ≤ k ∧ (k : ℝ) ≤ 2 * (L / (s : ℝ)) / (m : ℝ) ∧
      f / k ∣ A * s * v.1 - B * v.2 ∧ A * s * v.1 - B * v.2 ≠ 0 := by
  have hspos : 0 < s := Int.add_one_le_iff.mp hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hU : 1 ≤ L / (s : ℝ) := (le_div_iff₀ hsR).mpr (by simpa only [one_mul] using hsL)
  have hmod (p : ℤ × ℤ) (hp : p ∈ S) : A * (a₀ + s * p.1) ≡ B * p.2 [ZMOD f] :=
    (Int.modEq_iff_dvd.mpr (hcong p hp)).symm
  obtain ⟨hdet, hsep, _⟩ := SpacedGapCollinearity.spacedGapRectangle_geometry
    (S := ↑S) hspos hU hLH hf hfAB.of_mul_right_left hfAB.of_mul_right_right hbox hmod
  obtain ⟨p, hp, q, hq, hpq, hjshort, hbshort⟩ := exists_short_collinear_pair hm hcard hbox
    (fun p hp q hq hpq => (hsep p hp q hq hpq).1) hdet
  obtain ⟨hj₀, hb₀⟩ := hsep p hp q hq hpq
  let d₁ : ℤ := q.1 - p.1
  let d₂ : ℤ := q.2 - p.2
  let n : ℤ := Int.gcd d₁ d₂
  let v : ℤ × ℤ := (d₁ / n, d₂ / n)
  have hngcd : 0 < Int.gcd d₁ d₂ := Int.gcd_pos_of_ne_zero_left d₂ hj₀
  have hn : 0 < n := by
    change (0 : ℤ) < (Int.gcd d₁ d₂ : ℤ)
    exact_mod_cast hngcd
  have hfactor {z : ℤ} (hz : n ∣ z) : z = n * (z / n) := by
    rw [mul_comm, Int.ediv_mul_cancel hz]
  have hj : q.1 - p.1 = n * v.1 := hfactor (Int.gcd_dvd_left d₁ d₂)
  have hb : q.2 - p.2 = n * v.2 := hfactor (Int.gcd_dvd_right d₁ d₂)
  have hvprim : Int.gcd v.1 v.2 = 1 := Int.gcd_ediv_gcd_ediv_gcd hngcd
  have hv₁ : v.1 ≠ 0 := fun hv => hj₀ (by simp only [hj, hv, mul_zero])
  have hv₂ : v.2 ≠ 0 := fun hv => hb₀ (by simp only [hb, hv, mul_zero])
  rw [hj] at hjshort
  rw [hb] at hbshort
  let k : ℤ := Int.gcd f n
  have hk : 0 < k := by
    change (0 : ℤ) < (Int.gcd f n : ℤ)
    exact_mod_cast Int.gcd_pos_of_ne_zero_right f hn.ne'
  have hkn : (k : ℝ) ≤ (n : ℝ) := Int.cast_le.mpr (Int.le_of_dvd hn (Int.gcd_dvd_right f n))
  have hnj : (n : ℝ) ≤ |((n * v.1 : ℤ) : ℝ)| := by
    have h : n ≤ |n * v.1| := by
      rw [abs_mul, abs_of_pos hn]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Int.one_le_abs hv₁) hn.le
    exact_mod_cast h
  refine ⟨p, hp, q, hq, n, v, k, hpq, hn, hj, hb, hvprim, hv₁, hv₂, hjshort, hbshort,
    rfl, Int.add_one_le_iff.mpr hk, hkn.trans (hnj.trans hjshort), ?_, ?_⟩
  · have hdvd : f ∣ n * (A * s * v.1 - B * v.2) := by
      convert dvd_sub (hcong q hq) (hcong p hp) using 1
      calc
        _ = A * s * (n * v.1) - B * (n * v.2) := by ring
        _ = _ := by rw [← hj, ← hb]; ring
    -- Replace `n` by its gcd with `f` under divisibility, then divide by that gcd.
    have h := Int.ediv_dvd_ediv (Int.gcd_dvd_left f n) (Int.dvd_gcd_mul_iff_dvd_mul.mpr hdvd)
    change f / k ∣ k * (A * s * v.1 - B * v.2) / k at h
    rwa [Int.mul_ediv_cancel_left _ hk.ne'] at h
  · intro hz
    -- A vanishing form would force `A ∣ v.2`, too large for the vertical side.
    have hmul : A ∣ B * v.2 := ⟨s * v.1, by
      rw [← sub_eq_zero.mp hz, mul_assoc]⟩
    have hzdiv : A ∣ v.2 := hAB.dvd_of_dvd_mul_left hmul
    have hlarge : A ≤ |v.2| := Int.le_of_dvd (abs_pos.mpr hv₂) ((dvd_abs A v.2).mpr hzdiv)
    have hlargeR : (A : ℝ) ≤ |(v.2 : ℝ)| := by exact_mod_cast hlarge
    have hn1 : (1 : ℤ) ≤ n := Int.add_one_le_iff.mpr hn
    have hv₂le : |(v.2 : ℝ)| ≤ |((n * v.2 : ℤ) : ℝ)| := by
      have h : |v.2| ≤ |n * v.2| := by
        rw [abs_mul, abs_of_pos hn]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hn1 (abs_nonneg v.2)
      exact_mod_cast h
    have hH : 0 ≤ 2 * H := mul_nonneg zero_le_two (zero_le_one.trans (hL.trans hLH))
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact (not_lt_of_ge hlargeR) ((hv₂le.trans (hbshort.trans (div_le_self hH hmR))).trans_lt hA)

end SpacedGapOccupancy
