module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Masked gap directions and divisor recovery

Source: `79f24b34:.godel/alice/masked-gap-lcm.md:9–17`, “Count directions before
fixing the cofactors.” The next use is the recovered-`hᵢ` input to the scalar and endpoint
count at lines 19–23, before the per-mask numerator allowance is used at line 25.

We count actual signed directions and cofactor tuples for one fixed split and one
centred box. The scalar `G` and numerator `c` may vary with each tuple. The theorem
does not select the split, count smooth filters, or bound scalar or numerator recovery.

Owning check session: `01a209ce-61c0-7258-9ef8-09cad8ad12db`.
-/

namespace MaskedGapDirections

/-- Data held fixed during the direction count. `pᵢ` and `Dᵢ` are the two fixed mask
parts of each row and gap, and `j` is the fixed common cofactor. -/
public structure FixedRows where
  d : ℤ
  q : ℤ
  j : ℤ
  F₁ : ℤ
  F₂ : ℤ
  p₁ : ℤ
  p₂ : ℤ
  D₁ : ℤ
  D₂ : ℤ

/-- The data being counted, with no scalar or numerator witness attached. -/
public structure Cofactors where
  u₁ : ℕ
  u₂ : ℕ
  v₁ : ℤ
  v₂ : ℤ
  deriving DecidableEq

/-- The two integer coordinates keep their signs. -/
@[expose] public def Cofactors.direction (t : Cofactors) : ℤ × ℤ :=
  ((t.u₂ : ℤ) * t.v₁, (t.u₁ : ℤ) * t.v₂)

@[expose] public def FixedRows.A (R : FixedRows) : ℤ := R.F₂ * R.p₂ * R.D₁

@[expose] public def FixedRows.B (R : FixedRows) : ℤ := R.F₁ * R.p₁ * R.D₂

/-- The four coprimalities and the actual row congruences, with `hᵢ = pᵢ j uᵢ`
and `δᵢ = Dᵢ G vᵢ` substituted. The unit condition is on `q G j` as in the
source, and `G` is positive. The proof needs no separate positivity hypotheses
on `q`, `j`, or the individual fixed row and mask factors. -/
public structure RowConditions (R : FixedRows) (t : Cofactors) : Prop where
  u₁_pos : 0 < t.u₁
  u₂_pos : 0 < t.u₂
  v₁_ne : t.v₁ ≠ 0
  v₂_ne : t.v₂ ≠ 0
  coprime_u : IsCoprime (t.u₁ : ℤ) (t.u₂ : ℤ)
  coprime_v : IsCoprime t.v₁ t.v₂
  coprime₁ : IsCoprime (t.u₁ : ℤ) t.v₁
  coprime₂ : IsCoprime (t.u₂ : ℤ) t.v₂
  rows : ∃ c G : ℤ, 0 < G ∧ IsCoprime (R.q * G * R.j) R.d ∧
    (c * R.F₁ * (R.p₁ * R.j * t.u₁) ≡ R.q * (R.D₁ * G * t.v₁) [ZMOD R.d]) ∧
    (c * R.F₂ * (R.p₂ * R.j * t.u₂) ≡ R.q * (R.D₂ * G * t.v₂) [ZMOD R.d])

private theorem cancel_modEq {k a b d : ℤ} (hk : IsCoprime k d)
    (h : k * a ≡ k * b [ZMOD d]) : a ≡ b [ZMOD d] := by
  rw [Int.modEq_iff_dvd, ← mul_sub] at h
  exact Int.modEq_iff_dvd.mpr (hk.symm.dvd_of_dvd_mul_left h)

/-- Eliminating `c` from the two rows gives the crossed congruence. The four
pairwise coprimalities across the products give a primitive vector. -/
public theorem direction_properties {R : FixedRows} {t : Cofactors} (h : RowConditions R t) :
    t.direction.1 ≠ 0 ∧ t.direction.2 ≠ 0 ∧
    IsCoprime t.direction.1 t.direction.2 ∧
    (R.A * t.direction.1 ≡ R.B * t.direction.2 [ZMOD R.d]) := by
  refine ⟨mul_ne_zero (by exact_mod_cast h.u₂_pos.ne') h.v₁_ne,
    mul_ne_zero (by exact_mod_cast h.u₁_pos.ne') h.v₂_ne,
    (h.coprime_u.symm.mul_right h.coprime₂).mul_left
      (h.coprime₁.symm.mul_right h.coprime_v), ?_⟩
  obtain ⟨c, G, _, hunit, h₁, h₂⟩ := h.rows
  apply cancel_modEq hunit.of_mul_left_left
  calc
    (R.q * G) * (R.A * t.direction.1) ≡
        (c * R.F₁ * (R.p₁ * R.j * t.u₁)) * (R.F₂ * R.p₂ * t.u₂) [ZMOD R.d] := by
          unfold FixedRows.A Cofactors.direction
          convert h₁.symm.mul_right (R.F₂ * R.p₂ * t.u₂) using 1
          ring
    _ ≡ (R.q * G) * (R.B * t.direction.2) [ZMOD R.d] := by
          unfold FixedRows.B Cofactors.direction
          convert h₂.mul_right (R.F₁ * R.p₁ * t.u₁) using 1 <;> ring

/-- Once both fixed divisors are removed from the coordinates, the determinant
of the resulting vectors is divisible by `d`. Only one of the two substituted
unit conditions is needed for this cancellation. -/
public theorem crossed_filter_dvd_det {d A B f₁ f₂ : ℤ} {x y : ℤ × ℤ}
    (hunit : IsCoprime (A * f₂) d)
    (hx : A * x.1 ≡ B * x.2 [ZMOD d]) (hy : A * y.1 ≡ B * y.2 [ZMOD d])
    (hx₁ : f₂ ∣ x.1) (hx₂ : f₁ ∣ x.2) (hy₁ : f₂ ∣ y.1) (hy₂ : f₁ ∣ y.2) :
    d * f₁ * f₂ ∣ x.1 * y.2 - y.1 * x.2 := by
  obtain ⟨a, ha⟩ := hx₁
  obtain ⟨b, hb⟩ := hx₂
  obtain ⟨c, hc⟩ := hy₁
  obtain ⟨e, he⟩ := hy₂
  rw [ha, hb, ← mul_assoc, ← mul_assoc] at hx
  rw [hc, he, ← mul_assoc, ← mul_assoc] at hy
  have h : (A * f₂) * (a * e) ≡ (A * f₂) * (c * b) [ZMOD d] := calc
    _ ≡ (B * f₁) * (b * e) [ZMOD d] := by
      simpa only [mul_assoc] using hx.mul_right e
    _ ≡ _ [ZMOD d] := by
      simpa only [mul_assoc, mul_comm e b] using (hy.mul_right b).symm
  obtain ⟨k, hk⟩ := (cancel_modEq hunit h).symm.dvd
  refine ⟨k, ?_⟩
  rw [ha, hb, hc, he]
  linear_combination (f₁ * f₂) * hk

private theorem det_eq_zero_of_thin_box {m : ℤ} {x y : ℤ × ℤ} {N₁ N₂ : ℝ}
    (hm : 0 < m) (hthin : 2 * N₁ * N₂ < (m : ℝ))
    (hx : |(x.1 : ℝ)| ≤ N₁ ∧ |(x.2 : ℝ)| ≤ N₂)
    (hy : |(y.1 : ℝ)| ≤ N₁ ∧ |(y.2 : ℝ)| ≤ N₂)
    (hdiv : m ∣ x.1 * y.2 - y.1 * x.2) : x.1 * y.2 - y.1 * x.2 = 0 := by
  have hN₁ := (abs_nonneg _).trans hx.1
  have hbound : |((x.1 * y.2 - y.1 * x.2 : ℤ) : ℝ)| ≤ 2 * N₁ * N₂ := by
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul]
    calc
      _ ≤ |(x.1 : ℝ) * y.2| + |(y.1 : ℝ) * x.2| := abs_sub _ _
      _ ≤ N₁ * N₂ + N₁ * N₂ := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hx.1 hy.2 (abs_nonneg _) hN₁)
          (mul_le_mul hy.1 hx.2 (abs_nonneg _) hN₁)
      _ = _ := by ring
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
  exact_mod_cast (show ((x.1 * y.2 - y.1 * x.2).natAbs : ℝ) < (m.natAbs : ℝ) by
    simpa only [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hmR] using hbound.trans_lt hthin)

private theorem eq_or_neg_of_det_eq_zero {x y : ℤ × ℤ}
    (hx : IsCoprime x.1 x.2) (hy : IsCoprime y.1 y.2)
    (hdet : x.1 * y.2 - y.1 * x.2 = 0) : y = x ∨ y = (-x.1, -x.2) := by
  obtain ⟨a, b, hab⟩ := hx
  let k := a * y.1 + b * y.2
  have h₁ : y.1 = k * x.1 := by
    dsimp only [k]
    linear_combination -y.1 * hab - b * hdet
  have h₂ : y.2 = k * x.2 := by
    dsimp only [k]
    linear_combination -y.2 * hab + a * hdet
  have hk := Int.isCoprime_iff_gcd_eq_one.mp hy
  rw [h₁, h₂, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp ⟨a, b, hab⟩, mul_one] at hk
  rcases Int.natAbs_eq_iff.mp hk with hk | hk
  · exact Or.inl (Prod.ext (by simpa only [hk, Int.ofNat_one, one_mul] using h₁)
      (by simpa only [hk, Int.ofNat_one, one_mul] using h₂))
  · exact Or.inr (Prod.ext (by simpa only [hk, Int.ofNat_one, neg_mul, one_mul] using h₁)
      (by simpa only [hk, Int.ofNat_one, neg_mul, one_mul] using h₂))

private theorem card_le_two_of_primitive_collinear {S : Finset (ℤ × ℤ)}
    (hprim : ∀ x ∈ S, IsCoprime x.1 x.2)
    (hdet : ∀ x ∈ S, ∀ y ∈ S, x.1 * y.2 - y.1 * x.2 = 0) : S.card ≤ 2 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have hsub : S ⊆ {x, (-x.1, -x.2)} := by
      intro y hy
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        eq_or_neg_of_det_eq_zero (hprim x hx) (hprim y hy) (hdet x hx y hy)
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

private def factorPair (t : Cofactors) : ℕ × ℕ := (t.u₂, t.u₁)

private theorem factorPair_mem {t : Cofactors} {n : ℤ × ℤ} (hn : t.direction = n)
    (h₁ : n.1 ≠ 0) (h₂ : n.2 ≠ 0) :
    factorPair t ∈ n.1.natAbs.divisors ×ˢ n.2.natAbs.divisors := by
  subst n
  rw [Finset.mem_product]
  exact ⟨Nat.mem_divisors.mpr ⟨⟨t.v₁.natAbs, by simp [Cofactors.direction,
    factorPair, Int.natAbs_mul]⟩, Int.natAbs_ne_zero.mpr h₁⟩,
    Nat.mem_divisors.mpr ⟨⟨t.v₂.natAbs, by simp [Cofactors.direction,
      factorPair, Int.natAbs_mul]⟩, Int.natAbs_ne_zero.mpr h₂⟩⟩

private theorem eq_of_direction_eq_of_factorPair_eq {s t : Cofactors}
    (hu₁ : 0 < s.u₁) (hu₂ : 0 < s.u₂) (hn : s.direction = t.direction)
    (hf : factorPair s = factorPair t) : s = t := by
  have h₁ : s.u₁ = t.u₁ := congrArg Prod.snd hf
  have h₂ : s.u₂ = t.u₂ := congrArg Prod.fst hf
  have hv₁ : s.v₁ = t.v₁ := by
    have heq := congrArg Prod.fst hn
    change (s.u₂ : ℤ) * s.v₁ = (t.u₂ : ℤ) * t.v₁ at heq
    rw [← h₂] at heq
    exact mul_left_cancel₀ (by exact_mod_cast hu₂.ne') heq
  have hv₂ : s.v₂ = t.v₂ := by
    have heq := congrArg Prod.snd hn
    change (s.u₁ : ℤ) * s.v₂ = (t.u₁ : ℤ) * t.v₂ at heq
    rw [← h₁] at heq
    exact mul_left_cancel₀ (by exact_mod_cast hu₁.ne') heq
  cases s
  cases t
  cases h₁
  cases h₂
  cases hv₁
  cases hv₂
  rfl

/-- For a fixed signed direction, `u₂` is a positive divisor of `|n₁|` and `u₁`
of `|n₂|`. Their choices uniquely determine both signed `vᵢ`, so there are at
most `τ(|n₁|) τ(|n₂|)` tuples. Here `τ` is `Nat.divisors.card`. -/
public theorem card_direction_fiber_le {S : Finset Cofactors} {n : ℤ × ℤ}
    (hpos : ∀ t ∈ S, 0 < t.u₁ ∧ 0 < t.u₂) (h₁ : n.1 ≠ 0) (h₂ : n.2 ≠ 0) :
    (S.filter fun t => t.direction = n).card ≤
      n.1.natAbs.divisors.card * n.2.natAbs.divisors.card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn factorPair
  · intro t ht
    exact factorPair_mem (Finset.mem_filter.mp ht).2 h₁ h₂
  · intro s hs t ht hf
    obtain ⟨hs, hsn⟩ := Finset.mem_filter.mp hs
    obtain ⟨_, htn⟩ := Finset.mem_filter.mp ht
    exact eq_of_direction_eq_of_factorPair_eq (hpos s hs).1 (hpos s hs).2 (hsn.trans htn.symm) hf

/-- The exact set of eligible tuples can be made into a `Finset`: a bounded
integer box has finitely many directions, and each nonzero-coordinate direction
has finite positive-cofactor recovery by the same injection used for the count. -/
public theorem finite_of_bounded_directions {T : Set Cofactors} {N₁ N₂ : ℝ}
    (hpos : ∀ t ∈ T, 0 < t.u₁ ∧ 0 < t.u₂)
    (hne : ∀ t ∈ T, t.direction.1 ≠ 0 ∧ t.direction.2 ≠ 0)
    (hbox : ∀ t ∈ T, |(t.direction.1 : ℝ)| ≤ N₁ ∧ |(t.direction.2 : ℝ)| ≤ N₂) :
    T.Finite := by
  obtain ⟨M₁, hM₁⟩ := exists_int_ge N₁
  obtain ⟨M₂, hM₂⟩ := exists_int_ge N₂
  have hdirs : (Cofactors.direction '' T).Finite := by
    apply ((Set.finite_Icc (a := -M₁) (b := M₁)).prod
      (Set.finite_Icc (a := -M₂) (b := M₂))).subset
    rintro n ⟨t, ht, rfl⟩
    have h₁ := abs_le.mp ((hbox t ht).1.trans hM₁)
    have h₂ := abs_le.mp ((hbox t ht).2.trans hM₂)
    exact ⟨⟨by exact_mod_cast h₁.1, by exact_mod_cast h₁.2⟩,
      ⟨by exact_mod_cast h₂.1, by exact_mod_cast h₂.2⟩⟩
  apply Set.Finite.of_finite_fibers Cofactors.direction hdirs
  rintro n ⟨t, ht, rfl⟩
  obtain ⟨h₁, h₂⟩ := hne t ht
  apply Set.Finite.of_injOn (f := factorPair) (t := ↑(t.direction.1.natAbs.divisors ×ˢ
    t.direction.2.natAbs.divisors)) _ _ (Finset.finite_toSet _)
  · rintro s ⟨_, hs⟩
    exact factorPair_mem (Set.mem_singleton_iff.mp hs) h₁ h₂
  · rintro s ⟨hs, hsn⟩ r ⟨_, hrn⟩ hsr
    exact eq_of_direction_eq_of_factorPair_eq (hpos s hs).1 (hpos s hs).2
      ((Set.mem_singleton_iff.mp hsn).trans (Set.mem_singleton_iff.mp hrn).symm) hsr

/-- In a centred box strictly thinner than the crossed lattice determinant,
there are at most two actual signed directions. The number of cofactor tuples
is bounded by the sum of the divisor products over exactly the occupied directions.
For the full set of eligible tuples, obtain `S` using `finite_of_bounded_directions`
and `Set.Finite.toFinset`. -/
public theorem card_directions_and_tuples_le {R : FixedRows} {S : Finset Cofactors}
    {f₁ f₂ : ℕ} {N₁ N₂ : ℝ} (hd : 0 < R.d) (hf₁ : 0 < f₁) (hf₂ : 0 < f₂)
    (hunits : IsCoprime (R.A * f₂) R.d ∧ IsCoprime (R.B * f₁) R.d)
    (hthin : 2 * N₁ * N₂ < (R.d : ℝ) * f₁ * f₂)
    (hrows : ∀ t ∈ S, RowConditions R t)
    (hfilter : ∀ t ∈ S, f₁ ∣ t.u₁ ∧ f₂ ∣ t.u₂)
    (hbox : ∀ t ∈ S, |(t.direction.1 : ℝ)| ≤ N₁ ∧ |(t.direction.2 : ℝ)| ≤ N₂) :
    (S.image Cofactors.direction).card ≤ 2 ∧
    S.card ≤ ∑ n ∈ S.image Cofactors.direction,
      n.1.natAbs.divisors.card * n.2.natAbs.divisors.card := by
  have hprop (n : ℤ × ℤ) (hn : n ∈ S.image Cofactors.direction) :
      (n.1 ≠ 0 ∧ n.2 ≠ 0 ∧ IsCoprime n.1 n.2 ∧ (R.A * n.1 ≡ R.B * n.2 [ZMOD R.d])) ∧
      ((f₂ : ℤ) ∣ n.1) ∧ ((f₁ : ℤ) ∣ n.2) := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ht₁, ht₂⟩ := hfilter t ht
    exact ⟨direction_properties (hrows t ht),
      (Int.natCast_dvd_natCast.mpr ht₂).mul_right _,
      (Int.natCast_dvd_natCast.mpr ht₁).mul_right _⟩
  have hrect (n : ℤ × ℤ) (hn : n ∈ S.image Cofactors.direction) :
      |(n.1 : ℝ)| ≤ N₁ ∧ |(n.2 : ℝ)| ≤ N₂ := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    exact hbox t ht
  constructor
  · apply card_le_two_of_primitive_collinear (fun n hn => (hprop n hn).1.2.2.1)
    intro x hx y hy
    obtain ⟨⟨_, _, _, hcx⟩, hfx₁, hfx₂⟩ := hprop x hx
    obtain ⟨⟨_, _, _, hcy⟩, hfy₁, hfy₂⟩ := hprop y hy
    have hm : 0 < R.d * (f₁ : ℤ) * (f₂ : ℤ) :=
      mul_pos (mul_pos hd (by exact_mod_cast hf₁)) (by exact_mod_cast hf₂)
    apply det_eq_zero_of_thin_box hm (by exact_mod_cast hthin) (hrect x hx) (hrect y hy)
    exact crossed_filter_dvd_det hunits.1 hcx hcy hfx₁ hfx₂ hfy₁ hfy₂
  · have hsum := Finset.sum_card_fiberwise_eq_card_filter S (S.image Cofactors.direction)
      Cofactors.direction
    rw [Finset.filter_true_of_mem (fun t ht => Finset.mem_image_of_mem _ ht)] at hsum
    rw [← hsum]
    apply Finset.sum_le_sum
    intro n hn
    exact card_direction_fiber_le (fun t ht => ⟨(hrows t ht).u₁_pos, (hrows t ht).u₂_pos⟩)
      (hprop n hn).1.1 (hprop n hn).1.2.1

end MaskedGapDirections
