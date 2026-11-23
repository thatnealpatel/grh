module

public import Lemmas.CrossedGapRadical
public import Lemmas.MaskedGapDirections
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Occupied crossed-gap directions

Source: `b6920957:.godel/alice/crossed-gap-filters.md:13–30`, steps 1–3,
and the direction-count input to the box price immediately following
(discovery route 2 at `dcc11ec5`).

For fixed `d`, `F₁`, `F₂` and box parameters `X`, `K`, `V`, count distinct
signed, primitive occupied directions, not the row witnesses producing them.
The dyadic estimates enter as the determinant bound and the selection guards.
For each direction the source supplies `M`, the full eligible part of
`|n₁ n₂|`, and `A = ℓ₁ℓ₂ ∣ M`, which is used only for availability.
The admissible splits are ordered by coordinate; divisibility is on the
coordinates themselves, not on the cofactors. The repeat credit limits the
radical of the final product. At `V ≤ 1` the only filter is `(1, 1)`, with no
upper product or radical bound. This is the finite cover and multiplicity
bound, not the smooth-radical enumeration, scalar recovery, or the final
asymptotic box price.

Owning check session: `01a20a16-7036-75bb-8ab9-3bc3a536b6e9`.
-/

namespace CrossedDirectionCover

open UniqueFactorizationMonoid

/-- The full eligible part of `N` contains exactly its eligible-smooth divisors. -/
@[expose] public def IsEligiblePart (eligible : ℕ → Prop) (N M : ℕ) : Prop :=
  ∀ a : ℕ, a ∣ M ↔ a ∣ N ∧ ∀ p : ℕ, p.Prime → p ∣ a → eligible p

/-- Enumerate the admissible ordered divisor pairs without using occupancy.
The positive factors are coprime, as required by a primitive direction. -/
public noncomputable def admissibleSplits (eligible : ℕ → Prop) (X K V : ℝ) :
    Finset (ℕ × ℕ) := by
  classical
  let I := Finset.Icc 1 ⌊X * V⌋₊
  exact if 1 < V then
    (I ×ˢ I).filter fun b =>
      b.1.Coprime b.2 ∧ V ≤ ((b.1 * b.2 : ℕ) : ℝ) ∧ ((b.1 * b.2 : ℕ) : ℝ) ≤ X * V ∧
      ((radical (b.1 * b.2) : ℕ) : ℝ) ≤ X * V / K ∧
      ∀ p : ℕ, p.Prime → p ∣ b.1 * b.2 → eligible p ∧ (p : ℝ) ≤ X
  else {(1, 1)}

/-- The finite search bounds on the two factors impose no further restriction:
positivity and the upper product bound already put both in the search interval. -/
public theorem mem_admissibleSplits {eligible : ℕ → Prop} {X K V : ℝ} {b : ℕ × ℕ}
    (hX : 1 < X) : b ∈ admissibleSplits eligible X K V ↔
    if 1 < V then
      0 < b.1 ∧ 0 < b.2 ∧ b.1.Coprime b.2 ∧ V ≤ ((b.1 * b.2 : ℕ) : ℝ) ∧
      ((b.1 * b.2 : ℕ) : ℝ) ≤ X * V ∧ ((radical (b.1 * b.2) : ℕ) : ℝ) ≤ X * V / K ∧
      ∀ p : ℕ, p.Prime → p ∣ b.1 * b.2 → eligible p ∧ (p : ℝ) ≤ X
    else b = (1, 1) := by
  classical
  by_cases hV : 1 < V
  · simp only [admissibleSplits, hV, ite_true, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, hb⟩
      exact ⟨h₁.1, h₂.1, hb⟩
    · rintro ⟨h₁, h₂, hb⟩
      have hcap : 0 ≤ X * V := mul_nonneg (zero_lt_one.trans hX).le (zero_lt_one.trans hV).le
      have hf := (Nat.le_floor_iff hcap).mpr hb.2.2.1
      exact ⟨⟨⟨h₁, (Nat.le_mul_of_pos_right _ h₂).trans hf⟩,
        ⟨h₂, (Nat.le_mul_of_pos_left _ h₁).trans hf⟩⟩, hb⟩
  · simp only [admissibleSplits, hV, ite_false, Finset.mem_singleton]

/-- A finite set of occupied signed directions has cardinality at most twice the
number of admissible ordered splits. Select a divisor separately for each
occupied direction, then count the coordinate-divisibility classes in the
same box. The modulus for a class is `d * m₁ * m₂`, which beats the box's
determinant bound in both branches of `V`. -/
public theorem card_le_twice_admissibleSplits {eligible : ℕ → Prop} {X K V : ℝ}
    {d F₁ F₂ : ℤ} {S : Finset (ℤ × ℤ)} (hd : 0 < d) (hX : 1 < X) (hK : 1 ≤ K)
    (hcoeff : IsCoprime F₁ d ∧ IsCoprime F₂ d)
    (hrows : ∀ n ∈ S, n.1 ≠ 0 ∧ n.2 ≠ 0 ∧ IsCoprime n.1 n.2 ∧
      IsCoprime n.1 d ∧ IsCoprime n.2 d ∧ (F₂ * n.1 ≡ F₁ * n.2 [ZMOD d]))
    (hdet : ∀ x ∈ S, ∀ y ∈ S,
      |((x.1 * y.2 - y.1 * x.2 : ℤ) : ℝ)| ≤ (d : ℝ) * V / 2)
    (hdata : ∀ n ∈ S, ∃ M A : ℕ, IsEligiblePart eligible (n.1 * n.2).natAbs M ∧
      (∀ p : ℕ, p.Prime → p ∣ M → (p : ℝ) ≤ X) ∧
      K ≤ ((M / radical M : ℕ) : ℝ) ∧ A ∣ M ∧ (1 < V → V ≤ (A : ℝ)))
    (hseed : 1 < K → X ^ 2 * K ^ 2 ≤ V) :
    S.card ≤ 2 * (admissibleSplits eligible X K V).card := by
  classical
  let splits := admissibleSplits eligible X K V
  let fiber (b : ℕ × ℕ) := S.filter fun n => (b.1 : ℤ) ∣ n.1 ∧ (b.2 : ℤ) ∣ n.2
  have hcover : S ⊆ splits.biUnion fiber := by
    intro n hn
    obtain ⟨hn₁, hn₂, hprim, _, _, _⟩ := hrows n hn
    obtain ⟨M, A, hfull, hcap, hcredit, hAM, havailable⟩ := hdata n hn
    have hNpos : 0 < (n.1 * n.2).natAbs :=
      Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (mul_ne_zero hn₁ hn₂))
    have hMpos := Nat.pos_of_dvd_of_pos ((hfull M).mp dvd_rfl).1 hNpos
    obtain ⟨m, hmM, _, hsmall, hlarge⟩ :=
      CrossedGapRadical.exists_combined_divisor hMpos hcap hK hcredit hAM havailable hseed
    obtain ⟨hmN, hmEligible⟩ := (hfull m).mp hmM
    obtain ⟨m₁, m₂, hprod, h₁, h₂, hcop⟩ :=
      CrossedGapRadical.split_primitive_divisor hprim hmN
    apply Finset.mem_biUnion.mpr
    refine ⟨(m₁, m₂), (mem_admissibleSplits hX).mpr ?_, Finset.mem_filter.mpr ⟨hn, h₁, h₂⟩⟩
    by_cases hV : 1 < V
    · rw [ite_eq_left hV]
      have hpos : 0 < m₁ * m₂ := by
        rw [hprod]
        exact Nat.pos_of_dvd_of_pos hmM hMpos
      refine ⟨Nat.pos_of_mul_pos_right hpos, Nat.pos_of_mul_pos_left hpos, hcop, ?_⟩
      change V ≤ ((m₁ * m₂ : ℕ) : ℝ) ∧ ((m₁ * m₂ : ℕ) : ℝ) ≤ X * V ∧
        ((radical (m₁ * m₂) : ℕ) : ℝ) ≤ X * V / K ∧ _
      rw [hprod]
      obtain ⟨hVm, hmXV, hmrad⟩ := hlarge hV
      exact ⟨hVm, hmXV, hmrad, fun p hp hpdiv => ⟨hmEligible p hp hpdiv,
        hcap p hp (hpdiv.trans hmM)⟩⟩
    · rw [ite_eq_right hV]
      obtain ⟨e₁, e₂⟩ := mul_eq_one.mp (hprod.trans (hsmall (le_of_not_gt hV)).2)
      exact Prod.ext e₁ e₂
  have hcard (b : ℕ × ℕ) (hb : b ∈ splits) : (fiber b).card ≤ 2 := by
    have hb' := (mem_admissibleSplits hX).mp hb
    have hthreshold : V / 2 < ((b.1 * b.2 : ℕ) : ℝ) := by
      by_cases hV : 1 < V
      · rw [ite_eq_left hV] at hb'
        exact (half_lt_self (zero_lt_one.trans hV)).trans_le hb'.2.2.2.1
      · rw [ite_eq_right hV] at hb'
        rw [hb']
        change V / 2 < ((1 * 1 : ℕ) : ℝ)
        simp only [mul_one, Nat.cast_one]
        exact (div_le_div_of_nonneg_right (le_of_not_gt hV) zero_le_two).trans_lt
          (half_lt_self zero_lt_one)
    apply MaskedGapDirections.card_le_two_of_primitive_collinear
    · intro x hx
      exact (hrows x (Finset.mem_filter.mp hx).1).2.2.1
    · intro x hx y hy
      obtain ⟨hxS, hx₁, hx₂⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyS, hy₁, hy₂⟩ := Finset.mem_filter.mp hy
      obtain ⟨_, _, _, hxunit, _, hxc⟩ := hrows x hxS
      obtain ⟨_, _, _, _, _, hyc⟩ := hrows y hyS
      have hunit := hcoeff.2.mul_left (hxunit.of_isCoprime_of_dvd_left hx₁)
      -- In the determinant lemma `f₂` is the divisor of coordinate 1.
      have hdiv := MaskedGapDirections.crossed_filter_dvd_det hunit hxc hyc hx₁ hx₂ hy₁ hy₂
      rw [mul_right_comm d (b.2 : ℤ) (b.1 : ℤ)] at hdiv
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hlt : |((x.1 * y.2 - y.1 * x.2 : ℤ) : ℝ)| <
          ((d * (b.1 : ℤ) * (b.2 : ℤ) : ℤ) : ℝ) := by
        calc
          _ ≤ (d : ℝ) * V / 2 := hdet x hxS y hyS
          _ = (d : ℝ) * (V / 2) := mul_div_assoc ..
          _ < (d : ℝ) * ((b.1 * b.2 : ℕ) : ℝ) := mul_lt_mul_of_pos_left hthreshold hdR
          _ = _ := by rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
            Nat.cast_mul, mul_assoc]
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
      exact_mod_cast (show ((x.1 * y.2 - y.1 * x.2).natAbs : ℝ) <
        ((d * (b.1 : ℤ) * (b.2 : ℤ)).natAbs : ℝ) by
          simpa only [Nat.cast_natAbs, Int.cast_abs] using hlt.trans_le (le_abs_self _))
  calc
    S.card ≤ (splits.biUnion fiber).card := Finset.card_le_card hcover
    _ ≤ ∑ b ∈ splits, (fiber b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ splits, 2 := Finset.sum_le_sum hcard
    _ = 2 * splits.card := by simp [mul_comm]

end CrossedDirectionCover
