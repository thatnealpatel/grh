module

public import Mathlib.Data.Int.ModEq

/-!
# Crossed primitive splits for bounded CRT candidates

Source: `b6920957:.godel/alice/crossed-gap-filters.md:32–50`, specifically the
split in line 38 and the redundancy of the output test in lines 44–48.

For positive `T`, the gcd-product test recovers the factors `h₂` and `k`
of `T`, in that order. The factors may share primes. The inputs and cofactor
witnesses are signed integers, and zero inputs are allowed. For already
integral forced outputs, only the stated row congruences modulo `T` and
coprimality of `T` with `q * d` are needed to preserve the individual gcds,
even on rejected candidates. This does not assert integrality of the
quotients, full row primitivity, smoothness, or an occupation estimate.

Owning check session: `01a209f7-85a2-71df-a0cc-7987e51e67d1`.
-/

namespace CrossedPrimitiveSplit

/-- A split with `h₂` dividing the first input and `k` dividing the second.
Each signed cofactor is coprime to the *other* factor. When `T > 0`, the
product condition forces both factors to be positive. -/
public def IsSplit (T : ℕ) (u₁ u₂ : ℤ) (h₂ k : ℕ) : Prop :=
  T = h₂ * k ∧
    (∃ δ₁ : ℤ, u₁ = (h₂ : ℤ) * δ₁ ∧ k.Coprime δ₁.natAbs) ∧
    (∃ δ₂ : ℤ, u₂ = (k : ℤ) * δ₂ ∧ h₂.Coprime δ₂.natAbs)

/-- The candidate admits a crossed primitive split. -/
public def Passes (T : ℕ) (u₁ u₂ : ℤ) : Prop :=
  ∃ h₂ k : ℕ, IsSplit T u₁ u₂ h₂ k

private theorem gcd_mul_eq_factor_iff {h k : ℕ} {u : ℤ} (hh : 0 < h) :
    (h * k).gcd u.natAbs = h ↔ ∃ δ : ℤ, u = (h : ℤ) * δ ∧ k.Coprime δ.natAbs := by
  have scale {δ : ℤ} (hu : u = (h : ℤ) * δ) :
      (h * k).gcd u.natAbs = h * k.gcd δ.natAbs := by
    rw [hu, Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_mul_left]
  constructor
  · intro hg
    have hdvd : h ∣ u.natAbs := hg ▸ Nat.gcd_dvd_right (h * k) u.natAbs
    obtain ⟨δ, hδ⟩ := Int.natCast_dvd.mpr hdvd
    exact ⟨δ, hδ, Nat.eq_of_mul_eq_mul_left hh
      ((scale hδ).symm.trans (hg.trans (Nat.mul_one h).symm))⟩
  · rintro ⟨δ, hδ, hcop⟩
    rw [scale hδ, hcop.gcd_eq_one, Nat.mul_one]

/-- For positive `T`, a proposed factor pair is a primitive split exactly when
it has product `T` and both factors are the designated gcds. -/
public theorem isSplit_iff {T h₂ k : ℕ} {u₁ u₂ : ℤ} (hT : 0 < T) :
    IsSplit T u₁ u₂ h₂ k ↔
      T = h₂ * k ∧ h₂ = T.gcd u₁.natAbs ∧ k = T.gcd u₂.natAbs := by
  unfold IsSplit
  refine and_congr_right fun hprod ↦ ?_
  have hpos : 0 < h₂ * k := hprod ▸ hT
  rw [hprod, eq_comm (a := h₂), eq_comm (a := k)]
  refine and_congr (gcd_mul_eq_factor_iff (Nat.pos_of_mul_pos_right hpos)).symm ?_
  rw [Nat.mul_comm h₂ k]
  exact (gcd_mul_eq_factor_iff (Nat.pos_of_mul_pos_left hpos)).symm

/-- The primitive split predicate is exactly the product-of-gcds test. -/
public theorem passes_iff_gcd_mul_eq {T : ℕ} {u₁ u₂ : ℤ} (hT : 0 < T) :
    Passes T u₁ u₂ ↔ T.gcd u₁.natAbs * T.gcd u₂.natAbs = T := by
  constructor
  · rintro ⟨h₂, k, hs⟩
    obtain ⟨hprod, rfl, rfl⟩ := (isSplit_iff hT).1 hs
    exact hprod.symm
  · intro hprod
    exact ⟨T.gcd u₁.natAbs, T.gcd u₂.natAbs, (isSplit_iff hT).2 ⟨hprod.symm, rfl, rfl⟩⟩

/-- A passing candidate has a unique ordered factor pair, given by the two gcds. -/
public theorem existsUnique_isSplit {T : ℕ} {u₁ u₂ : ℤ} (hT : 0 < T)
    (hprod : T.gcd u₁.natAbs * T.gcd u₂.natAbs = T) :
    ∃! p : ℕ × ℕ, IsSplit T u₁ u₂ p.1 p.2 := by
  refine ⟨(T.gcd u₁.natAbs, T.gcd u₂.natAbs), (isSplit_iff hT).2 ⟨hprod.symm, rfl, rfl⟩, ?_⟩
  intro p hp
  obtain ⟨_, h₁, h₂⟩ := (isSplit_iff hT).1 hp
  exact Prod.ext h₁ h₂

private theorem gcd_natAbs_eq_of_modEq {T : ℕ} {a b : ℤ}
    (h : a ≡ b [ZMOD (T : ℤ)]) : T.gcd a.natAbs = T.gcd b.natAbs := by
  -- A common divisor of `T` and `a` divides `b`, and conversely.
  have gcd_dvd {x y : ℤ} (hxy : x ≡ y [ZMOD (T : ℤ)]) :
      (T : ℤ).gcd x ∣ (T : ℤ).gcd y :=
    Int.dvd_gcd (Int.gcd_dvd_left _ _)
      ((hxy.of_dvd (Int.gcd_dvd_left _ _)).dvd_iff.mp (Int.gcd_dvd_right _ _))
  simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] using
    Nat.dvd_antisymm (gcd_dvd h) (gcd_dvd h.symm)

/-- The output congruence preserves the coordinate gcd without any split
hypothesis: both `d` and `q` are units modulo `T`. -/
public theorem gcd_eq_of_output_congruence {T q d : ℕ} {u w : ℤ}
    (hcop : T.Coprime (q * d)) (h : (d : ℤ) * w ≡ -(q : ℤ) * u [ZMOD (T : ℤ)]) :
    T.gcd w.natAbs = T.gcd u.natAbs := by
  obtain ⟨hq, hd⟩ := Nat.coprime_mul_iff_right.mp hcop
  have hg := gcd_natAbs_eq_of_modEq h
  simpa only [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast,
    hq.symm.gcd_mul_left_cancel_right, hd.symm.gcd_mul_left_cancel_right] using hg

/-- The forced outputs preserve both gcds and the truth or falsity of the
primitive split predicate. No acceptance hypothesis is needed. -/
public theorem forced_output_invariant {T q d : ℕ} {u₁ u₂ w₁ w₂ : ℤ} (hT : 0 < T)
    (hcop : T.Coprime (q * d))
    (hw₁ : (d : ℤ) * w₁ ≡ -(q : ℤ) * u₁ [ZMOD (T : ℤ)])
    (hw₂ : (d : ℤ) * w₂ ≡ -(q : ℤ) * u₂ [ZMOD (T : ℤ)]) :
    T.gcd w₁.natAbs = T.gcd u₁.natAbs ∧ T.gcd w₂.natAbs = T.gcd u₂.natAbs ∧
      (Passes T w₁ w₂ ↔ Passes T u₁ u₂) := by
  have h₁ := gcd_eq_of_output_congruence hcop hw₁
  have h₂ := gcd_eq_of_output_congruence hcop hw₂
  refine ⟨h₁, h₂, ?_⟩
  rw [passes_iff_gcd_mul_eq hT (u₁ := w₁), passes_iff_gcd_mul_eq hT (u₁ := u₁), h₁, h₂]

end CrossedPrimitiveSplit
