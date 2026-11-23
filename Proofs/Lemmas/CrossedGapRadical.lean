module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Find

/-!
# Crossed-gap divisor selection with repeat credit

Source: `b6920957:.godel/alice/crossed-gap-filters.md:13–24`, unchanged at `011d4c8f`.
We prove the finite selection step: `M` is the full eligible part of the product
of the absolute primitive coordinates; the cofactor product `A ∣ M` supplies
availability, but the repeat credit `M / radical M` comes from the full `M`.
All repeat quotients are exact natural divisions, cast to `ℝ` for the bounds.
For `1 < V` the final divisor lies in `[V, X * V]` and its radical is at most
`X * V / K`. For `V ≤ 1` the hypotheses force `K = 1` and the divisor is `1`;
the bounds `X * V` and `X * V / K` do not apply in that branch. The signed-coordinate
split allows divisors supported on the gap as well as on the cofactors. This
module does not prove the dyadic estimates, determinant count, or enumeration.

Owning check session: `01a209f7-85a2-71df-a0cc-7987e51e67d1`.
-/

namespace CrossedGapRadical

open UniqueFactorizationMonoid

private theorem one_le_cap {L : ℕ} {X : ℝ} (hL : 1 < (L : ℝ))
    (hcap : ∀ p : ℕ, p.Prime → p ∣ L → (p : ℝ) ≤ X) : 1 ≤ X := by
  have hL' : 1 < L := by exact_mod_cast hL
  obtain ⟨p, hp, hpL⟩ := Nat.exists_prime_and_dvd hL'.ne'
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  exact hp'.trans (hcap p hp hpL)

/-- Take the least divisor of `L` that is a multiple of `s` and reaches `T`.
If it is not `s` itself, removing one prime from its quotient by `s` drops below `T`. -/
private theorem exists_crossing {s L : ℕ} {T X : ℝ} (hsL : s ∣ L)
    (hsT : (s : ℝ) ≤ T) (hT : 1 < T) (hTL : T ≤ (L : ℝ))
    (hcap : ∀ p : ℕ, p.Prime → p ∣ L → (p : ℝ) ≤ X) :
    ∃ m : ℕ, s ∣ m ∧ m ∣ L ∧ T ≤ (m : ℝ) ∧ (m : ℝ) ≤ X * T := by
  classical
  have hex : ∃ m : ℕ, s ∣ m ∧ m ∣ L ∧ T ≤ (m : ℝ) := ⟨L, hsL, dvd_rfl, hTL⟩
  let m := Nat.find hex
  have hm : s ∣ m ∧ m ∣ L ∧ T ≤ (m : ℝ) := Nat.find_spec hex
  refine ⟨m, hm.1, hm.2.1, hm.2.2, ?_⟩
  have hTpos := zero_lt_one.trans hT
  obtain ⟨r, hr⟩ := hm.1
  by_cases hr1 : r = 1
  · have hX := one_le_cap (hT.trans_le hTL) hcap
    have hmle : (m : ℝ) ≤ T := by simpa only [hr, hr1, mul_one] using hsT
    exact hmle.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hX hTpos.le)
  · obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd hr1
    have hfac : m = s * k * p := by rw [hr, hk, mul_comm p k, mul_assoc]
    have hpart : s * k ∣ L := (show s * k ∣ m from ⟨p, hfac⟩).trans hm.2.1
    have hpL : p ∣ L := by
      apply dvd_trans _ hm.2.1
      rw [hfac]
      exact dvd_mul_left _ _
    have hmpos : 0 < m := by exact_mod_cast hTpos.trans_le hm.2.2
    have hkpos : 0 < s * k := by
      rw [hfac] at hmpos
      exact Nat.pos_of_ne_zero (left_ne_zero_of_mul hmpos.ne')
    have hlt : s * k < m := by
      rw [hfac]
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt hkpos
    have hbelow : ((s * k : ℕ) : ℝ) < T :=
      lt_of_not_ge fun h => Nat.find_min hex hlt ⟨dvd_mul_right s k, hpart, h⟩
    calc
      (m : ℝ) = ((s * k : ℕ) : ℝ) * (p : ℝ) := by rw [hfac, Nat.cast_mul]
      _ ≤ T * (p : ℝ) := mul_le_mul_of_nonneg_right hbelow.le (Nat.cast_nonneg p)
      _ = (p : ℝ) * T := mul_comm _ _
      _ ≤ X * T := mul_le_mul_of_nonneg_right (hcap p hp hpL) hTpos.le

/-- Add just one copy of each prime of `w`, using the radical of `M` for those copies. -/
private theorem repeat_seed {w M : ℕ} (hM : 0 < M) (hw : w ∣ M / radical M) :
    w * radical w ∣ M ∧ (w * radical w) / radical (w * radical w) = w := by
  have hC : M / radical M * radical M = M := Nat.div_mul_cancel radical_dvd_self
  have hwM : w ∣ M := hw.trans ((dvd_mul_right _ _).trans (dvd_of_eq hC))
  have hrad : radical w ∣ radical M := radical_dvd_radical hwM hM.ne'
  refine ⟨hC ▸ Nat.mul_dvd_mul hw hrad, ?_⟩
  rw [mul_comm w, radical_mul_of_dvd radical_dvd_self]
  exact Nat.div_eq_of_eq_mul_right (Nat.radical_pos _) rfl

private theorem repeat_credit_dvd {s m : ℕ} (hsm : s ∣ m) :
    s / radical s ∣ m / radical m := by
  obtain ⟨t, rfl⟩ := hsm
  rw [Nat.dvd_div_iff_mul_dvd radical_dvd_self, mul_comm (radical (s * t))]
  calc
    s / radical s * radical (s * t) ∣ s / radical s * (radical s * t) :=
      Nat.mul_dvd_mul_left _ (radical_mul_dvd.trans (Nat.mul_dvd_mul_left _ radical_dvd_self))
    _ = s * t := by rw [← mul_assoc, Nat.div_mul_cancel radical_dvd_self]

/-- Select the final smooth divisor of `M`. Availability is needed only when
`1 < V`, and the nonunit seed bound is needed only when `1 < K`. -/
public theorem exists_combined_divisor {M A : ℕ} {X K V : ℝ} (hM : 0 < M)
    (hcap : ∀ p : ℕ, p.Prime → p ∣ M → (p : ℝ) ≤ X)
    (hK : 1 ≤ K) (hcredit : K ≤ ((M / radical M : ℕ) : ℝ)) (hAM : A ∣ M)
    (havailable : 1 < V → V ≤ (A : ℝ)) (hseed : 1 < K → X ^ 2 * K ^ 2 ≤ V) :
    ∃ m : ℕ, m ∣ M ∧ K ≤ ((m / radical m : ℕ) : ℝ) ∧
      (V ≤ 1 → K = 1 ∧ m = 1) ∧
      (1 < V → V ≤ (m : ℝ) ∧ (m : ℝ) ≤ X * V ∧ ((radical m : ℕ) : ℝ) ≤ X * V / K) := by
  have hCcap (p : ℕ) (hp : p.Prime) (hpC : p ∣ M / radical M) : (p : ℝ) ≤ X := by
    have hC : M / radical M ∣ M := ⟨radical M, (Nat.div_mul_cancel radical_dvd_self).symm⟩
    exact hcap p hp (hpC.trans hC)
  rcases le_or_gt V 1 with hV | hV
  · have hK' : K = 1 := by
      apply le_antisymm _ hK
      by_contra! hKgt
      have hX := one_le_cap (hKgt.trans_le hcredit) hCcap
      have hXsq : 1 ≤ X ^ 2 := one_le_pow₀ hX
      have hKsq : 1 < K ^ 2 := one_lt_pow₀ hKgt (by decide)
      have hle : K ^ 2 ≤ X ^ 2 * K ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hXsq (sq_nonneg K)
      exact (hKsq.trans_le (hle.trans ((hseed hKgt).trans hV))).false
    exact ⟨1, one_dvd M, by simp [hK'], fun _ => ⟨hK', rfl⟩,
      fun hv => (hv.not_ge hV).elim⟩
  have hex : ∃ s : ℕ, s ∣ M ∧ (s : ℝ) ≤ V ∧ K ≤ ((s / radical s : ℕ) : ℝ) := by
    rcases hK.eq_or_lt with hK' | hKgt
    · exact ⟨1, one_dvd M, by exact_mod_cast hV.le, by simp [← hK']⟩
    · obtain ⟨w, _, hwC, hKw, hwX⟩ :=
        exists_crossing (one_dvd (M / radical M)) (by exact_mod_cast hK) hKgt hcredit hCcap
      obtain ⟨hsM, hscredit⟩ := repeat_seed hM hwC
      have hwpos : 0 < w := by exact_mod_cast (zero_lt_one.trans hKgt).trans_le hKw
      have hradw : ((radical w : ℕ) : ℝ) ≤ (w : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hwpos (radical_dvd_self (a := w))
      have hsq : ((w : ℝ) * w) ≤ X ^ 2 * K ^ 2 := by
        rw [← mul_pow, pow_two]
        exact mul_le_mul hwX hwX (Nat.cast_nonneg w) ((Nat.cast_nonneg w).trans hwX)
      refine ⟨w * radical w, hsM, ?_, by rwa [hscredit]⟩
      rw [Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left hradw (Nat.cast_nonneg w)).trans
        (hsq.trans (hseed hKgt))
  obtain ⟨s, hsM, hsV, hscredit⟩ := hex
  -- The lcm combines the two supplies without adding shared powers twice.
  -- It stays inside the ambient `M`.
  have hLM : s.lcm A ∣ M := Nat.lcm_dvd hsM hAM
  have hVL : V ≤ (s.lcm A : ℝ) := (havailable hV).trans (by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hLM hM) (Nat.dvd_lcm_right s A))
  obtain ⟨m, hsm, hmL, hVm, hmXV⟩ := exists_crossing (Nat.dvd_lcm_left s A) hsV hV hVL
    (fun p hp hpL => hcap p hp (hpL.trans hLM))
  have hmM := hmL.trans hLM
  have hmpos := Nat.pos_of_dvd_of_pos hmM hM
  have hmcredit_pos : 0 < m / radical m :=
    Nat.pos_of_dvd_of_pos ⟨radical m, (Nat.div_mul_cancel radical_dvd_self).symm⟩ hmpos
  have hmcredit : K ≤ ((m / radical m : ℕ) : ℝ) := hscredit.trans (by
    exact_mod_cast Nat.le_of_dvd hmcredit_pos (repeat_credit_dvd hsm))
  have hmul : ((m / radical m : ℕ) : ℝ) * ((radical m : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel (radical_dvd_self (a := m))
  refine ⟨m, hmM, hmcredit, fun hv => (hV.not_ge hv).elim, fun _ => ⟨hVm, hmXV, ?_⟩⟩
  apply (le_div_iff₀ (zero_lt_one.trans_le hK)).2
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_right hmcredit (Nat.cast_nonneg (radical m))).trans
    (hmul.trans_le hmXV)

/-- A divisor selected from the full eligible part splits over the signed primitive
coordinates, not necessarily over their cofactors. The split factors are coprime. -/
public theorem split_primitive_divisor {m : ℕ} {n₁ n₂ : ℤ} (hprim : IsCoprime n₁ n₂)
    (hm : m ∣ (n₁ * n₂).natAbs) :
    ∃ m₁ m₂ : ℕ, m₁ * m₂ = m ∧ (m₁ : ℤ) ∣ n₁ ∧ (m₂ : ℤ) ∣ n₂ ∧ m₁.Coprime m₂ := by
  have hcop : n₁.natAbs.Coprime n₂.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hprim
  rw [Int.natAbs_mul] at hm
  have h₁ := Nat.gcd_dvd_right m n₁.natAbs
  have h₂ := Nat.gcd_dvd_right m n₂.natAbs
  refine ⟨_, _, ?_, Int.natCast_dvd.mpr h₁, Int.natCast_dvd.mpr h₂, hcop.of_dvd h₁ h₂⟩
  rw [← hcop.gcd_mul m, Nat.gcd_eq_left hm]

end CrossedGapRadical
