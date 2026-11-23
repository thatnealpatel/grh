module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Radical.NatInt

/-!
# Prefix overlap ceiling

Source: `fea7eb0b:.godel/alice/prefix-overlap-review.md`, lines 3–9.
This is the rowwise arithmetic for `m = g * d * y`, with `d` the sorted prime
prefix and `y` the suffix. Only the split's ordering and the upper bound `X`
on prime factors of `d * y` enter the proof, not the algorithm for choosing the
longest prefix up to `Z`. The repeat factor is that of the **full** product
`n * m`, the exact natural quotient by the product of its distinct primes.
In the retained-residual application, `C` is the positive repeat coefficient
(`q^0.27` in the source), and `X` and `H` are real cutoffs without rounding.

If `D = gcd d y = 1`, no prime divides both `d` and `y`. The theorems below
concern `D > 1`: They claim no boundary prime or exclusion for `D = 1`,
and coprimality of `d` and `y` need not make the full product squarefree.
This is not a bound on `G₁`, which need not divide the prefix, nor a proof of
the source's asymptotic edge count.

Owning check session: `01a208d1-f4a1-7e74-9d68-6b0dfb6d9df9`.
-/

namespace PrefixOverlapCeiling

open UniqueFactorizationMonoid (radical radical_dvd_self squarefree_radical)

private theorem repeat_pos {M : ℕ} (hM : 0 < M) : 0 < M / radical M :=
  Nat.div_pos (Nat.le_of_dvd hM radical_dvd_self) (Nat.radical_pos M)

/-- At a prime dividing `M`, multiplying the repeat factor by that prime restores
exactly the one copy removed by the radical. -/
private theorem pow_dvd_mul_repeat {p k M : ℕ} (hp : p.Prime) (hM : 0 < M)
    (hpM : p ∣ M) (hk : p ^ k ∣ M) : p ^ k ∣ p * (M / radical M) := by
  have hpr : p ∣ radical M := by
    have hp' : p ∈ (radical M).primeFactors := by
      rw [Nat.primeFactors_radical]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpM, hM.ne'⟩
    exact (Nat.mem_primeFactors.mp hp').2.1
  have hrad : (radical M).factorization p = 1 :=
    Nat.factorization_eq_one_of_squarefree squarefree_radical hp hpr
  have hk' := (hp.pow_dvd_iff_le_factorization hM.ne').mp hk
  apply (hp.pow_dvd_iff_le_factorization
    (mul_ne_zero hp.ne_zero (repeat_pos hM).ne')).mpr
  rw [Nat.factorization_mul hp.ne_zero (repeat_pos hM).ne', Finsupp.add_apply,
    hp.factorization_self, Nat.factorization_div radical_dvd_self, Finsupp.tsub_apply, hrad]
  omega

/-- A nontrivial overlap is a power of the largest prime of the prefix, which is
also the smallest prime of the suffix. Its square is at most that prime times
the joint repeat factor. -/
public theorem exists_boundary_prime_power_and_sq_le {g n d y : ℕ} {X : ℝ}
    (hg : 0 < g) (hn : 0 < n) (hd : 0 < d) (hy : 0 < y)
    (horder : ∀ p ∈ d.primeFactors, ∀ r ∈ y.primeFactors, p ≤ r)
    (hX : ∀ p ∈ (d * y).primeFactors, (p : ℝ) ≤ X)
    (hD : 1 < d.gcd y) :
    ∃ p j : ℕ, p.Prime ∧ 0 < j ∧ d.gcd y = p ^ j ∧ (p : ℝ) ≤ X ∧
      (∀ r ∈ d.primeFactors, r ≤ p) ∧ (∀ r ∈ y.primeFactors, p ≤ r) ∧
      (d.gcd y) ^ 2 ≤ p * ((n * g * d * y) / radical (n * g * d * y)) := by
  obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd (ne_of_gt hD)
  have hD0 : d.gcd y ≠ 0 := (Nat.zero_lt_one.trans hD).ne'
  have hpd : p ∈ d.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpD.trans (Nat.gcd_dvd_left d y), hd.ne'⟩
  have hpy : p ∈ y.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpD.trans (Nat.gcd_dvd_right d y), hy.ne'⟩
  have hmax : ∀ r ∈ d.primeFactors, r ≤ p := fun r hr ↦ horder r hr p hpy
  have hmin : ∀ r ∈ y.primeFactors, p ≤ r := horder p hpd
  have hfac : (d.gcd y).factorization = Finsupp.single p ((d.gcd y).factorization p) := by
    ext r
    by_cases hr : r = p
    · subst r
      simp
    · rw [Finsupp.single_eq_of_ne hr]
      by_contra! hne
      have hrD : r ∈ (d.gcd y).primeFactors := by
        rwa [← Nat.support_factorization, Finsupp.mem_support_iff]
      obtain ⟨hrprime, hrdvd, _⟩ := Nat.mem_primeFactors.mp hrD
      have hrd := Nat.mem_primeFactors.mpr ⟨hrprime, hrdvd.trans (Nat.gcd_dvd_left d y), hd.ne'⟩
      have hry := Nat.mem_primeFactors.mpr ⟨hrprime, hrdvd.trans (Nat.gcd_dvd_right d y), hy.ne'⟩
      exact hr (le_antisymm (hmax r hrd) (hmin r hry))
  let j := (d.gcd y).factorization p
  have hDj : d.gcd y = p ^ j := Nat.eq_pow_of_factorization_eq_single hD0 hfac
  have hpdy : p ∣ d * y := (Nat.mem_primeFactors.mp hpd).2.1.trans (dvd_mul_right d y)
  have hpX := hX p (Nat.mem_primeFactors.mpr ⟨hp, hpdy, mul_ne_zero hd.ne' hy.ne'⟩)
  refine ⟨p, j, hp, hp.factorization_pos_of_dvd hD0 hpD, hDj, hpX, hmax, hmin, ?_⟩
  let M := n * g * d * y
  have hM : 0 < M := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hn hg) hd) hy
  have hdyM : d * y ∣ M := by
    simpa only [M, mul_assoc] using dvd_mul_left (d * y) (n * g)
  have hsq : (d.gcd y) ^ 2 ∣ M := by
    rw [pow_two]
    exact (mul_dvd_mul (Nat.gcd_dvd_left d y) (Nat.gcd_dvd_right d y)).trans hdyM
  change (d.gcd y) ^ 2 ≤ p * (M / radical M)
  rw [hDj, ← pow_mul] at hsq ⊢
  exact Nat.le_of_dvd (Nat.mul_pos hp.pos (repeat_pos hM))
    (pow_dvd_mul_repeat hp hM (hpdy.trans hdyM) hsq)

/-- On the retained residual, a nontrivial overlap cannot satisfy `C * D² ≥ X * H`.
The strict inequality comes from the strict repeat cutoff. -/
public theorem scaled_sq_lt_of_retained_repeat {g n d y : ℕ} {X C H : ℝ}
    (hg : 0 < g) (hn : 0 < n) (hd : 0 < d) (hy : 0 < y)
    (horder : ∀ p ∈ d.primeFactors, ∀ r ∈ y.primeFactors, p ≤ r)
    (hX : ∀ p ∈ (d * y).primeFactors, (p : ℝ) ≤ X)
    (hD : 1 < d.gcd y) (hC : 0 < C)
    (hretained : C * (((n * g * d * y) / radical (n * g * d * y) : ℕ) : ℝ) < H) :
    C * (d.gcd y : ℝ) ^ 2 < X * H := by
  obtain ⟨p, _, hp, _, _, hpX, _, _, hsq⟩ :=
    exists_boundary_prime_power_and_sq_le hg hn hd hy horder hX hD
  let e : ℝ := (((n * g * d * y) / radical (n * g * d * y) : ℕ) : ℝ)
  have he : 0 ≤ e := Nat.cast_nonneg _
  have hsq' : (d.gcd y : ℝ) ^ 2 ≤ (p : ℝ) * e := by
    simpa only [e, Nat.cast_pow, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hsq
  have hXpos : 0 < X := (Nat.cast_pos.mpr hp.pos).trans_le hpX
  calc
    C * (d.gcd y : ℝ) ^ 2 ≤ C * ((p : ℝ) * e) := mul_le_mul_of_nonneg_left hsq' hC.le
    _ ≤ C * (X * e) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpX he) hC.le
    _ = X * (C * e) := mul_left_comm _ _ _
    _ < X * H := mul_lt_mul_of_pos_left hretained hXpos

end PrefixOverlapCeiling
