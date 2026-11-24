module

public import Lemmas.AdaptivePlaneBin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

/-!
# The smooth-number price of one adaptive plane bin

Source: `.godel/alice/shared-complement-count.md:15,25–27` for the smooth
half-power count, and `e6b43a82` / `1d036a89`,
`.godel/alice/denominator-pair-gap-regions.md:19–35,47` for the nonvertical
rank-two bin and its crossing-divisor count.

Scope: the finite Euler-product bound on positive smooth naturals and its
application to the two enumerands of `card_le_small_add_twice_crossing` in one
fixed bin. No asymptotic estimate, global summation, or capture claim.

Owning check session: `01a20ec7-4115-7a16-8368-f5947df6f1f0`.
-/

open scoped BigOperators

namespace AdaptivePlaneBin

open DividedPlaneFilter

/-- The finite half-power Euler product over all primes at most `X`. -/
@[expose] public noncomputable def smoothEulerPrice (X : ℕ) : ℝ :=
  ∏ p ∈ X.primesLE, (1 - (√(p : ℝ))⁻¹)⁻¹

private noncomputable def halfWeight (n : ℕ) : ℝ := (√(n : ℝ))⁻¹

private theorem halfWeight_nonneg (n : ℕ) : 0 ≤ halfWeight n :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

private theorem sqrt_nat_pow (p k : ℕ) : √((p : ℝ) ^ k) = (√(p : ℝ)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ', Real.sqrt_mul (Nat.cast_nonneg p), ih]

private theorem sum_halfWeight_le_smoothEulerPrice {Y : ℝ} (hY : 0 ≤ Y) (X : ℕ) :
    (∑ n ∈ smallDividedR Y X, halfWeight n) ≤ smoothEulerPrice X := by
  classical
  let P := X.primesLE
  let B := Finset.range (⌊Y⌋₊ + 1)
  let exponents (n : ℕ) : ∀ p ∈ P, ℕ := fun p _ => n.factorization p
  have hn0 {n : ℕ} (hn : n ∈ smallDividedR Y X) : n ≠ 0 :=
    Nat.ne_of_gt ((mem_smallDividedR hY).mp hn).1
  -- Extend the factorization to all primes in `P`, inserting zero exponents.
  have reconstruct (n : ℕ) (hn : n ∈ smallDividedR Y X) :
      (∏ p ∈ P, p ^ n.factorization p) = n := by
    symm
    refine (Nat.prod_primeFactors_pow_factorization (hn0 hn)).trans (Finset.prod_subset ?_ ?_)
    · intro p hp
      exact Nat.mem_primesLE.mpr
        ⟨((mem_smallDividedR hY).mp hn).2.2 p hp, Nat.prime_of_mem_primeFactors hp⟩
    · intro p _ hp
      have he : n.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
      rw [he, pow_zero]
  have hinj : Set.InjOn exponents ↑(smallDividedR Y X) := by
    intro m hm n hn hmn
    rw [← reconstruct m hm, ← reconstruct n hn]
    exact Finset.prod_congr rfl fun p hp =>
      congrArg (fun e : ∀ q ∈ P, ℕ => p ^ e p hp) hmn
  have hmem : (smallDividedR Y X).image exponents ⊆ P.pi (fun _ => B) := by
    intro e he
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_pi.mpr fun p _ => Finset.mem_range.mpr ?_
    exact (Nat.factorization_lt p (hn0 hn)).trans
      (Nat.lt_succ_of_le ((Nat.le_floor_iff hY).mpr ((mem_smallDividedR hY).mp hn).2.1))
  have hweight (n : ℕ) (hn : n ∈ smallDividedR Y X) :
      halfWeight n = ∏ p ∈ P.attach, halfWeight p.val ^ exponents n p.val p.property := by
    rw [Finset.prod_attach P (fun p => halfWeight p ^ n.factorization p)]
    calc
      halfWeight n = halfWeight (∏ p ∈ P, p ^ n.factorization p) :=
        congrArg halfWeight (reconstruct n hn).symm
      _ = ∏ p ∈ P, halfWeight p ^ n.factorization p := by
        simp only [halfWeight, Nat.cast_prod, Nat.cast_pow,
          Real.sqrt_prod P (fun p _ => pow_nonneg (Nat.cast_nonneg p) _), sqrt_nat_pow,
          ← Finset.prod_inv_distrib, inv_pow]
  calc
    (∑ n ∈ smallDividedR Y X, halfWeight n) ≤
        ∑ e ∈ P.pi (fun _ => B), ∏ p ∈ P.attach, halfWeight p.val ^ e p.val p.property :=
      Finset.sum_le_sum_of_injOn exponents hinj hmem (fun n hn => (hweight n hn).le)
        (fun e _ _ => Finset.prod_nonneg fun p _ => pow_nonneg (halfWeight_nonneg p.val) _)
    _ = ∏ p ∈ P, ∑ k ∈ B, halfWeight p ^ k :=
      (Finset.prod_sum P (fun _ => B) (fun p k => halfWeight p ^ k)).symm
    _ ≤ smoothEulerPrice X := by
      apply Finset.prod_le_prod₀
      · exact fun p _ => Finset.sum_nonneg fun k _ => pow_nonneg (halfWeight_nonneg p) k
      · intro p hp
        have hp₁ : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
        have hsqrt : (1 : ℝ) < √(p : ℝ) := by simpa using Real.sqrt_lt_sqrt zero_le_one hp₁
        have hden : 0 < 1 - halfWeight p := sub_pos.mpr (inv_lt_one_of_one_lt₀ hsqrt)
        change (∑ k ∈ B, halfWeight p ^ k) ≤ (1 - halfWeight p)⁻¹
        rw [← one_div]
        apply (le_div_iff₀ hden).mpr
        rw [geom_sum_mul_neg]
        exact sub_le_self _ (pow_nonneg (halfWeight_nonneg p) _)

/-- The count of positive `X`-smooth naturals at most `Y` is at most
`sqrt Y * smoothEulerPrice X`. The bound also holds when `X = 0`. -/
public theorem card_smallDividedR_le_smoothEulerPrice {Y : ℝ} (hY : 0 ≤ Y) (X : ℕ) :
    ((smallDividedR Y X).card : ℝ) ≤ √Y * smoothEulerPrice X := by
  calc
    ((smallDividedR Y X).card : ℝ) = ∑ _n ∈ smallDividedR Y X, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ smallDividedR Y X, √Y * halfWeight n := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn₁, hnY, _⟩ := (mem_smallDividedR hY).mp hn
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn₁
      rw [halfWeight, ← div_eq_mul_inv]
      exact (le_div_iff₀ (Real.sqrt_pos.mpr hnpos)).mpr (by simpa using Real.sqrt_le_sqrt hnY)
    _ = √Y * ∑ n ∈ smallDividedR Y X, halfWeight n := (Finset.mul_sum _ _ _).symm
    _ ≤ √Y * smoothEulerPrice X :=
      mul_le_mul_of_nonneg_left (sum_halfWeight_le_smoothEulerPrice hY X) (Real.sqrt_nonneg _)

/-- The explicit smooth-number price of the actual triples in one nonvertical
adaptive bin, using the same hypotheses as `card_le_small_add_twice_crossing`. -/
public theorem card_le_smoothEulerPrice {Γ : AddSubgroup (ℤ × ℤ × ℤ)}
    (a : NormalizedCoordinate Γ) {S : Finset Γ}
    {u w : (ℤ × ℤ) →ₗ[ℤ] ℤ} {M D T₀ T₁ : ℝ} {X : ℕ}
    (hπ : Function.Injective (gapProjection Γ)) (hC : 0 < (gapProjection Γ).range.index)
    (hM : 0 < M) (hD : 0 < D) (hU : 1 ≤ 4 * T₀) (hdet : formDet u w ≠ 0)
    (hm : Set.InjOn (fun p : Γ => p.val.1) ↑S)
    (hpos : ∀ p ∈ S, 0 < p.val.1)
    (hsmooth : ∀ p ∈ S, ∀ k ∈ p.val.1.natAbs.primeFactors, k ≤ X)
    (hprim : ∀ p ∈ S, Int.gcd p.val.1 p.val.2.1 = 1)
    (hpass : ∀ p ∈ S, Passes u w M D (adaptiveWidth Γ D T₀ T₁) (gapProjection Γ p)) :
    (S.card : ℝ) ≤ smoothEulerPrice X * (√(4 * T₀) + 2 * √(4 * T₀ * (X : ℝ))) := by
  have hU₀ : 0 ≤ 4 * T₀ := zero_le_one.trans hU
  have hsmall := card_smallDividedR_le_smoothEulerPrice hU₀ X
  have hcross : ((eligibleCrossingF (4 * T₀) X).card : ℝ) ≤
      √(4 * T₀ * (X : ℝ)) * smoothEulerPrice X := by
    have hsub : eligibleCrossingF (4 * T₀) X ⊆ smallDividedR (4 * T₀ * (X : ℝ)) X :=
      Finset.filter_subset _ _
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (card_smallDividedR_le_smoothEulerPrice (mul_nonneg hU₀ (Nat.cast_nonneg X)) X)
  calc
    (S.card : ℝ) ≤ ((smallDividedR (4 * T₀) X).card : ℝ) +
        2 * ((eligibleCrossingF (4 * T₀) X).card : ℝ) := by
      exact_mod_cast card_le_small_add_twice_crossing a hπ hC hM hD hU hdet hm hpos hsmooth hprim hpass
    _ ≤ √(4 * T₀) * smoothEulerPrice X + 2 * (√(4 * T₀ * (X : ℝ)) * smoothEulerPrice X) :=
      add_le_add hsmall (mul_le_mul_of_nonneg_left hcross (by norm_num))
    _ = _ := by ring

end AdaptivePlaneBin
