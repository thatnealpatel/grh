module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Interval.Finset.Fin

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.Rev
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Finite normalized branch divisor of a square minor

Source: `d500be7b:.godel/alice/jet-axis-lcm.md:44–92`, the divisor in (1) and its
assembly before (2); see also `.godel/alice/jet-quotient-determinant.md:383–386`.
Owning check session: `01a20f1a-0f71-75d4-a170-6751dc7ee00a`.

Rows are evaluation points and columns are tests. For a rectangular matrix `B`, use
`A := B.submatrix rows cols` for the chosen square minor and restrict the witnesses to those
rows and tests. Within a prime the same polynomial for a given test is used at every row.
We take finite congruences to the normalized evaluations as input. We do not construct
analytic normalized jets, pass to a limit, reduce to a primitive quotient wedge, or prove
the norm bound in (2).

The local lower bounds are stated as divisibilities, including when parameters or their
pairwise differences are zero. In the grouped bound a singleton still gets the marked
scalar contribution, and an empty minor has divisor `1`.
-/

open Polynomial
open scoped BigOperators Matrix

namespace MarkedBranchDivisor

private theorem eval_eq_vandermonde_mul {a : ℕ} (ha : 0 < a)
    (t : Fin a → ℤ) (P : Fin a → ℤ[X]) :
    ∃ C : Matrix (Fin a) (Fin a) ℤ, (Matrix.of fun u i ↦ (P i).eval (t u)) =
      Matrix.vandermonde t * C := by
  -- Reduction by a monic polynomial over ℤ preserves all the evaluations, even at repeats.
  let W : ℤ[X] := ∏ u, (X - Polynomial.C (t u))
  have hmonic : W.Monic := monic_prod_X_sub_C t Finset.univ
  have hdeg : W.natDegree = a := by
    rw [Polynomial.natDegree_prod_of_monic Finset.univ (fun u ↦ X - Polynomial.C (t u))
      (fun u _ ↦ monic_X_sub_C (t u))]
    simp only [natDegree_X_sub_C, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_fin, Nat.cast_id]
  have hne : W ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hdeg
    omega
  have hW (u : Fin a) : W.eval (t u) = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ u) (by simp)
  let Q (i : Fin a) : ℤ[X] := P i %ₘ W
  have hQdeg (i : Fin a) : (Q i).natDegree < a := hdeg ▸ natDegree_modByMonic_lt (P i) hmonic hne
  have heval (u i : Fin a) : (Q i).eval (t u) = (P i).eval (t u) := by
    have h := congrArg (eval (t u)) (modByMonic_add_div (P i) W)
    simpa only [eval_add, eval_mul, hW, zero_mul, add_zero] using h
  refine ⟨Matrix.of fun n i ↦ (Q i).coeff n, ?_⟩
  ext u i
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vandermonde_apply]
  rw [← heval u i, eval_eq_sum_range,
    Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ (t u) ^ n * (Q i).coeff n) a]
  refine (Finset.sum_subset (Finset.range_mono (hQdeg i)) ?_).trans ?_
  · intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    rw [coeff_eq_zero_of_natDegree_lt (by omega : (Q i).natDegree < n), zero_mul]
  · apply Finset.sum_congr rfl
    intro n _
    exact mul_comm _ _

/-- Exact integral factorization by the product of all the row scalars and the entire
Vandermonde, not merely by the individual differences. -/
public theorem exists_det_eq_scalar_mul_vandermonde {a : ℕ}
    (t s : Fin a → ℤ) (P : Fin a → ℤ[X]) :
    ∃ z : ℤ, (Matrix.of fun u i ↦ s u * (P i).eval (t u)).det =
      ((∏ u, s u) * ∏ u, ∏ v ∈ Finset.Ioi u, (t v - t u)) * z := by
  cases a with
  | zero => exact ⟨1, by simp [Matrix.det_isEmpty]⟩
  | succ a =>
    obtain ⟨C, hC⟩ := eval_eq_vandermonde_mul (Nat.zero_lt_succ a) t P
    refine ⟨C.det, ?_⟩
    calc
      _ = (∏ u, s u) * (Matrix.of fun u i ↦ (P i).eval (t u)).det :=
        Matrix.det_mul_column s (Matrix.of fun u i ↦ (P i).eval (t u))
      _ = _ := by rw [hC, Matrix.det_mul, Matrix.det_vandermonde, mul_assoc]

/-- The sum of the lower bounds on differences for `u < v`, plus `r` times the sum of
the lower bounds on the marked quotients. -/
@[expose] public def localExponent {a : ℕ} (r : ℕ)
    (gap : Fin a → Fin a → ℕ) (excess : Fin a → ℕ) : ℕ :=
  (∑ u, ∑ v ∈ Finset.Ioi u, gap u v) + r * (∑ u, excess u)

/-- On a marked branch choose an integer representative `q` of the quotient with its own
power divisibility lower bound, and take representatives `t u = l u * q` and `s u = q ^ r`.
The denominator `l u` is nonzero, but `q` may be zero. On an unmarked branch the excess must
be zero and the scalar must not be divisible by `p`. For a prime `p` this allows, in particular,
an integer representative of the local unit `l u` to the power `-r`. -/
@[expose] public def NormalizedScalars {a : ℕ} (p r : ℕ) (marked : Bool)
    (l t s : Fin a → ℤ) (excess : Fin a → ℕ) : Prop :=
  if marked then
    ∀ u, l u ≠ 0 ∧ ∃ q : ℤ, t u = l u * q ∧ s u = q ^ r ∧ (p : ℤ) ^ excess u ∣ q
  else
    ∀ u, excess u = 0 ∧ ¬ (p : ℤ) ∣ s u

/-- Finite form of the full local exponent in (1), for a square minor of a single branch
class. Congruences at this precision suffice; no primality is needed for this step. -/
public theorem prime_pow_dvd_det_of_local_congruence {a p r : ℕ} {marked : Bool}
    (A : Matrix (Fin a) (Fin a) ℤ) (l t s : Fin a → ℤ) (P : Fin a → ℤ[X])
    (gap : Fin a → Fin a → ℕ) (excess : Fin a → ℕ)
    (hgap : ∀ u v, u < v → (p : ℤ) ^ gap u v ∣ t v - t u)
    (hs : NormalizedScalars p r marked l t s excess)
    (hA : ∀ u i, A u i ≡ s u * (P i).eval (t u) [ZMOD ↑(p ^ localExponent r gap excess)]) :
    (↑(p ^ localExponent r gap excess) : ℤ) ∣ A.det := by
  have hd : (p : ℤ) ^ (∑ u, ∑ v ∈ Finset.Ioi u, gap u v) ∣
      ∏ u, ∏ v ∈ Finset.Ioi u, (t v - t u) := by
    simp only [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun u _ ↦
      Finset.prod_dvd_prod_of_dvd _ _ fun v hv ↦ hgap u v (Finset.mem_Ioi.mp hv)
  have hsrow (u : Fin a) : (p : ℤ) ^ (r * excess u) ∣ s u := by
    cases marked with
    | false =>
      have h : excess u = 0 := (hs u).1
      simp [h]
    | true =>
      obtain ⟨_, q, _, hsq, hq⟩ := hs u
      rw [hsq, mul_comm r, pow_mul]
      exact pow_dvd_pow_of_dvd hq r
  have hsc : (p : ℤ) ^ (r * ∑ u, excess u) ∣ ∏ u, s u := by
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun u _ ↦ hsrow u
  let B : Matrix (Fin a) (Fin a) ℤ := Matrix.of fun u i ↦ s u * (P i).eval (t u)
  have hB : (↑(p ^ localExponent r gap excess) : ℤ) ∣ B.det := by
    obtain ⟨z, hz⟩ := exists_det_eq_scalar_mul_vandermonde t s P
    change B.det = _ at hz
    rw [hz, Nat.cast_pow, localExponent, pow_add, mul_comm (∏ u, s u)]
    exact (mul_dvd_mul hd hsc).trans (dvd_mul_right _ _)
  let ρ := Int.castRingHom (ZMod (p ^ localExponent r gap excess))
  have hmap : ρ.mapMatrix A = ρ.mapMatrix B := by
    ext u i
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hA u i)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change ρ A.det = 0
  rw [ρ.map_det, hmap, ← ρ.map_det]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hB

private theorem sum_card_Ioi (a : ℕ) : ∑ u : Fin a, (Finset.Ioi u).card = a.choose 2 := by
  calc
    _ = ∑ u : Fin a, (Fin.revPerm u : ℕ) := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [Fin.card_Ioi, Fin.revPerm_apply, Fin.val_rev]
      omega
    _ = ∑ u : Fin a, (u : ℕ) := Equiv.sum_comp Fin.revPerm Fin.val
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun x : ℕ ↦ x), Finset.sum_range_id, Nat.choose_two_right]

private theorem localExponent_const (a r k e : ℕ) :
    localExponent (a := a) r (fun _ _ ↦ k) (fun _ ↦ e) = k * a.choose 2 + e * (r * a) := by
  have hgap : (∑ u : Fin a, ∑ _v ∈ Finset.Ioi u, k) = k * a.choose 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    rw [← Finset.sum_mul, sum_card_Ioi, mul_comm]
  rw [localExponent, hgap]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.cast_id]
  ac_rfl

private theorem prod_pow_group {G J : ℕ} (hG : G ≠ 0) (hJ : J ∣ G) (V R : ℕ) :
    (∏ p ∈ G.primeFactors, p ^ (G.factorization p * V + J.factorization p * R)) = G ^ V * J ^ R := by
  have hJ0 : J ≠ 0 := by
    intro h
    simp [h, hG] at hJ
  have hJG : ∏ p ∈ G.primeFactors, p ^ J.factorization p = J := by
    calc
      _ = ∏ p ∈ J.primeFactors, p ^ J.factorization p := by
        symm
        apply Finset.prod_subset (Nat.primeFactors_mono hJ hG)
        intro p _ hp
        have hzero : J.factorization p = 0 :=
          Finsupp.notMem_support_iff.mp (Nat.support_factorization J ▸ hp)
        rw [hzero, pow_zero]
      _ = J := by
        simpa only [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hJ0
  have hGG : ∏ p ∈ G.primeFactors, p ^ G.factorization p = G := by
    simpa only [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hG
  simp_rw [pow_add, pow_mul, Finset.prod_mul_distrib, Finset.prod_pow, hGG, hJG]

/-- For a group with modulus `G` and marked divisor `J ∣ G`, each prime `p` uses the
uniform pairwise lower bound `G.factorization p` and row excess `J.factorization p`.
The branch marking, parameters, scalars and common polynomials can vary with `p`.
Assemble their coprime prime powers into the divisor of the integral minor. -/
public theorem group_divisor_dvd_det_of_prime_power_congruences {a G J r : ℕ}
    (hG : G ≠ 0) (hJ : J ∣ G) (A : Matrix (Fin a) (Fin a) ℤ) (l : Fin a → ℤ)
    (h : ∀ p ∈ G.primeFactors,
      ∃ (marked : Bool) (t s : Fin a → ℤ) (P : Fin a → ℤ[X]),
        (∀ u v, u < v → (p : ℤ) ^ G.factorization p ∣ t v - t u) ∧
        NormalizedScalars p r marked l t s (fun _ ↦ J.factorization p) ∧
        (∀ u i, A u i ≡ s u * (P i).eval (t u)
          [ZMOD ↑(p ^ (G.factorization p * a.choose 2 + J.factorization p * (r * a)))])) :
    (↑(G ^ a.choose 2 * J ^ (r * a)) : ℤ) ∣ A.det := by
  let E (p : ℕ) := G.factorization p * a.choose 2 + J.factorization p * (r * a)
  have hlocal (p : ℕ) (hp : p ∈ G.primeFactors) : (↑(p ^ E p) : ℤ) ∣ A.det := by
    obtain ⟨marked, t, s, P, hgap, hs, hA⟩ := h p hp
    have hE : localExponent (a := a) r (fun _ _ ↦ G.factorization p)
        (fun _ ↦ J.factorization p) = E p := localExponent_const _ _ _ _
    change (∀ u i, A u i ≡ s u * (P i).eval (t u) [ZMOD ↑(p ^ E p)]) at hA
    rw [← hE] at hA ⊢
    exact prime_pow_dvd_det_of_local_congruence A l t s P _ _ hgap hs hA
  have hcop : (↑G.primeFactors : Set ℕ).Pairwise
      (Function.onFun IsCoprime fun p ↦ (↑(p ^ E p) : ℤ)) := by
    intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp)
    have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hq)
    exact (((Nat.coprime_primes hp' hq').mpr hpq).pow (E p) (E q)).isCoprime
  have hprod := Finset.prod_dvd_of_coprime hcop hlocal
  rw [← Nat.cast_prod, prod_pow_group hG hJ] at hprod
  exact hprod

end MarkedBranchDivisor
