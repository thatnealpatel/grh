module

public import Lemmas.MarkedBranchInterpolation

/-!
# Divisor of an actual normalized minor on a smooth p-adic disk

Source: `d500be7bb3a2:.godel/alice/jet-axis-lcm.md:26–92`, the local divisor (1)
and the grouped divisor before (2), used in `a433ed178:.godel/alice/jet-reference-disks.md:35–76`.
Owning check session: `01a20f6c-c41c-70db-8373-949d4b4e2596`.

The outer variable of the curve and test polynomials is the ordinate. Rows index
actual roots and columns index the selected tests of the square integral minor.
The scale identity is an equality in `ℤ_[p]`, not a congruence hypothesis. The
marked row gain comes only from the displacement from the marked center. A
reference point can certify pairwise gaps (and need not be a row); it does not
increase the depth used for the marked row gain. No quotient saturation,
archimedean determinant bound, or point count is asserted here.
-/

open Polynomial SmoothBranchEvaluation MarkedBranchInterpolation MarkedBranchDivisor
open scoped BigOperators

namespace SmoothDiskMinor

variable {p : ℕ} [Fact p.Prime]

private theorem reduction_eq_iff {N : ℕ} {z w : ℤ_[p]} :
    PadicInt.toZModPow N z = PadicInt.toZModPow N w ↔ (p : ℤ_[p]) ^ N ∣ z - w := by
  rw [← RingHom.sub_mem_ker_iff, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

private theorem int_pow_dvd_of_cast_dvd {N : ℕ} {z : ℤ}
    (h : (p : ℤ_[p]) ^ N ∣ (z : ℤ_[p])) : (p : ℤ) ^ N ∣ z := by
  rw [← Nat.cast_pow]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ N)).mp
  have hz := (reduction_eq_iff (w := 0)).mpr (by simpa only [sub_zero] using h)
  simpa only [map_intCast, map_zero] using hz

private theorem dvd_sub_representatives {N G : ℕ} (hNG : N ≤ G)
    {s t : ℤ} {z w : ℤ_[p]}
    (hs : PadicInt.toZModPow G (s : ℤ_[p]) = PadicInt.toZModPow G z)
    (ht : PadicInt.toZModPow G (t : ℤ_[p]) = PadicInt.toZModPow G w)
    (hzw : (p : ℤ_[p]) ^ N ∣ z - w) : (p : ℤ) ^ N ∣ s - t := by
  have hs' := (pow_dvd_pow (p : ℤ_[p]) hNG).trans (reduction_eq_iff.mp hs)
  have ht' := (pow_dvd_pow (p : ℤ_[p]) hNG).trans (reduction_eq_iff.mp ht)
  apply int_pow_dvd_of_cast_dvd (p := p)
  rw [Int.cast_sub, show (s : ℤ_[p]) - (t : ℤ_[p]) =
    ((s : ℤ_[p]) - z) + (z - w) - ((t : ℤ_[p]) - w) by abel]
  exact dvd_sub (dvd_add hs' hzw) ht'

private theorem exists_marked_congruences {n : ℕ}
    (F : ℤ_[p][X][X]) (a b : ℤ_[p]) (hcenter : evalAt F a b = 0)
    (hunit : IsUnit (evalAt F.derivative a b))
    (x y : Fin n → ℤ_[p]) (hx : ∀ u, (p : ℤ_[p]) ∣ x u - a)
    (hy : ∀ u, PadicInt.toZModPow 1 (y u) = PadicInt.toZModPow 1 b)
    (hroot : ∀ u, evalAt F (x u) (y u) = 0)
    (l : Fin n → ℤ) (hl : ∀ u, l u ≠ 0) (hldiv : ∀ u, (l u : ℤ_[p]) ∣ x u - a)
    (k excess : Fin n → ℕ)
    (hdepth : ∀ u, (p : ℤ_[p]) ^ k u ∣ x u - a)
    (hexcess : ∀ u, excess u ≤ k u - (l u : ℤ_[p]).valuation)
    (r E : ℕ) (M : Fin n → ℤ_[p][X][X]) (hM : ∀ i, VanishesToOrderAt (M i) a b r)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ u i, evalAt (M i) (x u) (y u) = (l u : ℤ_[p]) ^ r * (A u i : ℤ_[p]))
    (gap : Fin n → Fin n → ℕ)
    (hgap : ∀ u v, u < v → (p : ℤ_[p]) ^ gap u v ∣ x v - x u) :
    ∃ (t s : Fin n → ℤ) (P : Fin n → ℤ[X]),
      (∀ u v, u < v → (p : ℤ) ^ gap u v ∣ t v - t u) ∧
      NormalizedScalars p r true l t s excess ∧
      ∀ u i, A u i ≡ s u * (P i).eval (t u) [ZMOD ↑(p ^ E)] := by
  let G := Finset.univ.sup fun u ↦ Finset.univ.sup (gap u)
  obtain ⟨P, hP⟩ := exists_normalized_interpolation F a b hcenter hunit x y hx hy hroot
    l hl hldiv k excess hdepth hexcess r E M hM A hA
  obtain ⟨t, q, ht, hs, heval⟩ := hP G
  refine ⟨t, fun u ↦ q u ^ r, P, fun u v huv ↦ ?_, hs, heval⟩
  have hle : gap u v ≤ G :=
    (Finset.le_sup (f := gap u) (Finset.mem_univ v)).trans
      (Finset.le_sup (f := fun i ↦ Finset.univ.sup (gap i)) (Finset.mem_univ u))
  exact dvd_sub_representatives hle (ht v).2.2 (ht u).2.2
    (by simpa only [sub_sub_sub_cancel_right] using hgap u v huv)

/-- The prime-power divisor for a square minor on one marked smooth disk. Each
`k u` certifies the depth of the actual free-coordinate displacement, and each
`gap u v` certifies the depth of the actual difference for `u < v`. The row excess
is `k u - vₚ(l u)`, with natural subtraction; no reference depth enters it.
Divisibility bounds also allow a zero displacement or a zero difference. -/
public theorem prime_pow_dvd_det_of_marked_disk {n : ℕ}
    (F : ℤ_[p][X][X]) (a b : ℤ_[p]) (hcenter : evalAt F a b = 0)
    (hunit : IsUnit (evalAt F.derivative a b))
    (x y : Fin n → ℤ_[p]) (hx : ∀ u, (p : ℤ_[p]) ∣ x u - a)
    (hy : ∀ u, PadicInt.toZModPow 1 (y u) = PadicInt.toZModPow 1 b)
    (hroot : ∀ u, evalAt F (x u) (y u) = 0)
    (l : Fin n → ℤ) (hl : ∀ u, l u ≠ 0) (hldiv : ∀ u, (l u : ℤ_[p]) ∣ x u - a)
    (k : Fin n → ℕ) (gap : Fin n → Fin n → ℕ)
    (hdepth : ∀ u, (p : ℤ_[p]) ^ k u ∣ x u - a)
    (hgap : ∀ u v, u < v → (p : ℤ_[p]) ^ gap u v ∣ x v - x u)
    (r : ℕ) (M : Fin n → ℤ_[p][X][X]) (hM : ∀ i, VanishesToOrderAt (M i) a b r)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ u i, evalAt (M i) (x u) (y u) = (l u : ℤ_[p]) ^ r * (A u i : ℤ_[p])) :
    (p : ℤ) ^ ((∑ u, ∑ v ∈ Finset.Ioi u, gap u v) +
      r * (∑ u, (k u - (l u : ℤ_[p]).valuation))) ∣ A.det := by
  let excess (u : Fin n) := k u - (l u : ℤ_[p]).valuation
  obtain ⟨t, s, P, htgap, hs, heval⟩ := exists_marked_congruences F a b hcenter hunit
    x y hx hy hroot l hl hldiv k excess hdepth (fun _ ↦ le_rfl)
    r (localExponent r gap excess) M hM A hA gap hgap
  simpa only [Nat.cast_pow, localExponent, excess] using
    prime_pow_dvd_det_of_local_congruence A l t s P gap excess htgap hs heval

private theorem exists_unit_representative (E : ℕ) (v : ℤ_[p]ˣ) :
    ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧
      PadicInt.toZModPow E (s : ℤ_[p]) = PadicInt.toZModPow E (v : ℤ_[p]) := by
  -- Even for E = 0, retain one digit so the integer representative is prime to p.
  let s : ℤ := (v : ℤ_[p]).appr (max E 1)
  have hd : (p : ℤ_[p]) ^ max E 1 ∣ (v : ℤ_[p]) - (s : ℤ_[p]) := by
    simpa only [s, Int.cast_natCast] using
      Ideal.mem_span_singleton.mp (PadicInt.appr_spec (max E 1) (v : ℤ_[p]))
  refine ⟨s, ?_, (reduction_eq_iff.mpr ((pow_dvd_pow _ (le_max_left E 1)).trans hd)).symm⟩
  intro hs
  have hs' : (p : ℤ_[p]) ∣ (s : ℤ_[p]) := by
    obtain ⟨z, hz⟩ := hs
    refine ⟨(z : ℤ_[p]), ?_⟩
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun m : ℤ ↦ (m : ℤ_[p])) hz
  have hd' : (p : ℤ_[p]) ∣ (v : ℤ_[p]) - (s : ℤ_[p]) := by
    simpa only [pow_one] using (pow_dvd_pow _ (le_max_right E 1)).trans hd
  exact PadicInt.irreducible_p.not_dvd_isUnit v.isUnit
    (by simpa only [sub_add_cancel] using dvd_add hd' hs')

private theorem exists_unmarked_congruences {n : ℕ}
    (F : ℤ_[p][X][X]) (a b : ℤ_[p]) (hunit : IsUnit (evalAt F.derivative a b))
    (x y : Fin n → ℤ_[p]) (hx : ∀ u, (p : ℤ_[p]) ∣ x u - a)
    (hy : ∀ u, PadicInt.toZModPow 1 (y u) = PadicInt.toZModPow 1 b)
    (hroot : ∀ u, evalAt F (x u) (y u) = 0)
    (l : Fin n → ℤ) (hl : ∀ u, IsUnit (l u : ℤ_[p]))
    (r E k : ℕ) (M : Fin n → ℤ_[p][X][X]) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ u i, evalAt (M i) (x u) (y u) = (l u : ℤ_[p]) ^ r * (A u i : ℤ_[p]))
    (hgap : ∀ u v, u < v → (p : ℤ_[p]) ^ k ∣ x v - x u) :
    ∃ (t s : Fin n → ℤ) (P : Fin n → ℤ[X]),
      (∀ u v, u < v → (p : ℤ) ^ k ∣ t v - t u) ∧
      (∀ u, ¬ (p : ℤ) ∣ s u) ∧
      ∀ u i, A u i ≡ s u * (P i).eval (t u) [ZMOD ↑(p ^ E)] := by
  let N := max E k
  let ρ := PadicInt.toZModPow (p := p) N
  obtain ⟨T, P, hT, hP⟩ := exists_integral_evaluation F a b hunit (le_rfl : 1 ≤ 1) N
  let t (u : Fin n) := T (x u - a)
  have hx' (u : Fin n) : (p : ℤ_[p]) ^ 1 ∣ x u - a := by simpa only [pow_one] using hx u
  choose L hL using hl
  choose s hs using fun u ↦ exists_unit_representative N ((L u)⁻¹ ^ r)
  refine ⟨t, fun u ↦ s u, fun i ↦ P (M i), fun u v huv ↦ ?_, fun u ↦ (hs u).1, ?_⟩
  · exact dvd_sub_representatives (le_max_right E k) (hT _ (hx' v)).2 (hT _ (hx' u)).2
      (by simpa only [sub_sub_sub_cancel_right] using hgap u v huv)
  intro u i
  have hnorm : ((↑(L u)⁻¹ : ℤ_[p]) ^ r) * evalAt (M i) (x u) (y u) = (A u i : ℤ_[p]) := by
    rw [hA, ← hL u, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have hred := congrArg ρ hnorm
  rw [map_mul, ← Units.val_pow_eq_pow_val, ← (hs u).2,
    hP (x u) (y u) (hx' u) (hy u) (hroot u) (M i)] at hred
  have hmod : A u i ≡ s u * (P (M i)).eval (t u) [ZMOD ↑(p ^ N)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa only [ρ, t, map_intCast, Int.cast_mul] using hred.symm
  refine Int.ModEq.of_dvd ?_ hmod
  simpa only [Nat.cast_pow] using pow_dvd_pow (p : ℤ) (le_max_left E k)

/-- Assemble the local divisors of the same square minor. At each prime of `G`, use
one oriented smooth disk and the actual evaluation identity there. The pairwise
bound comes from `G`. In the marked case `J.factorization p` is bounded by each
row's own excess; in the unmarked case it is zero and `l` is a local unit. -/
public theorem group_divisor_dvd_det_of_smooth_disks {n G J r : ℕ}
    (hG : G ≠ 0) (hJ : J ∣ G) (A : Matrix (Fin n) (Fin n) ℤ)
    (l : Fin n → ℤ) (hl : ∀ u, l u ≠ 0)
    (h : ∀ (p : ℕ) (hp : p ∈ G.primeFactors),
      letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      ∃ (F : ℤ_[p][X][X]) (a b : ℤ_[p]) (x y : Fin n → ℤ_[p]) (M : Fin n → ℤ_[p][X][X]),
        IsUnit (evalAt F.derivative a b) ∧
        (∀ u, (p : ℤ_[p]) ∣ x u - a) ∧
        (∀ u, PadicInt.toZModPow 1 (y u) = PadicInt.toZModPow 1 b) ∧
        (∀ u, evalAt F (x u) (y u) = 0) ∧
        (∀ u v, u < v → (p : ℤ_[p]) ^ G.factorization p ∣ x v - x u) ∧
        (∀ u i, evalAt (M i) (x u) (y u) = (l u : ℤ_[p]) ^ r * (A u i : ℤ_[p])) ∧
        ((evalAt F a b = 0 ∧ (∀ i, VanishesToOrderAt (M i) a b r) ∧
          (∀ u, (l u : ℤ_[p]) ∣ x u - a) ∧
          ∃ k : Fin n → ℕ, (∀ u, (p : ℤ_[p]) ^ k u ∣ x u - a) ∧
            (∀ u, J.factorization p ≤ k u - (l u : ℤ_[p]).valuation)) ∨
          (J.factorization p = 0 ∧ ∀ u, IsUnit (l u : ℤ_[p])))) :
    (↑(G ^ n.choose 2 * J ^ (r * n)) : ℤ) ∣ A.det := by
  apply group_divisor_dvd_det_of_prime_power_congruences hG hJ A l
  intro p hp
  let _ : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  obtain ⟨F, a, b, x, y, M, hunit, hx, hy, hroot, hgap, hA, hcases⟩ := h p hp
  let E := G.factorization p * n.choose 2 + J.factorization p * (r * n)
  rcases hcases with ⟨hcenter, hM, hldiv, k, hdepth, hexcess⟩ | ⟨he, hlu⟩
  · obtain ⟨t, s, P, ht, hs, hP⟩ := exists_marked_congruences F a b hcenter hunit
      x y hx hy hroot l hl hldiv k (fun _ ↦ J.factorization p) hdepth hexcess r E M hM A hA
      (fun _ _ ↦ G.factorization p) hgap
    exact ⟨true, t, s, P, ht, hs, hP⟩
  · obtain ⟨t, s, P, ht, hs, hP⟩ := exists_unmarked_congruences F a b hunit x y hx hy hroot
      l hlu r E (G.factorization p) M A hA hgap
    exact ⟨false, t, s, P, ht, fun u ↦ ⟨he, hs u⟩, hP⟩

end SmoothDiskMinor
