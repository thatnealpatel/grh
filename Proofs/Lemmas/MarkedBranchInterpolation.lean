module

public import Lemmas.SmoothBranchEvaluation
public import Lemmas.MarkedBranchDivisor
import Mathlib.Algebra.Polynomial.Div

/-!
# Finite interpolation of normalized jets on a marked smooth branch

Source: `d500be7bb3a2:.godel/alice/jet-axis-lcm.md:26–92`,
`4cda3a091f6f:.godel/alice/jet-reference-disks.md:12–86`, and
`4cda3a091f6f:.godel/alice/jet-quotient-determinant.md:21–60`.
Owning check session: `01a20f35-88fa-72a0-aedd-8c10c7068d1c`.

Scope: one prime and one marked residue disk of a plane curve, oriented so the
ordinate partial derivative at the center is a unit. The center is a root, and
the parameter is the actual free-coordinate displacement from that center. In
the source chart `Z = 1` with `p ∤ q`, the center `(A/q, B/q)` is in `ℤ_[p]²`.
The dehomogenized integral test forms map into `ℤ_[p][X][X]`; their Taylor
coefficients after translation are integral in `ℤ_[p]`, not necessarily in `ℤ`.
Order at least `r` means that every translated coefficient of total degree
less than `r` vanishes. The integral axis displacement `q I - A` being divisible
by `l` gives `l ∣ I - A/q` in `ℤ_[p]`, since `q` is a unit there. The integer
normalization from the source is used as an exact multiplication identity, not as
a congruence or as division in a residue ring. This is the finite interpolation
step, not a determinant bound or a construction of the global jet lattice.
-/

open Polynomial SmoothBranchEvaluation
open scoped BigOperators

namespace MarkedBranchInterpolation

/-- Translate an affine bivariate polynomial to a center; the ordinate is the outer
variable. The new coordinates are displacements from `(a, b)`. -/
@[expose] public noncomputable def translate {R : Type*} [CommRing R]
    (M : R[X][X]) (a b : R) : R[X][X] :=
  (M.map (eval₂RingHom C (X + C a))).comp (X + C (C b))

/-- The Taylor coefficients below total degree `r` at `(a, b)` vanish. -/
@[expose] public def VanishesToOrderAt {R : Type*} [CommRing R]
    (M : R[X][X]) (a b : R) (r : ℕ) : Prop :=
  ∀ i j : ℕ, i + j < r → ((translate M a b).coeff j).coeff i = 0

private theorem eval_translate {R : Type*} [CommRing R]
    (M : R[X][X]) (a b t s : R) :
    evalAt (translate M a b) t s = evalAt M (t + a) (s + b) := by
  have hC : (evalRingHom t).comp C = RingHom.id R := by
    ext z
    exact eval_C
  have hcomp : (evalRingHom t).comp (eval₂RingHom C (X + C a)) = evalRingHom (t + a) := by
    apply RingHom.ext
    intro P
    change (evalRingHom t) (P.eval₂ C (X + C a)) = P.eval (t + a)
    rw [P.hom_eval₂, hC]
    simp [eval₂_id]
  simp only [translate, evalAt, eval₂_comp, eval₂_add, eval₂_X, eval₂_C,
    coe_evalRingHom, eval_C, eval₂_map]
  exact congrArg (fun f : R[X] →+* R ↦ M.eval₂ f (s + b)) hcomp

private theorem pow_X_dvd_subst {R : Type*} [CommRing R] (J : R[X][X]) (D : R[X])
    (hD : X ∣ D) (r : ℕ) (hJ : ∀ i j : ℕ, i + j < r → (J.coeff j).coeff i = 0) :
    (X : R[X]) ^ r ∣ J.eval D := by
  rw [eval_eq_sum, Polynomial.sum_def]
  apply Finset.dvd_sum
  intro j hj
  conv_rhs => rw [(J.coeff j).as_sum_support_C_mul_X_pow]
  rw [Finset.sum_mul]
  apply Finset.dvd_sum
  intro i hi
  have hij : r ≤ i + j := le_of_not_gt fun h ↦ (mem_support_iff.mp hi) (hJ i j h)
  apply (pow_dvd_pow X hij).trans
  rw [pow_add, mul_assoc]
  exact (mul_dvd_mul (dvd_refl _) (pow_dvd_pow_of_dvd hD j)).mul_left _

variable {p : ℕ} [Fact p.Prime]

private theorem cancel_normalization {l z : ℤ_[p]} (hl : l ≠ 0) {r E : ℕ}
    (h : (p : ℤ_[p]) ^ (E + l.valuation * r) ∣ l ^ r * z) :
    (p : ℤ_[p]) ^ E ∣ z := by
  let U := PadicInt.unitCoeff hl
  have hfac : l ^ r = (U : ℤ_[p]) ^ r * (p : ℤ_[p]) ^ (l.valuation * r) := by
    rw [pow_mul, ← mul_pow]
    exact congrArg (· ^ r) (PadicInt.unitCoeff_spec hl)
  have hunit : IsUnit ((U : ℤ_[p]) ^ r) := U.isUnit.pow r
  rw [hfac, mul_assoc, hunit.dvd_mul_left, add_comm E, pow_add] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))).mp h

private theorem reduction_eq_iff {N : ℕ} {v w : ℤ_[p]} :
    PadicInt.toZModPow N v = PadicInt.toZModPow N w ↔ (p : ℤ_[p]) ^ N ∣ v - w := by
  rw [← RingHom.sub_mem_ker_iff, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

private theorem exists_quotient_representative {l : ℤ} (hl : (l : ℤ_[p]) ≠ 0) {τ : ℤ_[p]}
    (hldiv : (l : ℤ_[p]) ∣ τ) {k e : ℕ} (hk : (p : ℤ_[p]) ^ k ∣ τ)
    (he : e ≤ k - (l : ℤ_[p]).valuation) (N : ℕ) :
    ∃ q : ℤ, (p : ℤ) ^ e ∣ q ∧
      PadicInt.toZModPow N ((l * q : ℤ) : ℤ_[p]) = PadicInt.toZModPow N τ := by
  have hd : (l : ℤ_[p]) * (p : ℤ_[p]) ^ e ∣ τ := by
    by_cases he0 : e = 0
    · simpa [he0] using hldiv
    let U := PadicInt.unitCoeff hl
    have hfac : (l : ℤ_[p]) * (p : ℤ_[p]) ^ e =
        (U : ℤ_[p]) * (p : ℤ_[p]) ^ ((l : ℤ_[p]).valuation + e) := by
      rw [pow_add, ← mul_assoc, ← PadicInt.unitCoeff_spec hl]
    have hν : (l : ℤ_[p]).valuation + e ≤ k := by omega
    rw [hfac]
    refine dvd_trans ?_ ((pow_dvd_pow _ hν).trans hk)
    simpa only [one_mul] using mul_dvd_mul (U.isUnit.dvd : (U : ℤ_[p]) ∣ 1)
      (dvd_refl ((p : ℤ_[p]) ^ ((l : ℤ_[p]).valuation + e)))
  obtain ⟨w, hw⟩ := hd
  refine ⟨(p : ℤ) ^ e * (w.appr N : ℤ), dvd_mul_right _ _, ?_⟩
  let ρ := PadicInt.toZModPow (p := p) N
  have h : ρ w = ρ (w.appr N : ℤ_[p]) :=
    reduction_eq_iff.mpr (Ideal.mem_span_singleton.mp (PadicInt.appr_spec N w))
  calc
    ρ _ = ρ ((l : ℤ_[p]) * (p : ℤ_[p]) ^ e * w) := by
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, map_mul, h]
      rw [mul_assoc]
    _ = ρ τ := congrArg ρ hw.symm

private theorem map_eval_congr {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (P : R[X]) {z w : R} (h : ρ z = ρ w) :
    ρ (P.eval z) = ρ (P.eval w) := by
  rw [← P.eval₂_at_apply ρ z, ← P.eval₂_at_apply ρ w, h]

private theorem map_evalAt_congr {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (M : R[X][X]) (x : R) {y z : R} (h : ρ y = ρ z) :
    ρ (evalAt M x y) = ρ (evalAt M x z) := by
  rw [evalAt, evalAt, M.hom_eval₂, M.hom_eval₂, h]

private theorem eval_subst {R : Type*} [CommRing R] (J : R[X][X]) (D : R[X]) (z : R) :
    (J.eval D).eval z = evalAt J z (D.eval z) :=
  (J.eval₂_at_apply (evalRingHom z) D).symm

/-- For a finite family of roots in the marked disk, each test has one integer polynomial
common to all the roots and to all requested displacement precisions `G`. Here `k u` is a
lower bound on the depth of the actual displacement, and `excess u` is at most the part
of that depth above the valuation of `l u`. The *same* integer `t u = l u * q u` gives
both the displacement approximation and the normalized congruence modulo `p ^ E`. -/
public theorem exists_normalized_interpolation {n m : ℕ}
    (F : ℤ_[p][X][X]) (a b : ℤ_[p]) (hcenter : evalAt F a b = 0)
    (hunit : IsUnit (evalAt F.derivative a b))
    (x y : Fin n → ℤ_[p]) (hx : ∀ u, (p : ℤ_[p]) ∣ x u - a)
    (hy : ∀ u, PadicInt.toZModPow 1 (y u) = PadicInt.toZModPow 1 b)
    (hroot : ∀ u, evalAt F (x u) (y u) = 0)
    (l : Fin n → ℤ) (hl : ∀ u, l u ≠ 0) (hldiv : ∀ u, (l u : ℤ_[p]) ∣ x u - a)
    (k excess : Fin n → ℕ) (hdepth : ∀ u, (p : ℤ_[p]) ^ k u ∣ x u - a)
    (hexcess : ∀ u, excess u ≤ k u - (l u : ℤ_[p]).valuation)
    (r E : ℕ) (M : Fin m → ℤ_[p][X][X]) (hM : ∀ i, VanishesToOrderAt (M i) a b r)
    (A : Fin n → Fin m → ℤ)
    (hA : ∀ u i, evalAt (M i) (x u) (y u) = (l u : ℤ_[p]) ^ r * (A u i : ℤ_[p])) :
    ∃ P : Fin m → ℤ[X], ∀ G : ℕ, ∃ t q : Fin n → ℤ,
      (∀ u, t u = l u * q u ∧ (p : ℤ) ^ excess u ∣ q u ∧
        PadicInt.toZModPow G (t u : ℤ_[p]) = PadicInt.toZModPow G (x u - a)) ∧
      MarkedBranchDivisor.NormalizedScalars p r true l t (fun u ↦ q u ^ r) excess ∧
      ∀ u i, A u i ≡ q u ^ r * (P i).eval (t u) [ZMOD ↑(p ^ E)] := by
  classical
  let ν (u : Fin n) := (l u : ℤ_[p]).valuation
  -- Allow for the loss of `r * ν u` digits in each row before coefficient reduction.
  let N := E + Finset.univ.sup ν * r
  let ρ := PadicInt.toZModPow (p := p) N
  obtain ⟨B, hB⟩ := exists_ordinate_polynomial F a b hunit N
  have hB₀ : ρ (B.eval 0) = ρ b := by
    have ha : (p : ℤ_[p]) ∣ a - a := by rw [sub_self]; exact dvd_zero _
    simpa only [sub_self] using hB a b ha rfl hcenter
  let D := B - C (B.eval 0)
  have hD : X ∣ D := X_dvd_iff.mpr (by rw [coeff_zero_eq_eval_zero]; simp [D])
  have hDy (u : Fin n) : ρ (D.eval (x u - a)) = ρ (y u - b) := by
    rw [show D.eval (x u - a) = B.eval (x u - a) - B.eval 0 by simp [D],
      map_sub, map_sub, hB (x u) (y u) (hx u) (hy u) (hroot u), hB₀]
  let J (i : Fin m) := translate (M i) a b
  have hQex (i : Fin m) : ∃ Q : ℤ_[p][X], (J i).eval D = X ^ r * Q :=
    pow_X_dvd_subst (J i) D hD r (hM i)
  choose Q hQ using hQex
  have hPex (i : Fin m) : ∃ P : ℤ[X],
      P.map (Int.castRingHom (ZMod (p ^ N))) = (Q i).map ρ :=
    Polynomial.map_surjective _ ZMod.intCast_surjective _
  choose P hP using hPex
  refine ⟨P, fun G ↦ ?_⟩
  have hlₚ (u : Fin n) : (l u : ℤ_[p]) ≠ 0 := Int.cast_ne_zero.mpr (hl u)
  choose q hq using fun u : Fin n ↦
    exists_quotient_representative (hlₚ u) (hldiv u) (hdepth u) (hexcess u) (max N G)
  let t (u : Fin n) := l u * q u
  have ht (u : Fin n) : (p : ℤ_[p]) ^ max N G ∣ (t u : ℤ_[p]) - (x u - a) :=
    reduction_eq_iff.mp (hq u).2
  refine ⟨t, q, fun u ↦ ⟨rfl, (hq u).1, ?_⟩, fun u ↦ ⟨hl u, q u, rfl, rfl, (hq u).1⟩,
    fun u i ↦ ?_⟩
  · exact reduction_eq_iff.mpr ((pow_dvd_pow _ (le_max_right N G)).trans (ht u))
  have htN : ρ (t u : ℤ_[p]) = ρ (x u - a) :=
    reduction_eq_iff.mpr ((pow_dvd_pow _ (le_max_left N G)).trans (ht u))
  have hlift : ρ ((Q i).eval (t u : ℤ_[p])) = (↑((P i).eval (t u)) : ZMod (p ^ N)) := by
    rw [← eval₂_at_apply, ← eval_map, ← hP i, eval_map, map_intCast]
    exact (P i).eval₂_at_apply (Int.castRingHom (ZMod (p ^ N))) (t u)
  have heval : ρ (evalAt (M i) (x u) (y u)) =
      ((t u ^ r * (P i).eval (t u) : ℤ) : ZMod (p ^ N)) := by
    calc
      _ = ρ (evalAt (J i) (x u - a) (y u - b)) := by
        rw [show J i = translate (M i) a b from rfl, eval_translate, sub_add_cancel,
          sub_add_cancel]
      _ = ρ (((J i).eval D).eval (x u - a)) := by
        rw [eval_subst]
        exact map_evalAt_congr ρ (J i) _ (hDy u).symm
      _ = ρ (((J i).eval D).eval (t u : ℤ_[p])) := map_eval_congr ρ _ htN.symm
      _ = _ := by
        rw [hQ i, eval_mul, eval_pow, eval_X, map_mul, map_pow, hlift, map_intCast]
        simp only [Int.cast_mul, Int.cast_pow]
  have hraw : (p : ℤ_[p]) ^ N ∣
      evalAt (M i) (x u) (y u) - ((t u ^ r * (P i).eval (t u) : ℤ) : ℤ_[p]) :=
    reduction_eq_iff.mp (by simpa only [map_intCast] using heval)
  have hprec : E + ν u * r ≤ N := by
    have hle : ν u ≤ Finset.univ.sup ν := Finset.le_sup (Finset.mem_univ u)
    exact Nat.add_le_add_left (Nat.mul_le_mul_right r hle) E
  have hsub := (pow_dvd_pow _ hprec).trans hraw
  have heq : ((t u ^ r * (P i).eval (t u) : ℤ) : ℤ_[p]) =
      (l u : ℤ_[p]) ^ r * ((q u ^ r * (P i).eval (t u) : ℤ) : ℤ_[p]) := by
    simp only [Int.cast_mul, Int.cast_pow, t, mul_pow, mul_assoc]
  rw [hA, heq, ← mul_sub] at hsub
  have hnorm := cancel_normalization (hlₚ u) hsub
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  simpa only [map_intCast] using reduction_eq_iff.mpr hnorm

end MarkedBranchInterpolation
