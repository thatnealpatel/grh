module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div

/-!
# Finite evaluation on a smooth p-adic branch

Source: `85027edf:.godel/alice/prescribed-product-jets.md:50–52`.
Applications: `e2145667:.godel/alice/through-point-components.md:25–41`.
Lean consumer contract: `Proofs/Lemmas/BranchEvaluationDivisor.lean:91–116`.
Owning check session: `01a20efe-657a-74fc-9a09-f6e32d4cc146`.

The outer polynomial variable is the ordinate. The resulting univariate polynomials
use the unscaled horizontal displacement `x - a`. We work on one ordinate residue
class and do not choose branches, lift roots at the base, or use a convergent series.
-/

open Polynomial
open scoped BigOperators

namespace SmoothBranchEvaluation

/-- Evaluate a polynomial in the ordinate with polynomial coefficients in the abscissa. -/
@[expose] public noncomputable def evalAt {R : Type*} [CommRing R] (F : R[X][X]) (x y : R) : R :=
  F.eval₂ (evalRingHom x) y

private theorem comp_eval₂RingHom {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (z : S) :
    g.comp (eval₂RingHom f z) = eval₂RingHom (g.comp f) (g z) := by
  apply RingHom.ext
  intro P
  exact P.hom_eval₂ f g z

/-- Simultaneously substitute `a + X` for the abscissa and `P` for the ordinate. -/
private noncomputable def substitute {R : Type*} [CommRing R]
    (F : R[X][X]) (a : R) (P : R[X]) : R[X] :=
  F.eval₂ (eval₂RingHom C (C a + X)) P

private theorem eval_substitute {R : Type*} [CommRing R] (F : R[X][X])
    (a t : R) (P : R[X]) : (substitute F a P).eval t = evalAt F (a + t) (P.eval t) := by
  have hC : (evalRingHom t).comp C = RingHom.id R := by
    apply RingHom.ext
    intro z
    exact eval_C
  have he : (evalRingHom t).comp (eval₂RingHom C (C a + X)) = evalRingHom (a + t) := by
    rw [comp_eval₂RingHom, hC]
    simp only [coe_evalRingHom, eval_add, eval_C, eval_X]
    rfl
  exact (F.hom_eval₂ _ (evalRingHom t) P).trans (congrArg (fun f ↦ F.eval₂ f _) he)

private theorem map_eval_congr {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (P : R[X]) {z z' : R} (hz : ρ z = ρ z') :
    ρ (P.eval z) = ρ (P.eval z') := by
  rw [← P.eval₂_at_apply ρ z, ← P.eval₂_at_apply ρ z', hz]

private theorem evalAt_congr {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (F : R[X][X]) {x x' y y' : R}
    (hx : ρ x = ρ x') (hy : ρ y = ρ y') :
    ρ (evalAt F x y) = ρ (evalAt F x' y') := by
  have hcomp : ρ.comp (evalRingHom x) = ρ.comp (evalRingHom x') := by
    apply RingHom.ext
    intro P
    exact map_eval_congr ρ P hx
  rw [evalAt, evalAt, F.hom_eval₂, F.hom_eval₂, hcomp, hy]

private theorem root_factor {R : Type*} [CommRing R] (F : R[X][X])
    {x y : R} (hy : evalAt F x y = 0) :
    ∃ Q : R[X], (∀ z, evalAt F x z = (z - y) * Q.eval z) ∧
      evalAt F.derivative x y = Q.eval y := by
  let f := F.map (evalRingHom x)
  have hroot : IsRoot f y := (eval_map _ _).trans hy
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hroot
  refine ⟨Q, fun z ↦ ?_, ?_⟩
  · rw [evalAt, eval₂_eq_eval_map]
    change f.eval z = _
    rw [hQ, eval_mul, eval_sub, eval_X, eval_C]
  · rw [evalAt, eval₂_eq_eval_map, ← derivative_map]
    change f.derivative.eval y = _
    rw [hQ, derivative_mul]
    simp

private noncomputable def iterate {R : Type*} [CommRing R] (F : R[X][X])
    (a b c : R) : ℕ → R[X]
  | 0 => C b
  | n + 1 =>
    let P := iterate F a b c n
    P - C c * substitute F a P

variable {p : ℕ} [Fact p.Prime]

private theorem reduction_eq_iff {r : ℕ} {u v : ℤ_[p]} :
    PadicInt.toZModPow r u = PadicInt.toZModPow r v ↔ (p : ℤ_[p]) ^ r ∣ u - v := by
  rw [← RingHom.sub_mem_ker_iff, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

private theorem reduction_eq_iff_one {u v : ℤ_[p]} :
    PadicInt.toZModPow 1 u = PadicInt.toZModPow 1 v ↔ (p : ℤ_[p]) ∣ u - v := by
  simpa only [pow_one] using (reduction_eq_iff (r := 1) (u := u) (v := v))

private theorem iterate_spec (F : ℤ_[p][X][X]) {a b x y : ℤ_[p]} {u : ℤ_[p]ˣ}
    (hu : evalAt F.derivative a b = (u : ℤ_[p]))
    (hx : (p : ℤ_[p]) ∣ x - a) (hy : PadicInt.toZModPow 1 y = PadicInt.toZModPow 1 b)
    (hroot : evalAt F x y = 0) (n : ℕ) :
    (p : ℤ_[p]) ^ (n + 1) ∣ (iterate F a b (↑u⁻¹) n).eval (x - a) - y := by
  obtain ⟨Q, hQ, hderiv⟩ := root_factor F hroot
  let ρ := PadicInt.toZModPow (p := p) 1
  have hQy : ρ (Q.eval y) = ρ (u : ℤ_[p]) := by
    rw [← hderiv, ← hu]
    exact evalAt_congr ρ _ (reduction_eq_iff_one.mpr hx) hy
  induction n with
  | zero => simpa only [zero_add, pow_one, iterate, eval_C] using reduction_eq_iff_one.mp hy.symm
  | succ n ih =>
    let P := iterate F a b (↑u⁻¹) n
    let z := P.eval (x - a)
    have hz : ρ z = ρ y := reduction_eq_iff_one.mpr <|
      (dvd_pow_self _ (Nat.succ_ne_zero n)).trans ih
    have hQz : ρ (Q.eval z) = ρ (u : ℤ_[p]) := (map_eval_congr ρ Q hz).trans hQy
    -- The inverse makes the new error multiplier vanish in the residue ring.
    have hcorr : (p : ℤ_[p]) ∣ 1 - (↑u⁻¹ : ℤ_[p]) * Q.eval z := by
      have hr : ρ ((↑u⁻¹ : ℤ_[p]) * Q.eval z) = ρ 1 := by
        rw [map_mul, hQz, ← map_mul, Units.inv_mul]
      exact reduction_eq_iff_one.mp hr.symm
    calc
      (p : ℤ_[p]) ^ (n + 1 + 1) ∣ (z - y) * (1 - (↑u⁻¹ : ℤ_[p]) * Q.eval z) := by
        rw [pow_succ]
        exact mul_dvd_mul ih hcorr
      _ = (iterate F a b (↑u⁻¹) (n + 1)).eval (x - a) - y := by
        have ha : a + (x - a) = x := by rw [add_comm, sub_add_cancel]
        rw [iterate, eval_sub, eval_mul, eval_C, eval_substitute, ha]
        change _ = z - (↑u⁻¹ : ℤ_[p]) * evalAt F x z - y
        rw [hQ]
        ring

/-- At any precision one polynomial works for all roots in the chosen residue disk.
Only the ordinate derivative at the center must be a unit; the center itself need not
be a root. The horizontal argument is the displacement, not its quotient by a power of `p`. -/
public theorem exists_ordinate_polynomial (F : ℤ_[p][X][X]) (a b : ℤ_[p])
    (hunit : IsUnit (evalAt F.derivative a b)) (r : ℕ) :
    ∃ P : ℤ_[p][X], ∀ x y : ℤ_[p], (p : ℤ_[p]) ∣ x - a →
      PadicInt.toZModPow 1 y = PadicInt.toZModPow 1 b → evalAt F x y = 0 →
      PadicInt.toZModPow r (P.eval (x - a)) = PadicInt.toZModPow r y := by
  obtain ⟨u, hu⟩ := hunit
  refine ⟨iterate F a b (↑u⁻¹) r, fun x y hx hy hroot ↦ reduction_eq_iff.mpr ?_⟩
  exact (pow_dvd_pow _ (Nat.le_succ r)).trans (iterate_spec F hu.symm hx hy hroot r)

private theorem exists_parameter_representative (k r : ℕ) {t : ℤ_[p]}
    (ht : (p : ℤ_[p]) ^ k ∣ t) :
    ∃ z : ℤ, (p : ℤ) ^ k ∣ z ∧
      PadicInt.toZModPow r (z : ℤ_[p]) = PadicInt.toZModPow r t := by
  obtain ⟨w, rfl⟩ := ht
  refine ⟨(p : ℤ) ^ k * (w.appr r : ℤ), dvd_mul_right _ _, ?_⟩
  have hw : PadicInt.toZModPow r w = PadicInt.toZModPow r (w.appr r : ℤ_[p]) :=
    reduction_eq_iff.mpr (Ideal.mem_span_singleton.mp (PadicInt.appr_spec r w))
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, map_mul, hw]

/-- At fixed precision and displacement divisibility there is a common integer polynomial
for each integral test. The representative function depends only on the displacement and
preserves divisibility by `p ^ k`, even when `r < k`. Neither it nor the test polynomials
are chosen separately for individual roots. -/
public theorem exists_integral_evaluation (F : ℤ_[p][X][X]) (a b : ℤ_[p])
    (hunit : IsUnit (evalAt F.derivative a b)) {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    ∃ (T : ℤ_[p] → ℤ) (P : ℤ_[p][X][X] → ℤ[X]),
      (∀ t : ℤ_[p], (p : ℤ_[p]) ^ k ∣ t →
        (p : ℤ) ^ k ∣ T t ∧ PadicInt.toZModPow r (T t : ℤ_[p]) = PadicInt.toZModPow r t) ∧
      ∀ x y : ℤ_[p], (p : ℤ_[p]) ^ k ∣ x - a →
        PadicInt.toZModPow 1 y = PadicInt.toZModPow 1 b → evalAt F x y = 0 →
        ∀ M : ℤ_[p][X][X], PadicInt.toZModPow r (evalAt M x y) =
          ↑((P M).eval (T (x - a))) := by
  classical
  let ρ := PadicInt.toZModPow (p := p) r
  obtain ⟨B, hB⟩ := exists_ordinate_polynomial F a b hunit r
  have hrep (t : ℤ_[p]) : ∃ z : ℤ, (p : ℤ_[p]) ^ k ∣ t →
      (p : ℤ) ^ k ∣ z ∧ ρ (z : ℤ_[p]) = ρ t := by
    by_cases ht : (p : ℤ_[p]) ^ k ∣ t
    · obtain ⟨z, hz⟩ := exists_parameter_representative k r ht
      exact ⟨z, fun _ ↦ hz⟩
    · exact ⟨0, fun h ↦ (ht h).elim⟩
  choose T hT using hrep
  have hpoly (M : ℤ_[p][X][X]) : ∃ P : ℤ[X],
      P.map (Int.castRingHom (ZMod (p ^ r))) = (substitute M a B).map ρ :=
    Polynomial.map_surjective _ ZMod.intCast_surjective _
  choose P hP using hpoly
  refine ⟨T, P, hT, fun x y hx hy hroot M ↦ ?_⟩
  have hx₁ : (p : ℤ_[p]) ∣ x - a := (dvd_pow_self _ (Nat.ne_of_gt hk)).trans hx
  have ha : a + (x - a) = x := by rw [add_comm, sub_add_cancel]
  change ρ (evalAt M x y) = _
  calc
    ρ (evalAt M x y) = ρ ((substitute M a B).eval (x - a)) := by
      rw [eval_substitute, ha]
      exact evalAt_congr ρ M rfl (hB x y hx₁ hy hroot).symm
    _ = ((P M).map (Int.castRingHom (ZMod (p ^ r)))).eval (ρ (x - a)) := by
      rw [hP, eval_map, eval₂_at_apply]
    _ = (↑((P M).eval (T (x - a))) : ZMod (p ^ r)) := by
      rw [← (hT _ hx).2, map_intCast, eval_map]
      exact (P M).eval₂_at_apply (Int.castRingHom (ZMod (p ^ r))) (T (x - a))

/-- Finite coefficient arrays for integer-valued tests, in the form required by
`BranchEvaluationDivisor`. For the local determinant input take `r = k * m.choose 2`
and a square array. The same displacement representatives work in every row. -/
public theorem exists_finite_evaluation_congruences {m n k : ℕ} (hk : 1 ≤ k)
    (F : ℤ_[p][X][X]) (a b : ℤ_[p]) (hunit : IsUnit (evalAt F.derivative a b)) (r : ℕ)
    (x y : Fin n → ℤ_[p]) (hx : ∀ j, (p : ℤ_[p]) ^ k ∣ x j - a)
    (hy : ∀ j, PadicInt.toZModPow 1 (y j) = PadicInt.toZModPow 1 b)
    (hroot : ∀ j, evalAt F (x j) (y j) = 0)
    (M : Fin m → ℤ_[p][X][X]) (A : Fin m → Fin n → ℤ)
    (hA : ∀ i j, (A i j : ℤ_[p]) = evalAt (M i) (x j) (y j)) :
    ∃ (d : ℕ) (c : Fin d → Fin m → ℤ) (t : Fin n → ℤ),
      (∀ j, (↑(p ^ k) : ℤ) ∣ t j ∧
        PadicInt.toZModPow r (t j : ℤ_[p]) = PadicInt.toZModPow r (x j - a)) ∧
      ∀ i j, A i j ≡ (∑ l : Fin d, t j ^ (l : ℕ) * c l i) [ZMOD ↑(p ^ r)] := by
  obtain ⟨T, P, hT, hP⟩ := exists_integral_evaluation F a b hunit hk r
  let d := (Finset.univ.sup fun i ↦ (P (M i)).natDegree) + 1
  let t (j : Fin n) := T (x j - a)
  refine ⟨d, fun l i ↦ (P (M i)).coeff l, t, fun j ↦ ?_, fun i j ↦ ?_⟩
  · simpa only [Nat.cast_pow] using hT _ (hx j)
  · have hd : (P (M i)).natDegree < d :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun i ↦ (P (M i)).natDegree) (Finset.mem_univ i))
    have heval : (P (M i)).eval (t j) = ∑ l : Fin d, t j ^ (l : ℕ) * (P (M i)).coeff l := by
      rw [eval_eq_sum_range' hd,
        Fin.sum_univ_eq_sum_range (fun l : ℕ ↦ t j ^ l * (P (M i)).coeff l)]
      exact Finset.sum_congr rfl (fun l _ ↦ mul_comm _ _)
    rw [← heval, ← ZMod.intCast_eq_intCast_iff]
    simpa only [← hA i j, map_intCast] using hP (x j) (y j) (hx j) (hy j) (hroot j) (M i)

end SmoothBranchEvaluation
