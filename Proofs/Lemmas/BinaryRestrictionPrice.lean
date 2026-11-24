module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The integral binary restriction price

Source: `2097cfaa:.godel/alice/cheap-filter-occupancy.md:37–56`, the integral
factorization and coefficient lower bound used in the joining-line coefficient
comparison, not the covolume estimate. In the source's coordinates `a = -f_B`
and `c = f_A`, so `a * c = -f_A * f_B`.

The hypotheses are on the nonzero integral homogeneous restriction and the two
primitive linears. Each root is evaluated at its nonzero integral projective
representative, without dehomogenizing. By homogeneity, vanishing is independent
of scaling the representative. The integral quotient is not normalized, so the
result applies to restrictions of any content. The priced coefficient is at
the least `x₂` index of the quotient.

Owning check session: `01a20ca9-0415-7de3-a7c2-ad7d2c76dee0`.
-/

namespace BinaryRestrictionPrice

open MvPolynomial

/-- Integral binary forms, with `x₁ = X 0` and `x₂ = X 1`. -/
public abbrev Form := MvPolynomial (Fin 2) ℤ

/-- The linear form `a x₁ + b x₂`. -/
public noncomputable def linear (a b : ℤ) : Form := C a * X 0 + C b * X 1

/-- The exponent vector of `x₁ ^ m * x₂ ^ n`. -/
public noncomputable def exponents (m n : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 m + Finsupp.single 1 n

@[simp] private theorem exponents_zero (m n : ℕ) : exponents m n 0 = m := by
  simp [exponents]

@[simp] private theorem exponents_one (m n : ℕ) : exponents m n 1 = n := by
  simp [exponents]

private theorem degree_eq (s : Fin 2 →₀ ℕ) : s.degree = s 0 + s 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem degree_of_coeff {P : Form} {n : ℕ} {s : Fin 2 →₀ ℕ}
    (hP : P.IsHomogeneous n) (hs : P.coeff s ≠ 0) : s.degree = n := by
  rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
  exact hP hs

private theorem linear_homogeneous (a b : ℤ) : (linear a b).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X a 0).add (isHomogeneous_C_mul_X b 1)

private theorem eval_linear (x : Fin 2 → ℤ) (a b : ℤ) :
    eval x (linear a b) = a * x 0 + b * x 1 := by
  simp [linear]

private theorem aeval_linear_linear (a b u v s t : ℤ) :
    aeval ![linear u v, linear s t] (linear a b) =
      linear (a * u + b * s) (a * v + b * t) := by
  simp only [linear, map_add, map_mul, aeval_C, algebraMap_eq, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private def axis (j : Fin 2) (k : Fin 2) : ℤ := if k = j then 1 else 0

/-- On a homogeneous form, evaluation at a coordinate vector reads a single coefficient. -/
private theorem eval_axis {P : Form} {n : ℕ} (hP : P.IsHomogeneous n) (j : Fin 2) :
    P.eval (axis j) = P.coeff (Finsupp.single j n) := by
  classical
  let d := Finsupp.single j n
  calc
    _ = ∑ s ∈ P.support, eval (axis j) (monomial s (P.coeff s)) := by
      conv_lhs => rw [P.as_sum]
      rw [map_sum]
    _ = eval (axis j) (monomial d (P.coeff d)) := by
      apply Finset.sum_eq_single d
      · intro s hs hsd
        have hdeg := degree_of_coeff hP (mem_support_iff.mp hs)
        have hex : ∃ k, k ≠ j ∧ s k ≠ 0 := by
          by_contra! hz
          have he : s = Finsupp.single j (s j) := by
            apply Finsupp.ext
            intro k
            by_cases hk : k = j
            · subst k
              simp
            · rw [Finsupp.single_eq_of_ne hk]
              exact hz k hk
          have hsn : s j = n := calc
            _ = (Finsupp.single j (s j)).degree := (Finsupp.degree_single j (s j)).symm
            _ = s.degree := congrArg Finsupp.degree he.symm
            _ = n := hdeg
          exact hsd (he.trans (congrArg (Finsupp.single j) hsn))
        obtain ⟨k, hk, hsk⟩ := hex
        rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
        have hp : ∏ i : Fin 2, axis j i ^ s i = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) (by simp [axis, hk, zero_pow hsk])
        rw [hp, mul_zero]
      · intro hd
        rw [eval_monomial, notMem_support_iff.mp hd, zero_mul]
    _ = _ := by simp [d, eval_monomial, Finsupp.prod_single_index, axis]

/-- Vanishing at `(0, 1)` lets us take one `x₁` out of every term, over `ℤ`. -/
private theorem factor_X {P : Form} {n : ℕ} (hP : P.IsHomogeneous n) (hne : P ≠ 0)
    (hz : P.eval (axis 1) = 0) :
    1 ≤ n ∧ ∃ Q : Form, Q.IsHomogeneous (n - 1) ∧ P = X 0 * Q := by
  classical
  have h0 (s : Fin 2 →₀ ℕ) (hs : s ∈ P.support) : 1 ≤ s 0 := by
    have hdeg := degree_of_coeff hP (mem_support_iff.mp hs)
    rw [degree_eq] at hdeg
    by_contra! h
    have hz0 : s 0 = 0 := by omega
    have hz1 : s 1 = n := by omega
    have he : s = Finsupp.single 1 n := by
      apply Finsupp.ext
      rw [Fin.forall_fin_two]
      simp [hz0, hz1]
    exact (mem_support_iff.mp hs) (by rwa [he, ← eval_axis hP])
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hne
  have hn : 1 ≤ n := by
    have hd := degree_of_coeff hP hs
    rw [degree_eq] at hd
    have := h0 s (mem_support_iff.mpr hs)
    omega
  let k : Fin 2 →₀ ℕ := Finsupp.single 0 1
  refine ⟨hn, ∑ s ∈ P.support, monomial (s - k) (P.coeff s), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro s hs
    apply isHomogeneous_monomial
    have hdeg := degree_of_coeff hP (mem_support_iff.mp hs)
    have hx := h0 s hs
    rw [degree_eq] at hdeg ⊢
    simp only [Finsupp.tsub_apply]
    have hk0 : k 0 = 1 := by simp [k]
    have hk1 : k 1 = 0 := by simp [k]
    omega
  · rw [Finset.mul_sum]
    calc
      P = ∑ s ∈ P.support, monomial s (P.coeff s) := P.as_sum
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [X, ← show k = Finsupp.single 0 1 from rfl, monomial_mul_monomial, one_mul]
        rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (h0 s hs) : k ≤ s)]

/-- Complete a primitive integral linear form to a unimodular coordinate system. -/
private theorem factor_linear {P : Form} {n : ℕ} {a b : ℤ} (hP : P.IsHomogeneous n)
    (hne : P ≠ 0) (hprim : a.gcd b = 1) (hz : P.eval ![-b, a] = 0) :
    1 ≤ n ∧ ∃ Q : Form, Q ≠ 0 ∧ Q.IsHomogeneous (n - 1) ∧ P = linear a b * Q := by
  let u := a.gcdA b
  let v := a.gcdB b
  have huv : a * u + b * v = 1 := by
    simpa [hprim] using (Int.gcd_eq_gcd_ab a b).symm
  let T : Form →ₐ[ℤ] Form := aeval ![linear u (-b), linear v a]
  let S : Form →ₐ[ℤ] Form := aeval ![linear a b, linear (-v) u]
  have hST : S.comp T = AlgHom.id ℤ Form := by
    apply algHom_ext
    intro i
    fin_cases i
    · have hd : u * a + -b * -v = 1 := by rw [← huv]; ring
      change S (T (X 0)) = X 0
      simp only [T, S, aeval_X, Matrix.cons_val_zero, aeval_linear_linear, hd]
      rw [show u * b + -b * u = 0 by ring]
      simp [linear]
    · have hd : v * b + a * u = 1 := by rw [← huv]; ring
      change S (T (X 1)) = X 1
      simp only [T, S, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero, aeval_linear_linear, hd]
      rw [show v * a + a * -v = 0 by ring]
      simp [linear]
  have hinv (F : Form) : S (T F) = F := DFunLike.congr_fun hST F
  have hTP : (T P).IsHomogeneous n := by
    have hT (i : Fin 2) : (![linear u (-b), linear v a] i).IsHomogeneous 1 := by
      fin_cases i <;> exact linear_homogeneous _ _
    simpa only [one_mul] using hP.aeval _ hT
  have hTne : T P ≠ 0 := by
    intro h
    exact hne (by rw [← hinv P, h, map_zero])
  have hTz : (T P).eval (axis 1) = 0 := by
    have hvec : (fun i : Fin 2 ↦ eval (axis 1) (![linear u (-b), linear v a] i)) = ![-b, a] := by
      funext i
      fin_cases i <;> simp [eval_linear, axis]
    change eval (axis 1) (aeval ![linear u (-b), linear v a] P) = 0
    rw [← aeval_eq_eval, comp_aeval_apply]
    simpa only [aeval_eq_eval, hvec] using hz
  obtain ⟨hn, Q, hQ, hfact⟩ := factor_X hTP hTne hTz
  have hS (i : Fin 2) : (![linear a b, linear (-v) u] i).IsHomogeneous 1 := by
    fin_cases i <;> exact linear_homogeneous _ _
  have hfact' : P = linear a b * S Q := by
    rw [← hinv P, hfact, map_mul]
    simp [S]
  refine ⟨hn, S Q, ?_, ?_, hfact'⟩
  · intro h
    exact hne (by rw [hfact', h, mul_zero])
  · simpa only [one_mul] using hQ.aeval _ hS

/-- In the first possible `x₂` slot of `Q`, only the `x₂`-free term of `P` contributes. -/
private theorem coeff_mul_first {P Q : Form} {m n i : ℕ} (hP : P.IsHomogeneous m)
    (hi : i ≤ n) (hmin : ∀ v : Fin 2 →₀ ℕ, v 1 < i → Q.coeff v = 0) :
    (P * Q).coeff (exponents (m + n - i) i) =
      P.coeff (Finsupp.single 0 m) * Q.coeff (exponents (n - i) i) := by
  classical
  let s := Finsupp.single (0 : Fin 2) m
  let t := exponents (n - i) i
  have hsum : s + t = exponents (m + n - i) i := by
    apply Finsupp.ext
    rw [Fin.forall_fin_two]
    constructor
    · simp [s, t, Finsupp.add_apply]; omega
    · simp [s, t, Finsupp.add_apply]
  rw [coeff_mul, Finset.sum_eq_single (s, t)]
  · rintro ⟨u, v⟩ huv hne
    rw [Finset.mem_antidiagonal] at huv
    apply mul_eq_zero.mpr
    by_cases hv : Q.coeff v = 0
    · exact Or.inr hv
    left
    by_contra hu
    have hindex := congrArg (fun w : Fin 2 →₀ ℕ ↦ w 1) huv
    simp only [Finsupp.add_apply, exponents_one] at hindex
    have hvge : i ≤ v 1 := le_of_not_gt (fun h ↦ hv (hmin v h))
    have hu0 : u 1 = 0 := by omega
    have hdeg := degree_of_coeff hP hu
    rw [degree_eq, hu0, add_zero] at hdeg
    have hus : u = s := by
      apply Finsupp.ext
      rw [Fin.forall_fin_two]
      simp [s, hdeg, hu0]
    have hvt : v = t := add_left_cancel ((show s + v = _ by rwa [← hus]).trans hsum.symm)
    exact hne (by rw [hus, hvt])
  · intro h
    exact False.elim (h (Finset.mem_antidiagonal.mpr hsum))

/-- If the integral form `D` vanishes at the two distinct projective roots
`[-b : a]` and `[-d : c]` of the primitive linears, it factors as their product
with a nonzero integral homogeneous quotient. The roots are represented
without choosing an affine chart. In the least `x₂` slot of the quotient,
the coefficient of `D` is exactly `a * c` times the quotient coefficient. -/
public theorem restriction_price {D : Form} {e : ℕ} {a b c d : ℤ}
    (hD : D.IsHomogeneous e) (hDne : D ≠ 0)
    (hprimU : a.gcd b = 1) (hprimW : c.gcd d = 1)
    (hdet : a * d - b * c ≠ 0) (hac : a * c ≠ 0)
    (hU : D.eval ![-b, a] = 0) (hW : D.eval ![-d, c] = 0) :
    2 ≤ e ∧ ∃ H : Form, H ≠ 0 ∧ H.IsHomogeneous (e - 2) ∧
      D = linear a b * linear c d * H ∧
      ∃ i ≤ e - 2, H.coeff (exponents (e - 2 - i) i) ≠ 0 ∧
        (∀ s : Fin 2 →₀ ℕ, s 1 < i → H.coeff s = 0) ∧
        D.coeff (exponents (e - i) i) = (a * c) * H.coeff (exponents (e - 2 - i) i) ∧
        |a * c| ≤ |D.coeff (exponents (e - i) i)| := by
  classical
  obtain ⟨he, Q, hQne, hQhom, hDQ⟩ := factor_linear hD hDne hprimU hU
  have hUatW : (linear a b).eval ![-d, c] ≠ 0 := by
    rw [eval_linear]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show a * -d + b * c = -(a * d - b * c) by ring]
    exact neg_ne_zero.mpr hdet
  have hQatW : Q.eval ![-d, c] = 0 := by
    rw [hDQ, map_mul] at hW
    exact (mul_eq_zero.mp hW).resolve_left hUatW
  obtain ⟨he', H, hHne, hHhom, hQH⟩ := factor_linear hQhom hQne hprimW hQatW
  have he2 : 2 ≤ e := by omega
  have hH2 : H.IsHomogeneous (e - 2) := by
    rwa [show e - 2 = (e - 1) - 1 by omega]
  have hfact : D = linear a b * linear c d * H := by rw [hDQ, hQH, mul_assoc]
  have hsome : ∃ j : ℕ, ∃ s : Fin 2 →₀ ℕ, s 1 = j ∧ H.coeff s ≠ 0 := by
    obtain ⟨s, hs⟩ := exists_coeff_ne_zero hHne
    exact ⟨s 1, s, rfl, hs⟩
  let i := Nat.find hsome
  obtain ⟨t, ht, htne⟩ := Nat.find_spec hsome
  have htdeg := degree_of_coeff hH2 htne
  rw [degree_eq] at htdeg
  have hi : i ≤ e - 2 := by omega
  have hte : t = exponents (e - 2 - i) i := by
    apply Finsupp.ext
    rw [Fin.forall_fin_two]
    simp only [exponents_zero, exponents_one, ht]
    omega
  have hmin (s : Fin 2 →₀ ℕ) (hs : s 1 < i) : H.coeff s = 0 := by
    by_contra h
    have hle : i ≤ s 1 := Nat.find_min' hsome ⟨s, rfl, h⟩
    omega
  have hUW : (linear a b * linear c d).IsHomogeneous 2 :=
    (linear_homogeneous a b).mul (linear_homogeneous c d)
  have hcUW : (linear a b * linear c d).coeff (Finsupp.single 0 2) = a * c := by
    rw [← eval_axis hUW, map_mul, eval_linear, eval_linear]
    simp [axis]
  have hcoeff : D.coeff (exponents (e - i) i) =
      (a * c) * H.coeff (exponents (e - 2 - i) i) := calc
    _ = (linear a b * linear c d * H).coeff (exponents (2 + (e - 2) - i) i) := by
      rw [hfact, show 2 + (e - 2) - i = e - i by omega]
    _ = _ := (coeff_mul_first hUW hi hmin).trans (by rw [hcUW])
  rw [hte] at htne
  refine ⟨he2, H, hHne, hH2, hfact, i, hi, htne, hmin, hcoeff, ?_⟩
  rw [hcoeff, abs_mul (a * c)]
  exact le_mul_of_one_le_right (abs_pos.mpr hac).le (Int.one_le_abs htne)

end BinaryRestrictionPrice
