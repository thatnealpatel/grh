module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Joint outside-radical accounting

Source: `35960cb0:.godel/alice/two-ratio-radical.md:3–24`, unchanged at
`5ab1b80f` and `0648ae05`. This is the arithmetic used in the retained-triple
price: for one fixed omitted pool and reduced positive ratios `z = n/w` and
`S = x/y`, compare their outside prime supports with that of `L = S/z`.
The overlap contributes once beyond the union, and exact cancellation costs
one further copy. The distinct cancelled primes have product dividing
`gcd(n,x) * gcd(w,y)`, giving their base-`q` log price. No pool size bound is
needed for these identities. This does not prove the overlap estimates, the
hidden-factor bound, or the asymptotic triple count.

Owning check session: `01a20ce0-1582-79d6-b657-1b3239837bf7`.
-/

namespace JointOutsideRadical

private theorem valuation_num_den {p : ℕ} (hp : p.Prime) (u : ℚ) :
    padicValRat p u =
      (u.num.natAbs.factorization p : ℤ) - (u.den.factorization p : ℤ) := by
  simp only [padicValRat_def, padicValInt, Nat.multiplicity_eq_factorization hp]

/-- The signed prime valuation in reduced natural coordinates. -/
public theorem valuation_reduced_fraction {p n w : ℕ} (hp : p.Prime)
    (hw : 0 < w) (hcop : n.Coprime w) :
    padicValRat p ((n : ℚ) / w) = (n.factorization p : ℤ) - (w.factorization p : ℤ) := by
  have hfrac : mkRat (n : ℤ) w = (n : ℚ) / w := by
    rw [Rat.mkRat_eq_div, Rat.intCast_natCast]
  have hgcd : w.gcd n = 1 := hcop.symm.gcd_eq_one
  rw [← hfrac, valuation_num_den hp, Rat.num_mkRat, Rat.den_mkRat]
  simp [hw.ne', hgcd]

/-- The signed valuation of the actual quotient `S/z`, with subtraction in `ℤ`. -/
public theorem valuation_div {p : ℕ} (hp : p.Prime) {z S : ℚ}
    (hz : 0 < z) (hS : 0 < S) :
    padicValRat p (S / z) = padicValRat p S - padicValRat p z := by
  let : Fact p.Prime := ⟨hp⟩
  exact padicValRat.div hS.ne' hz.ne'

/-- The finite set of primes outside `P` with nonzero signed valuation in `u`. -/
@[expose] public noncomputable def support (P : Finset ℕ) (u : ℚ) : Finset ℕ := by
  classical
  exact (u.num.natAbs.primeFactors ∪ u.den.primeFactors).filter
    (fun p ↦ p ∉ P ∧ padicValRat p u ≠ 0)

/-- The primes in both outside supports. -/
@[expose] public noncomputable def overlap (P : Finset ℕ) (z S : ℚ) : Finset ℕ :=
  support P z ∩ support P S

/-- The primes in the overlap where the two nonzero signed valuations agree. -/
@[expose] public noncomputable def cancellation (P : Finset ℕ) (z S : ℚ) : Finset ℕ := by
  classical
  exact (overlap P z S).filter (fun p ↦ padicValRat p S = padicValRat p z)

/-- The sum of the base-`q` logarithms of the elements. -/
@[expose] public noncomputable def weight (q : ℝ) (E : Finset ℕ) : ℝ :=
  ∑ p ∈ E, Real.log (p : ℝ) / Real.log q

/-- The log weight of the outside radical with the fixed omitted pool `P`. -/
@[expose] public noncomputable def radicalWeight (q : ℝ) (P : Finset ℕ) (u : ℚ) : ℝ :=
  weight q (support P u)

public theorem mem_support {p : ℕ} {P : Finset ℕ} {u : ℚ} :
    p ∈ support P u ↔ p.Prime ∧ p ∉ P ∧ padicValRat p u ≠ 0 := by
  simp only [support, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hm, hP, hv⟩
    exact ⟨hm.elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors, hP, hv⟩
  · rintro ⟨hp, hP, hv⟩
    refine ⟨?_, hP, hv⟩
    by_contra! h
    have hzero {m : ℕ} (hm : p ∉ m.primeFactors) : m.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      rwa [Nat.support_factorization]
    exact hv (by simp [valuation_num_den hp, hzero h.1, hzero h.2])

/-- The quotient retains all primes in the union except exact cancellations. -/
public theorem support_div (P : Finset ℕ) {z S : ℚ} (hz : 0 < z) (hS : 0 < S) :
    support P (S / z) = (support P z ∪ support P S) \ cancellation P z S := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_union, cancellation, overlap, Finset.mem_filter,
    Finset.mem_inter, mem_support]
  by_cases hp : p.Prime
  · rw [valuation_div hp hz hS, sub_ne_zero]
    by_cases hP : p ∈ P
    · simp [hP]
    · by_cases hz₀ : padicValRat p z = 0 <;>
        by_cases hS₀ : padicValRat p S = 0 <;>
        simp [hp, hP, hz₀, hS₀, eq_comm]
  · simp [hp]

/-- The sum of the two radical weights includes one extra copy of the overlap
and one further copy of the cancellation set, relative to the quotient. -/
public theorem radicalWeight_add (q : ℝ) (P : Finset ℕ) {z S : ℚ}
    (hz : 0 < z) (hS : 0 < S) :
    radicalWeight q P z + radicalWeight q P S =
      radicalWeight q P (S / z) + weight q (overlap P z S) + weight q (cancellation P z S) := by
  have hsubset : cancellation P z S ⊆ support P z ∪ support P S := by
    intro p hp
    simp only [cancellation, overlap, Finset.mem_filter, Finset.mem_inter] at hp
    exact Finset.mem_union_left _ hp.1.1
  calc
    radicalWeight q P z + radicalWeight q P S =
        weight q (support P z ∪ support P S) + weight q (overlap P z S) :=
      (Finset.sum_union_inter (s₁ := support P z) (s₂ := support P S)
        (f := fun p : ℕ ↦ Real.log (p : ℝ) / Real.log q)).symm
    _ = (weight q ((support P z ∪ support P S) \ cancellation P z S) +
        weight q (cancellation P z S)) + weight q (overlap P z S) :=
      congrArg (· + weight q (overlap P z S)) (Finset.sum_sdiff hsubset).symm
    _ = _ := by
      rw [← support_div P hz hS]
      exact add_right_comm _ _ _

/-- On a finite prime set, the weight is the base-`q` log of the product of the
primes, also when the set is empty. -/
public theorem weight_eq_logb_prod (q : ℝ) {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) :
    weight q E = Real.logb q ((∏ p ∈ E, p : ℕ) : ℝ) := by
  rw [weight, Real.logb, Nat.cast_prod, Real.log_prod, Finset.sum_div]
  exact fun p hp ↦ Nat.cast_ne_zero.mpr (hE p hp).ne_zero

private theorem valuation_sign {p n w : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hw : 0 < w) (hcop : n.Coprime w) :
    (0 < padicValRat p ((n : ℚ) / w) ↔ p ∣ n) ∧
      (padicValRat p ((n : ℚ) / w) < 0 ↔ p ∣ w) := by
  have hnot : ¬(p ∣ n ∧ p ∣ w) := by
    rintro ⟨hpn, hpw⟩
    have hpg := Nat.dvd_gcd hpn hpw
    rw [hcop.gcd_eq_one] at hpg
    exact hp.not_dvd_one hpg
  rw [valuation_reduced_fraction hp hw hcop]
  constructor
  · constructor
    · intro h
      by_contra hpn
      have hn₀ := Nat.factorization_eq_zero_of_not_dvd hpn
      omega
    · intro hpn
      have hw₀ := Nat.factorization_eq_zero_of_not_dvd (fun hpw ↦ hnot ⟨hpn, hpw⟩)
      have hnpos := hp.factorization_pos_of_dvd hn.ne' hpn
      omega
  · constructor
    · intro h
      by_contra hpw
      have hw₀ := Nat.factorization_eq_zero_of_not_dvd hpw
      omega
    · intro hpw
      have hn₀ := Nat.factorization_eq_zero_of_not_dvd (fun hpn ↦ hnot ⟨hpn, hpw⟩)
      have hwpos := hp.factorization_pos_of_dvd hw.ne' hpw
      omega

/-- The cancellation product is squarefree and divides the product of the
numerator gcd and denominator gcd. Its logarithmic price is bounded by the
base-`q` log of this gcd product. -/
public theorem cancellation_gcd_price (P : Finset ℕ) {q : ℝ} (hq : 1 < q)
    {n w x y : ℕ} (hn : 0 < n) (hw : 0 < w) (hx : 0 < x) (hy : 0 < y)
    (hzw : n.Coprime w) (hSy : x.Coprime y) :
    let D := cancellation P ((n : ℚ) / w) ((x : ℚ) / y)
    let J := n.gcd x * w.gcd y
    Squarefree (∏ p ∈ D, p) ∧ (∏ p ∈ D, p) ∣ J ∧ weight q D ≤ Real.logb q (J : ℝ) := by
  dsimp only
  let D := cancellation P ((n : ℚ) / w) ((x : ℚ) / y)
  let J := n.gcd x * w.gcd y
  have hJ : 0 < J := Nat.mul_pos (Nat.gcd_pos_of_pos_left x hn) (Nat.gcd_pos_of_pos_left y hw)
  have hsub : D ⊆ J.primeFactors := by
    intro p hpD
    simp only [D, cancellation, overlap, Finset.mem_filter, Finset.mem_inter, mem_support] at hpD
    obtain ⟨⟨⟨hp, _, hz₀⟩, _⟩, heq⟩ := hpD
    have hsignZ := valuation_sign hp hn hw hzw
    have hsignS := valuation_sign hp hx hy hSy
    have hpJ : p ∣ J := by
      rcases lt_or_gt_of_ne hz₀ with hneg | hpos
      · have hpw := hsignZ.2.mp hneg
        have hpy := hsignS.2.mp (heq.symm ▸ hneg)
        exact (Nat.dvd_gcd hpw hpy).trans (dvd_mul_left _ _)
      · have hpn := hsignZ.1.mp hpos
        have hpx := hsignS.1.mp (heq.symm ▸ hpos)
        exact (Nat.dvd_gcd hpn hpx).trans (dvd_mul_right _ _)
    exact Nat.mem_primeFactors.mpr ⟨hp, hpJ, hJ.ne'⟩
  have hprime (p : ℕ) (hp : p ∈ D) : p.Prime := Nat.prime_of_mem_primeFactors (hsub hp)
  have hprod := Finset.prod_dvd_prod_of_subset D J.primeFactors id hsub
  have hdvd : (∏ p ∈ D, p) ∣ J := hprod.trans (Nat.prod_primeFactors_dvd J)
  refine ⟨Squarefree.squarefree_of_dvd hprod (Nat.squarefree_prod_primeFactors J), hdvd, ?_⟩
  change weight q D ≤ Real.logb q (J : ℝ)
  rw [weight_eq_logb_prod q hprime]
  have hpos : 0 < ∏ p ∈ D, p := Finset.prod_pos fun p hp ↦ (hprime p hp).pos
  exact (Real.logb_le_logb hq (Nat.cast_pos.mpr hpos) (Nat.cast_pos.mpr hJ)).mpr
    (Nat.cast_le.mpr (Nat.le_of_dvd hJ hdvd))

/-- The joint accounting and gcd price on the same reduced coordinates and
with the same omitted pool for all three ratios. -/
public theorem joint_outside_radical (P : Finset ℕ) {q : ℝ} (hq : 1 < q)
    {n w x y : ℕ} (hn : 0 < n) (hw : 0 < w) (hx : 0 < x) (hy : 0 < y)
    (hzw : n.Coprime w) (hSy : x.Coprime y) :
    let z : ℚ := (n : ℚ) / w
    let S : ℚ := (x : ℚ) / y
    let L := S / z
    let I := overlap P z S
    let D := cancellation P z S
    let J := n.gcd x * w.gcd y
    support P L = (support P z ∪ support P S) \ D ∧
      radicalWeight q P z + radicalWeight q P S = radicalWeight q P L + weight q I + weight q D ∧
      Squarefree (∏ p ∈ D, p) ∧ (∏ p ∈ D, p) ∣ J ∧ weight q D ≤ Real.logb q (J : ℝ) := by
  have hz : 0 < (n : ℚ) / w := div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hw)
  have hS : 0 < (x : ℚ) / y := div_pos (Nat.cast_pos.mpr hx) (Nat.cast_pos.mpr hy)
  exact ⟨support_div P hz hS, radicalWeight_add q P hz hS,
    cancellation_gcd_price P hq hn hw hx hy hzw hSy⟩

end JointOutsideRadical
