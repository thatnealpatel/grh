module

public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Ring

/-!
# Uniform recovery from one frozen plane vector

Source: `3d2886df:.godel/alice/common-plane-vector.md:9–31` (introduced at
`a99dda33`), with the original split data from
`25765be8:.godel/alice/normal-factor-minors.md`. Reconciled at `1de21475`.

We use the untransformed normal `(a,b,c)` and the original integral coordinates
`(m,x,y)`. A represented split supplies the arithmetic data for the full ordered
factors `A,B` with `AB = g`; no lattice membership modulo the larger original
moduli `P,Q` is imposed on the vector. Fix one nonzero vector on the reference
plane and one ordered pair of filters. Every represented split with those filters
and in the strict dot-product window has the same vector on its plane, and its
full factors divide the two fixed nonzero recovery integers. The reference
normal's two transverse coordinates are taken nonzero, as they are in the source.
The choice of filters, the geometric bound giving the window, and the asymptotic
count are outside this module.

Owning check session: `01a20c3b-0de7-75d0-b4f0-194be0854305`.
-/

namespace FrozenFilterRecovery

/-- Arithmetic data of a represented split on the original normal. -/
public structure SplitNormal (F q A B : ℕ) (a b c : ℤ) : Prop where
  factors_coprime : A.Coprime B
  a_coprime : IsCoprime a ((A : ℤ) * B)
  dvd_c : (A : ℤ) ∣ c
  dvd_b : (B : ℤ) ∣ b
  dvd_combination : (A : ℤ) * B ∣ (q : ℤ) * a + (F : ℤ) * (b + c)

/-- The integral pairing on the original, unscaled coordinates. -/
@[expose] public def normalDot (a b c m x y : ℤ) : ℤ := a * m + b * x + c * y

/-- The two annihilator congruences hold for every integer vector, without
assuming orthogonality or either primal congruence. -/
public theorem annihilators {F q A B : ℕ} {a b c : ℤ}
    (hs : SplitNormal F q A B a b c) (m x y : ℤ) :
    ((F : ℤ) * normalDot a b c m x y ≡ a * ((F : ℤ) * m - (q : ℤ) * x) [ZMOD A]) ∧
    ((F : ℤ) * normalDot a b c m x y ≡ a * ((F : ℤ) * m - (q : ℤ) * y) [ZMOD B]) := by
  have hA := (dvd_mul_right (A : ℤ) (B : ℤ)).trans hs.dvd_combination
  have hB := (dvd_mul_left (B : ℤ) (A : ℤ)).trans hs.dvd_combination
  constructor <;> apply Int.modEq_iff_dvd.mpr
  · calc
      _ ∣ (F : ℤ) * c * (x - y) - x * ((q : ℤ) * a + (F : ℤ) * (b + c)) :=
        dvd_sub ((hs.dvd_c.mul_left _).mul_right _) (hA.mul_left _)
      _ = _ := by unfold normalDot; ring
  · calc
      _ ∣ (F : ℤ) * b * (y - x) - y * ((q : ℤ) * a + (F : ℤ) * (b + c)) :=
        dvd_sub ((hs.dvd_b.mul_left _).mul_right _) (hB.mul_left _)
      _ = _ := by unfold normalDot; ring

/-- On the saturated integral plane, cancel the normal's first coordinate
modulo each full factor. -/
public theorem recover_of_orthogonal {F q A B : ℕ} {a b c m x y : ℤ}
    (hs : SplitNormal F q A B a b c) (horth : normalDot a b c m x y = 0) :
    ((A : ℤ) ∣ (F : ℤ) * m - (q : ℤ) * x) ∧
    ((B : ℤ) ∣ (F : ℤ) * m - (q : ℤ) * y) := by
  obtain ⟨hA, hB⟩ := annihilators hs m x y
  rw [horth, mul_zero] at hA hB
  exact ⟨hs.a_coprime.of_mul_right_left.symm.dvd_of_dvd_mul_left (hA.dvd_iff.mp (dvd_zero _)),
    hs.a_coprime.of_mul_right_right.symm.dvd_of_dvd_mul_left (hB.dvd_iff.mp (dvd_zero _))⟩

private theorem coords_zero_of_recovery_zero {F q : ℕ} {m t : ℤ} (hFq : F.Coprime q)
    (ht : |t| < (F : ℤ)) (h : (F : ℤ) * m - (q : ℤ) * t = 0) : m = 0 ∧ t = 0 := by
  have heq := sub_eq_zero.mp h
  have hdvd : (F : ℤ) ∣ (q : ℤ) * t := ⟨m, heq.symm⟩
  have ht0 := Int.eq_zero_of_abs_lt_dvd (hFq.isCoprime.dvd_of_dvd_mul_left hdvd) ht
  rw [ht0, mul_zero] at heq
  have hF0 : (F : ℤ) ≠ 0 := ne_of_gt ((abs_nonneg t).trans_lt ht)
  exact ⟨(mul_eq_zero.mp heq).resolve_left hF0, ht0⟩

/-- One nonzero vector orthogonal to a reference normal recovers every split
with the same filters in the strict window. Its participation in the filter is
proved from reference orthogonality, not assumed. -/
public theorem uniform_filter_recovery
    {F q fA fB Aref Bref : ℕ} {aRef bRef cRef m x y : ℤ}
    (href : SplitNormal F q Aref Bref aRef bRef cRef)
    (hfAref : fA ∣ Aref) (hfBref : fB ∣ Bref) (hdF : (fA * fB).Coprime F)
    (horth : normalDot aRef bRef cRef m x y = 0) (hu : ¬ (m = 0 ∧ x = 0 ∧ y = 0))
    (hFq : F.Coprime q) (hx : |x| < (F : ℤ)) (hy : |y| < (F : ℤ))
    (hbref : bRef ≠ 0) (hcref : cRef ≠ 0) :
    (∀ {A B : ℕ} {a b c : ℤ}, SplitNormal F q A B a b c →
      fA ∣ A → fB ∣ B → |normalDot a b c m x y| < (↑(fA * fB) : ℤ) →
      normalDot a b c m x y = 0 ∧
      ((A : ℤ) ∣ (F : ℤ) * m - (q : ℤ) * x) ∧
      ((B : ℤ) ∣ (F : ℤ) * m - (q : ℤ) * y)) ∧
    (F : ℤ) * m - (q : ℤ) * x ≠ 0 ∧ (F : ℤ) * m - (q : ℤ) * y ≠ 0 := by
  obtain ⟨hAref, hBref⟩ := recover_of_orthogonal href horth
  have hfx := (Int.natCast_dvd_natCast.mpr hfAref).trans hAref
  have hfy := (Int.natCast_dvd_natCast.mpr hfBref).trans hBref
  refine ⟨?_, ?_, ?_⟩
  · intro A B a b c hs hfA hfB hwindow
    obtain ⟨hA, hB⟩ := annihilators hs m x y
    have hleft := (hA.of_dvd (Int.natCast_dvd_natCast.mpr hfA)).dvd_iff.mpr (hfx.mul_left a)
    have hright := (hB.of_dvd (Int.natCast_dvd_natCast.mpr hfB)).dvd_iff.mpr (hfy.mul_left a)
    have hcop := (Nat.Coprime.of_dvd hfA hfB hs.factors_coprime).isCoprime
    have hprod : (↑(fA * fB) : ℤ) ∣ (F : ℤ) * normalDot a b c m x y := by
      rw [Nat.cast_mul]
      exact hcop.mul_dvd hleft hright
    have hzero := Int.eq_zero_of_abs_lt_dvd (hdF.isCoprime.dvd_of_dvd_mul_left hprod) hwindow
    exact ⟨hzero, recover_of_orthogonal hs hzero⟩
  · intro h
    obtain ⟨hm, hx0⟩ := coords_zero_of_recovery_zero hFq hx h
    have hcy : cRef * y = 0 := by simpa only [normalDot, hm, hx0, mul_zero, zero_add] using horth
    exact hu ⟨hm, hx0, (mul_eq_zero.mp hcy).resolve_left hcref⟩
  · intro h
    obtain ⟨hm, hy0⟩ := coords_zero_of_recovery_zero hFq hy h
    have hbx : bRef * x = 0 := by
      simpa only [normalDot, hm, hy0, mul_zero, zero_add, add_zero] using horth
    exact hu ⟨hm, (mul_eq_zero.mp hbx).resolve_left hbref, hy0⟩

end FrozenFilterRecovery
