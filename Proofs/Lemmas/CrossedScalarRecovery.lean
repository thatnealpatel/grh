module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar recovery after the crossed-direction count

Source: `79f24b34:.godel/alice/masked-gap-lcm.md:19–23`.
Consumer: `b6920957:.godel/alice/crossed-gap-filters.md:24–30`.

For fixed recovered rows, we count actual primitive pairs `(G, i)` for the
fixed affine relation `c = B * G + d * i`. We use the positive part of the
source box, not a count of all lattice points in the centered box. Every
eligible-smooth `c > 2R` has a crossing divisor `2R < f ≤ 2RX`. At fixed `f`
the pair count is at most `1 + 8RZ/(df)`. The distinct numerators therefore cost
at most the size of the explicit smooth-divisor menu times `1 + 4Z/d`.
This proves the finite scalar-recovery bound, not the asymptotic bound on the
menu size or the outer sum over recovered rows and dyadic boxes.

Owning check session: `01a20bcd-0340-73f5-9604-3b5724a0ee86`.
-/

open scoped BigOperators
open Finset

namespace CrossedScalarRecovery

/-- All prime factors, including those that occur with multiplicity, come from
the eligible set and are at most `X`. -/
@[expose] public def EligibleSmooth (eligible : ℕ → Prop) (X : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → eligible p ∧ (p : ℝ) ≤ X

private theorem crossing_prefix {T X : ℝ} (l : List ℕ) (a : ℕ) (ha : (a : ℝ) ≤ T)
    (hlt : T < ((a * l.prod : ℕ) : ℝ)) (hcap : ∀ p ∈ l, (p : ℝ) ≤ X) :
    ∃ f : ℕ, f ∣ a * l.prod ∧ T < (f : ℝ) ∧ (f : ℝ) ≤ T * X := by
  induction l generalizing a with
  | nil =>
    simp only [List.prod_nil, mul_one] at hlt
    exact (hlt.not_ge ha).elim
  | cons p l ih =>
    rw [List.prod_cons, ← mul_assoc] at hlt ⊢
    by_cases hcross : T < ((a * p : ℕ) : ℝ)
    · refine ⟨a * p, dvd_mul_right _ _, hcross, ?_⟩
      rw [Nat.cast_mul]
      exact mul_le_mul ha (hcap p (List.mem_cons_self ..)) (Nat.cast_nonneg p)
        ((Nat.cast_nonneg a).trans ha)
    · exact ih (a * p) (le_of_not_gt hcross) hlt (fun q hq => hcap q (List.mem_cons_of_mem _ hq))

/-- Multiply the prime factors of `n` in order, with multiplicity. The prefix
before the first crossing is at most `T`, so the overshoot is at most `X`. -/
public theorem exists_crossing_divisor {eligible : ℕ → Prop} {X T : ℝ} {n : ℕ}
    (hT : 1 ≤ T) (hn : T < (n : ℝ)) (hs : EligibleSmooth eligible X n) :
    ∃ f : ℕ, f ∣ n ∧ T < (f : ℝ) ∧ (f : ℝ) ≤ T * X ∧ EligibleSmooth eligible X f := by
  have hn0 : n ≠ 0 := by
    intro h
    simp only [h, Nat.cast_zero] at hn
    linarith
  have hprod : 1 * n.primeFactorsList.prod = n := by
    rw [one_mul, Nat.prod_primeFactorsList hn0]
  obtain ⟨f, hf, hTf, hfX⟩ := crossing_prefix n.primeFactorsList 1 (by simpa only [Nat.cast_one])
    (by rwa [hprod])
    (fun p hp => (hs p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)).2)
  rw [hprod] at hf
  exact ⟨f, hf, hTf, hfX, fun p hp hpf => hs p hp (hpf.trans hf)⟩

/-- Fixed affine numerator for a signed pair `(G, i)`. -/
@[expose] public def numerator (B d : ℤ) (x : ℤ × ℤ) : ℤ := B * x.1 + d * x.2

/-- The positive box, with primitivity on the original pair and coprimality
of the numerator with the fixed denominator. -/
public structure InBox (B d : ℤ) (R Z : ℝ) (x : ℤ × ℤ) : Prop where
  G_pos : 0 < x.1
  G_le : (x.1 : ℝ) ≤ 2 * R
  c_pos : 0 < numerator B d x
  c_le : (numerator B d x : ℝ) ≤ Z
  primitive : IsCoprime x.1 x.2
  coprime : IsCoprime d (numerator B d x)

/-- The conditions on the actual scalar recovery pairs for the final count. -/
@[expose] public def Admissible (eligible : ℕ → Prop) (B d : ℤ) (R Z X : ℝ)
    (x : ℤ × ℤ) : Prop :=
  InBox B d R Z x ∧ 2 * R < (numerator B d x : ℝ) ∧
    EligibleSmooth eligible X (numerator B d x).natAbs

private def det (B d : ℤ) (x y : ℤ × ℤ) : ℤ := x.1 * numerator B d y - y.1 * numerator B d x

private theorem det_eq (B d : ℤ) (x y : ℤ × ℤ) :
    det B d x y = d * (x.1 * y.2 - y.1 * x.2) := by
  unfold det numerator
  ring

private theorem eq_of_det_eq_zero {B d : ℤ} {R Z : ℝ} {x y : ℤ × ℤ}
    (hd : d ≠ 0) (hx : InBox B d R Z x) (hy : InBox B d R Z y)
    (hdet : det B d x y = 0) : x = y := by
  rw [det_eq] at hdet
  have hxy := (mul_eq_zero.mp hdet).resolve_left hd
  -- The first primitive pair gives an integral proportionality factor.
  obtain ⟨a, b, hab⟩ := hx.primitive
  let k := a * y.1 + b * y.2
  have h₁ : y.1 = k * x.1 := by
    dsimp only [k]
    linear_combination -y.1 * hab - b * hxy
  have h₂ : y.2 = k * x.2 := by
    dsimp only [k]
    linear_combination -y.2 * hab + a * hxy
  have hk := Int.isCoprime_iff_gcd_eq_one.mp hy.primitive
  rw [h₁, h₂, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hx.primitive, mul_one] at hk
  rcases Int.natAbs_eq_iff.mp hk with hk | hk
  · exact (Prod.ext (by simpa only [hk, Int.ofNat_one, one_mul] using h₁)
      (by simpa only [hk, Int.ofNat_one, one_mul] using h₂)).symm
  · rw [hk, Int.ofNat_one, neg_mul, one_mul] at h₁
    linarith only [h₁, hx.G_pos, hy.G_pos]

private theorem mul_dvd_det {B d : ℤ} {f : ℕ} {x y : ℤ × ℤ}
    (hcop : IsCoprime d (numerator B d x))
    (hfx : (f : ℤ) ∣ numerator B d x) (hfy : (f : ℤ) ∣ numerator B d y) :
    d * (f : ℤ) ∣ det B d x y := by
  have hdf : IsCoprime d (f : ℤ) := by
    obtain ⟨a, ha⟩ := hfx
    rw [ha] at hcop
    exact hcop.of_mul_right_left
  exact hdf.mul_dvd (by rw [det_eq]; exact dvd_mul_right _ _)
    (dvd_sub (hfy.mul_left _) (hfx.mul_left _))

private theorem cast_mul_le_abs_of_dvd {m k : ℤ} (hm : 0 < m) (hk : k ≠ 0) (h : m ∣ k) :
    (m : ℝ) ≤ |(k : ℝ)| := by
  obtain ⟨a, ha⟩ := h
  have ha0 : a ≠ 0 := by
    intro h0
    exact hk (by simp only [ha, h0, mul_zero])
  have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by
    have h : (1 : ℝ) ≤ (a.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr ha0
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [ha, Int.cast_mul, abs_mul, abs_of_pos hmR]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 hmR.le

private noncomputable def u (R : ℝ) (x : ℤ × ℤ) : ℝ := (x.1 : ℝ) / (2 * R)

private noncomputable def v (B d : ℤ) (Z : ℝ) (x : ℤ × ℤ) : ℝ := (numerator B d x : ℝ) / Z

private noncomputable def normSlope (B d : ℤ) (R Z : ℝ) (x : ℤ × ℤ) : ℝ :=
  u R x / (u R x + v B d Z x)

private theorem norm_bounds {B d : ℤ} {R Z : ℝ} {x : ℤ × ℤ}
    (hR : 0 < R) (hZ : 0 < Z) (hx : InBox B d R Z x) :
    0 < u R x ∧ 0 < v B d Z x ∧ u R x ≤ 1 ∧ v B d Z x ≤ 1 := by
  have h2R : 0 < 2 * R := by positivity
  have hG : (0 : ℝ) < x.1 := by exact_mod_cast hx.G_pos
  have hc : (0 : ℝ) < numerator B d x := by exact_mod_cast hx.c_pos
  exact ⟨div_pos hG h2R, div_pos hc hZ, (div_le_one h2R).2 hx.G_le, (div_le_one hZ).2 hx.c_le⟩

private theorem normSlope_gap {B d : ℤ} {f : ℕ} {R Z : ℝ} {x y : ℤ × ℤ}
    (hd : 0 < d) (hf : 0 < f) (hR : 0 < R) (hZ : 0 < Z)
    (hx : InBox B d R Z x) (hy : InBox B d R Z y) (hne : x ≠ y)
    (hfx : (f : ℤ) ∣ numerator B d x) (hfy : (f : ℤ) ∣ numerator B d y) :
    (d : ℝ) * (f : ℝ) / (8 * R * Z) ≤ |normSlope B d R Z x - normSlope B d R Z y| := by
  obtain ⟨hux, hvx, hux₁, hvx₁⟩ := norm_bounds hR hZ hx
  obtain ⟨huy, hvy, huy₁, hvy₁⟩ := norm_bounds hR hZ hy
  have hxy : det B d x y ≠ 0 := fun h => hne (eq_of_det_eq_zero hd.ne' hx hy h)
  have hdf : (0 : ℤ) < d * (f : ℤ) := mul_pos hd (by exact_mod_cast hf)
  have hdet : (d : ℝ) * (f : ℝ) ≤ |(det B d x y : ℝ)| := by
    simpa only [Int.cast_mul, Int.cast_natCast] using
      cast_mul_le_abs_of_dvd hdf hxy (mul_dvd_det hx.coprime hfx hfy)
  let sx := u R x + v B d Z x
  let sy := u R y + v B d Z y
  have hsx : 0 < sx := add_pos hux hvx
  have hsy : 0 < sy := add_pos huy hvy
  have hsx₂ : sx ≤ 2 := by dsimp only [sx]; linarith only [hux₁, hvx₁]
  have hsy₂ : sy ≤ 2 := by dsimp only [sy]; linarith only [huy₁, hvy₁]
  have hsprod : sx * sy ≤ 4 := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using mul_le_mul hsx₂ hsy₂ hsy.le (by norm_num)
  have hbase : 0 < 2 * R * Z := by positivity
  have hden : 0 < 2 * R * Z * (sx * sy) := mul_pos hbase (mul_pos hsx hsy)
  have hden_le : 2 * R * Z * (sx * sy) ≤ 8 * R * Z := calc
    _ ≤ 2 * R * Z * 4 := mul_le_mul_of_nonneg_left hsprod hbase.le
    _ = _ := by ring
  have hcross : u R x * v B d Z y - u R y * v B d Z x = (det B d x y : ℝ) / (2 * R * Z) := by
    simp only [u, v, det, Int.cast_sub, Int.cast_mul, ← mul_div_mul_comm, div_sub_div_same]
  have hformula : normSlope B d R Z x - normSlope B d R Z y =
      (det B d x y : ℝ) / (2 * R * Z * (sx * sy)) := calc
    _ = (u R x * sy - sx * u R y) / (sx * sy) := div_sub_div _ _ hsx.ne' hsy.ne'
    _ = (u R x * v B d Z y - u R y * v B d Z x) / (sx * sy) := by
      congr 1
      dsimp only [sx, sy]
      ring
    _ = _ := by rw [hcross, div_div]
  rw [hformula, abs_div, abs_of_pos hden]
  exact (div_le_div_of_nonneg_left (by positivity) hden hden_le).trans
    (div_le_div_of_nonneg_right hdet hden.le)

private theorem card_le_of_spaced {A : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hunit : ∀ x ∈ A, 0 ≤ x ∧ x ≤ 1)
    (hgap : ∀ x ∈ A, ∀ y ∈ A, x < y → δ ≤ y - x) : (A.card : ℝ) ≤ 1 + 1 / δ := by
  by_cases hA : A.card = 0
  · simp only [hA, Nat.cast_zero]
    positivity
  -- In sorted order, each adjacent gap adds at least `δ` to the lower bound.
  let e := A.orderEmbOfFin rfl
  have hem (j : Fin A.card) : e j ∈ A := A.orderEmbOfFin_mem rfl j
  have hlower (j : ℕ) (hj : j < A.card) : (j : ℝ) * δ ≤ e ⟨j, hj⟩ := by
    induction j with
    | zero => simpa only [Nat.cast_zero, zero_mul] using (hunit _ (hem ⟨0, hj⟩)).1
    | succ j ih =>
      have hj' : j < A.card := by omega
      have he : e ⟨j, hj'⟩ < e ⟨j + 1, hj⟩ := e.strictMono (by exact Nat.lt_succ_self j)
      have h := hgap _ (hem _) _ (hem _) he
      rw [Nat.cast_succ]
      linarith only [ih hj', h]
  have hlast : A.card - 1 < A.card := by omega
  have h := (hlower (A.card - 1) hlast).trans (hunit _ (hem ⟨A.card - 1, hlast⟩)).2
  rw [Nat.cast_sub (by omega : 1 ≤ A.card), Nat.cast_one] at h
  have h' := (le_div_iff₀ hδ).2 h
  linarith only [h']

/-- At a fixed divisor `f`, count the pairs themselves. The determinant of
any two distinct pairs is a nonzero multiple of `df`, and their normalized
slopes lie in `[0, 1]` with spacing at least `df/(8RZ)`. -/
public theorem card_le_fixed_divisor {S : Finset (ℤ × ℤ)} {B d : ℤ} {R Z : ℝ} {f : ℕ}
    (hd : 0 < d) (hR : 0 < R) (hZ : 0 < Z) (hf : 0 < f)
    (hbox : ∀ x ∈ S, InBox B d R Z x) :
    ((S.filter fun x => (f : ℤ) ∣ numerator B d x).card : ℝ) ≤
      1 + 8 * R * Z / ((d : ℝ) * (f : ℝ)) := by
  classical
  let T := S.filter fun x => (f : ℤ) ∣ numerator B d x
  let g := normSlope B d R Z
  let δ := (d : ℝ) * (f : ℝ) / (8 * R * Z)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hspace {x y : ℤ × ℤ} (hx : x ∈ T) (hy : y ∈ T) (hne : x ≠ y) : δ ≤ |g x - g y| :=
    normSlope_gap hd hf hR hZ (hbox x (mem_filter.mp hx).1) (hbox y (mem_filter.mp hy).1)
      hne (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have hinj : Set.InjOn g T := by
    intro x hx y hy hxy
    by_contra hne
    have h := hspace hx hy hne
    rw [hxy, sub_self, abs_zero] at h
    exact hδ.not_ge h
  have hunit (z : ℝ) (hz : z ∈ T.image g) : 0 ≤ z ∧ z ≤ 1 := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    obtain ⟨hu, hv, _, _⟩ := norm_bounds hR hZ (hbox x (mem_filter.mp hx).1)
    have hs : 0 < u R x + v B d Z x := add_pos hu hv
    exact ⟨(div_pos hu hs).le, (div_le_one hs).2 (le_add_of_nonneg_right hv.le)⟩
  have hgap (z : ℝ) (hz : z ∈ T.image g) (w : ℝ) (hw : w ∈ T.image g) (hzw : z < w) :
      δ ≤ w - z := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hw
    exact (abs_of_pos (sub_pos.mpr hzw)) ▸ hspace hy hx (fun he => hzw.ne (congrArg g he.symm))
  have h := card_le_of_spaced hδ hunit hgap
  rw [card_image_of_injOn hinj] at h
  simpa only [δ, one_div_div] using h

/-- All eligible-smooth integers in the crossing interval, independently of
which numerator is being recovered. -/
public noncomputable def divisorMenu (eligible : ℕ → Prop) (R X : ℝ) : Finset ℕ := by
  classical
  exact (Ioc ⌊2 * R⌋₊ ⌊2 * R * X⌋₊).filter (EligibleSmooth eligible X)

/-- Membership in the concrete crossing menu is exactly the size and smoothness test. -/
public theorem mem_divisorMenu {eligible : ℕ → Prop} {R X : ℝ} {f : ℕ} (hR : 0 ≤ 2 * R) :
    f ∈ divisorMenu eligible R X ↔
      2 * R < (f : ℝ) ∧ (f : ℝ) ≤ 2 * R * X ∧ EligibleSmooth eligible X f := by
  classical
  unfold divisorMenu
  rw [mem_filter, mem_Ioc, Nat.floor_lt hR, and_assoc]
  refine and_congr_right fun hlt => and_congr_left fun _ => ?_
  constructor
  · intro hf
    have hnonneg : 0 ≤ 2 * R * X := by
      by_contra! hneg
      rw [Nat.floor_of_nonpos hneg.le] at hf
      have hf0 : f = 0 := Nat.eq_zero_of_le_zero hf
      simp only [hf0, Nat.cast_zero] at hlt
      exact hlt.not_ge hR
    exact (Nat.le_floor_iff hnonneg).1 hf
  · exact Nat.le_floor

/-- The menu covers every admissible pair: no uniqueness of the crossing
divisor is required. -/
public theorem exists_mem_divisorMenu_dvd {eligible : ℕ → Prop} {B d : ℤ} {R Z X : ℝ} {x : ℤ × ℤ}
    (hR : 1 ≤ 2 * R) (hx : Admissible eligible B d R Z X x) :
    ∃ f ∈ divisorMenu eligible R X, (f : ℤ) ∣ numerator B d x := by
  have hc : (0 : ℝ) < numerator B d x := by exact_mod_cast hx.1.c_pos
  have he : ((numerator B d x).natAbs : ℝ) = (numerator B d x : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hc]
  obtain ⟨f, hfc, hRf, hfX, hfs⟩ := exists_crossing_divisor hR (by rw [he]; exact hx.2.1) hx.2.2
  exact ⟨f, (mem_divisorMenu (zero_le_one.trans hR)).2 ⟨hRf, hfX, hfs⟩, Int.natCast_dvd.2 hfc⟩

/-- The finite menu bounds the number of distinct recovered numerators of any
finite family of admissible pairs. Overlap of divisibility fibers is allowed. -/
public theorem card_numerators_le {S : Finset (ℤ × ℤ)} {eligible : ℕ → Prop}
    {B d : ℤ} {R Z X : ℝ} (hd : 0 < d) (hR : 1 ≤ 2 * R) (hZ : 0 < Z)
    (hS : ∀ x ∈ S, Admissible eligible B d R Z X x) :
    ((S.image (numerator B d)).card : ℝ) ≤
      (divisorMenu eligible R X).card * (1 + 4 * Z / (d : ℝ)) := by
  classical
  let M := divisorMenu eligible R X
  let T (f : ℕ) := S.filter fun x => (f : ℤ) ∣ numerator B d x
  have hcover : S ⊆ M.biUnion T := by
    intro x hx
    obtain ⟨f, hf, hfc⟩ := exists_mem_divisorMenu_dvd hR (hS x hx)
    exact mem_biUnion.mpr ⟨f, hf, mem_filter.mpr ⟨hx, hfc⟩⟩
  have hcard : (S.image (numerator B d)).card ≤ ∑ f ∈ M, (T f).card :=
    card_image_le.trans ((card_le_card hcover).trans card_biUnion_le)
  have hRpos : 0 < R := by linarith only [hR]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hprice (f : ℕ) (hf : f ∈ M) : ((T f).card : ℝ) ≤ 1 + 4 * Z / (d : ℝ) := by
    have hRf := ((mem_divisorMenu (zero_le_one.trans hR)).1 hf).1
    have hfpos : 0 < f := Nat.cast_pos.mp ((zero_le_one.trans hR).trans_lt hRf)
    have h₀ := card_le_fixed_divisor hd hRpos hZ hfpos (fun x hx => (hS x hx).1)
    have hden : 0 < (d : ℝ) * (2 * R) := by positivity
    have hden_le : (d : ℝ) * (2 * R) ≤ (d : ℝ) * (f : ℝ) :=
      mul_le_mul_of_nonneg_left hRf.le hdR.le
    have hquot : 8 * R * Z / ((d : ℝ) * (2 * R)) = 4 * Z / (d : ℝ) := by
      rw [show 8 * R * Z = 4 * Z * (2 * R) by ring, mul_div_mul_comm,
        div_self (show (2 : ℝ) * R ≠ 0 by positivity), mul_one]
    exact h₀.trans (add_le_add (le_refl 1)
      ((div_le_div_of_nonneg_left (by positivity) hden hden_le).trans_eq hquot))
  calc
    _ ≤ ∑ f ∈ M, ((T f).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _f ∈ M, (1 + 4 * Z / (d : ℝ)) := sum_le_sum hprice
    _ = _ := by rw [sum_const, nsmul_eq_mul]

private theorem finite_admissible (eligible : ℕ → Prop) (B d : ℤ) (R Z X : ℝ) (hd : d ≠ 0) :
    {x : ℤ × ℤ | Admissible eligible B d R Z X x}.Finite := by
  let A := Icc (1 : ℤ) ⌊2 * R⌋ ×ˢ Icc (1 : ℤ) ⌊Z⌋
  refine Set.Finite.of_injOn (f := fun x : ℤ × ℤ => (x.1, numerator B d x)) ?_ ?_ A.finite_toSet
  · intro x hx
    change Admissible eligible B d R Z X x at hx
    change (x.1, numerator B d x) ∈ A
    have hG : 1 ≤ x.1 := by have := hx.1.G_pos; omega
    have hc : 1 ≤ numerator B d x := by have := hx.1.c_pos; omega
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hG, Int.le_floor.mpr hx.1.G_le⟩,
      mem_Icc.mpr ⟨hc, Int.le_floor.mpr hx.1.c_le⟩⟩
  · intro x _ y _ h
    change (x.1, numerator B d x) = (y.1, numerator B d y) at h
    obtain ⟨hG, hc⟩ := Prod.mk.inj h
    unfold numerator at hc
    rw [hG, add_right_inj] at hc
    exact Prod.ext hG (mul_left_cancel₀ hd hc)

/-- The full finite set of actual admissible `(G, i)`, not a set of proxy
vectors. Finiteness comes from the injective map into the bounded `(G, c)` box. -/
public noncomputable def admissiblePairs (eligible : ℕ → Prop) (B d : ℤ) (R Z X : ℝ) (hd : d ≠ 0) :
    Finset (ℤ × ℤ) := (finite_admissible eligible B d R Z X hd).toFinset

/-- The finite pair set contains exactly the pairs satisfying the recovery conditions. -/
public theorem mem_admissiblePairs {eligible : ℕ → Prop} {B d : ℤ} {R Z X : ℝ} {hd : d ≠ 0} {x : ℤ × ℤ} :
    x ∈ admissiblePairs eligible B d R Z X hd ↔ Admissible eligible B d R Z X x :=
  Set.Finite.mem_toFinset _

/-- Full scalar recovery endpoint for the fixed rows and the positive box. -/
public theorem card_all_numerators_le {eligible : ℕ → Prop} {B d : ℤ} {R Z X : ℝ}
    (hd : 0 < d) (hR : 1 ≤ 2 * R) (hZ : 0 < Z) :
    (((admissiblePairs eligible B d R Z X hd.ne').image (numerator B d)).card : ℝ) ≤
      (divisorMenu eligible R X).card * (1 + 4 * Z / (d : ℝ)) :=
  card_numerators_le hd hR hZ fun _ hx => mem_admissiblePairs.mp hx

end CrossedScalarRecovery
