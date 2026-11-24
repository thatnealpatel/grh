module

public import Lemmas.MaskedGapBracketBin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Actual columns in the masked gap bracket

Source: `d673969:.godel/alice/masked-gap-bracket.md:17–40`, especially the recovery at
line 33 and its use in “During attachment selection”. The label and prefix rules are from
`d673969:.godel/alice/shared-row-labels.md:7–11` and
`d673969:.godel/alice/shared-complement-count.md:9`.

At a fixed ordered label list, complete input, and reference, we count distinct original
columns `(c,d)`, not row realizations or just signed directions. The cost of a signed vector
`x` is the number of positive divisors of `|x₂|`.

Owning check session: `01a20d85-3fca-796b-bf11-8791e07c4ba8`.
-/

open scoped BigOperators

namespace MaskedBracketColumns

/-- Product of the longest nondecreasing prime-factor prefix with product at most `K`.
For the source's real cutoff take `K = ⌊Z⌋₊`. The list retains repeated primes. -/
@[expose] public def sortedPrefix (K n : ℕ) : ℕ :=
  let factors := n.primeFactorsList
  let lengths := (Finset.range (factors.length + 1)).filter fun k => (factors.take k).prod ≤ K
  (factors.take (lengths.sup id)).prod

/-- The cutoff, modulus, complete first input and ordered two-label list are fixed. -/
public structure Input where
  K : ℕ
  q : ℕ
  v : ℕ
  F₁ : ℕ
  F₂ : ℕ
  q_pos : 0 < q

/-- The original graph column, not a pair of label factors. -/
public abbrev Column := ℕ × ℕ

/-- One realization of a column at the fixed input. The prefix fields are the actual
construction rule on the two products of the first row; the labels are not column coordinates. -/
public structure Rows (I : Input) (p : Column) where
  a : ℕ
  h : ℕ
  Y : ℕ
  Z : ℕ
  α : ℤ
  β : ℤ
  c_pos : 0 < p.1
  d_pos : 0 < p.2
  h_pos : 0 < h
  Y_pos : 0 < Y
  Z_pos : 0 < Z
  α_ne : α ≠ 0
  β_ne : β ≠ 0
  input : I.v = p.1 * (I.F₁ * a)
  row₁ : (I.v : ℤ) = (p.2 : ℤ) * Y + (I.q : ℤ) * α
  row₂ : (p.1 : ℤ) * I.F₂ * h = (p.2 : ℤ) * Z + (I.q : ℤ) * β
  c_prefix : p.1 = sortedPrefix I.K I.v
  d_prefix : p.2 = sortedPrefix I.K (p.2 * Y)
  second_gap_coprime : IsCoprime ((I.F₂ : ℤ) * h) β
  gaps_coprime : IsCoprime α β

/-- The raw signed gap vector used in the bracket. -/
@[expose] public def Rows.vector {I : Input} {p : Column} (r : Rows I p) : ℤ × ℤ :=
  (r.β, (r.h : ℤ) * r.α)

/-- The exact signed quotient recovers the first gap before taking the sorted prefix. -/
@[expose] public def recoveredDenominator (I : Input) (x : ℤ × ℤ) (h : ℕ) : ℕ :=
  sortedPrefix I.K (((I.v : ℤ) - (I.q : ℤ) * (x.2 / (h : ℤ))).toNat)

public theorem Rows.vector_primitive {I : Input} {p : Column} (r : Rows I p) :
    IsCoprime r.vector.1 r.vector.2 :=
  r.second_gap_coprime.of_mul_left_right.symm.mul_right r.gaps_coprime.symm

/-- A row is in the nonzero second-coordinate scope of the divisor argument. -/
public theorem Rows.vector_snd_ne_zero {I : Input} {p : Column} (r : Rows I p) :
    r.vector.2 ≠ 0 :=
  mul_ne_zero (by exact_mod_cast r.h_pos.ne') r.α_ne

/-- `h` is an actual choice in the finite set of positive divisors of the second coordinate. -/
public theorem Rows.h_mem_divisors {I : Input} {p : Column} (r : Rows I p) :
    r.h ∈ r.vector.2.natAbs.divisors := by
  apply Nat.mem_divisors.mpr
  refine ⟨⟨r.α.natAbs, ?_⟩, Int.natAbs_ne_zero.mpr r.vector_snd_ne_zero⟩
  simp [Rows.vector, Int.natAbs_mul]

/-- Recovery uses signed exact division (including negative gaps), then the actual
prefix of the positive first output. -/
public theorem Rows.denominator_recovered {I : Input} {p : Column} (r : Rows I p) :
    p.2 = recoveredDenominator I r.vector r.h := by
  have hquot : r.vector.2 / (r.h : ℤ) = r.α :=
    Int.ediv_eq_of_eq_mul_right (by exact_mod_cast r.h_pos.ne') rfl
  have hout : (I.v : ℤ) - (I.q : ℤ) * r.α = ((p.2 * r.Y : ℕ) : ℤ) := by
    rw [r.row₁, Nat.cast_mul, add_sub_cancel_right]
  rw [recoveredDenominator, hquot, hout, Int.toNat_natCast]
  exact r.d_prefix

/-- At the same complete input, `d` determines the original column. -/
public theorem Rows.column_eq_of_denominator_eq {I : Input} {p p' : Column}
    (r : Rows I p) (r' : Rows I p') (hd : p.2 = p'.2) : p = p' :=
  Prod.ext (r.c_prefix.trans r'.c_prefix.symm) hd

/-- Equal signed vectors and equal positive cofactors give equal reconstruction inputs,
then equal denominators, then equal original columns. -/
public theorem Rows.column_eq_of_vector_eq_of_h_eq {I : Input} {p p' : Column}
    (r : Rows I p) (r' : Rows I p') (hx : r.vector = r'.vector) (hh : r.h = r'.h) :
    p = p' := by
  apply r.column_eq_of_denominator_eq r'
  rw [r.denominator_recovered, r'.denominator_recovered, hx, hh]

/-- For any part of the original list, the divisor cost is summed over exactly its
occupied signed vectors. The subtype indexes distinct original columns, even if a column
admits more than one realization. -/
public theorem card_le_sum_vector_divisors {I : Input} {S : Finset Column}
    (rows : ∀ p : ↥S, Rows I p) (U : Finset ↥S) :
    U.card ≤ ∑ x ∈ U.image (fun p => (rows p).vector), x.2.natAbs.divisors.card := by
  let vectors := U.image fun p => (rows p).vector
  let choices (x : ℤ × ℤ) := x.2.natAbs.divisors
  rw [← Finset.card_sigma vectors choices]
  let code (p : ↥S) : Σ _ : ℤ × ℤ, ℕ := ⟨(rows p).vector, (rows p).h⟩
  refine Finset.card_le_card_of_injOn code ?_ ?_
  · intro p hp
    exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem _ hp, (rows p).h_mem_divisors⟩
  · intro p _ p' _ heq
    apply Subtype.ext
    exact (rows p).column_eq_of_vector_eq_of_h_eq (rows p')
      (congrArg (fun k : Σ _ : ℤ × ℤ, ℕ => k.1) heq)
      (congrArg (fun k : Σ _ : ℤ × ℤ, ℕ => k.2) heq)

private theorem card_le_two_mul_of_card_vectors_le_two {I : Input} {S : Finset Column}
    (rows : ∀ p : ↥S, Rows I p) (U : Finset ↥S) {D : ℕ}
    (hvec : (U.image fun p => (rows p).vector).card ≤ 2)
    (hD : ∀ p ∈ U, (rows p).vector.2.natAbs.divisors.card ≤ D) : U.card ≤ 2 * D := by
  calc
    U.card ≤ ∑ x ∈ U.image (fun p => (rows p).vector), x.2.natAbs.divisors.card :=
      card_le_sum_vector_divisors rows U
    _ ≤ ∑ _x ∈ U.image (fun p => (rows p).vector), D := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact hD p hp
    _ = (U.image fun p => (rows p).vector).card * D := by simp
    _ ≤ 2 * D := Nat.mul_le_mul_right D hvec

/-- At the fixed input the first labelled row coordinate is `v / c`. -/
@[expose] public def Input.A (I : Input) : ℕ := I.v / sortedPrefix I.K I.v

public theorem Rows.first_coordinate_eq {I : Input} {p : Column} (r : Rows I p) :
    I.A = I.F₁ * r.a := by
  rw [Input.A, ← r.c_prefix, r.input, Nat.mul_div_cancel_left _ r.c_pos]

/-- One group of `L` and the four mask parts. The arithmetic only needs the
listed divisibilities, so it applies in particular to the source's full mask parts. -/
public structure MaskGroup where
  L : ℕ
  m₁ : ℕ
  m₂ : ℕ
  m_d : ℕ
  m_t : ℕ
  deriving DecidableEq

@[expose] public def MaskGroup.a (M : MaskGroup) (I : Input) : ℤ :=
  ((I.A / M.L : ℕ) : ℤ) * M.m₁

@[expose] public def MaskGroup.b (M : MaskGroup) (I : Input) : ℤ := (I.F₂ : ℤ) * M.m₂

/-- The group credit in the raw coordinates. -/
@[expose] public def MaskGroup.credit (M : MaskGroup) : ℤ :=
  (M.L : ℤ) * M.m₁ * M.m₂ * M.m_d * M.m_t

/-- Fixed group conditions, with the coprimality of the two reduced coefficients. -/
public structure MaskGroup.Valid (M : MaskGroup) (I : Input) : Prop where
  L_pos : 0 < M.L
  m₁_pos : 0 < M.m₁
  m₂_pos : 0 < M.m₂
  m_d_pos : 0 < M.m_d
  m_t_pos : 0 < M.m_t
  L_dvd_A : M.L ∣ I.A
  coprime : IsCoprime (M.a I) (M.b I)

/-- The group's mask divisibilities and the exact row determinant quotient `t`.
The second mask is on `x₂/L`, so on the raw coordinate the divisor is `L*m₂`. -/
@[expose] public def MaskGroup.Contains (M : MaskGroup) {I : Input} {p : Column}
    (r : Rows I p) : Prop :=
  ∃ t : ℤ, (I.A : ℤ) * r.Z - (I.F₂ : ℤ) * r.h * r.Y = (I.q : ℤ) * M.L * t ∧
    (M.m₁ : ℤ) ∣ r.vector.1 ∧ (M.L : ℤ) * M.m₂ ∣ r.vector.2 ∧
    M.m_d ∣ p.2 ∧ (M.m_t : ℤ) ∣ t

/-- The reference product test; no group membership condition is placed on `x₀`. -/
@[expose] public def MaskGroup.Passes (M : MaskGroup) (ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ) (x₀ : ℤ × ℤ)
    (T : ℝ) (x : ℤ × ℤ) : Prop :=
  |(MaskedGapBracketBin.det x x₀ : ℝ)| * |(ℓ x : ℝ)| ≤ T * (M.credit : ℝ) * |(ℓ x₀ : ℝ)|

private theorem denominator_eq_mask_mul {d : ℕ} {M : MaskGroup} (h : M.m_d ∣ d) :
    d = M.m_d * (d / M.m_d) := by
  rw [mul_comm, Nat.div_mul_cancel h]

/-- The actual row equations give one congruence modulo `m_d*f*m_t`, not two
separate congruences. The shared prime factors of its factors need not cancel. -/
public theorem MaskGroup.crossing_coordinates {I : Input} {p : Column} {M : MaskGroup}
    (hM : M.Valid I) {r : Rows I p} (hr : M.Contains r) {f : ℕ} (hf : f ∣ p.2 / M.m_d) :
    ∃ z : ℤ × ℤ, r.vector = ((M.m₁ : ℤ) * z.1, (M.L : ℤ) * M.m₂ * z.2) ∧
      (M.a I * z.1 - M.b I * z.2 ≡ 0 [ZMOD (M.m_d : ℤ) * f * M.m_t]) := by
  obtain ⟨t, ht, ⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩, hd, ⟨j, hj⟩⟩ := hr
  have hv : (I.v : ℤ) = (p.1 : ℤ) * (I.A : ℤ) := by
    rw [r.first_coordinate_eq]
    exact_mod_cast r.input
  have h₁ := hv.symm.trans r.row₁
  have he : (p.2 : ℤ) * ((I.A : ℤ) * r.Z - (I.F₂ : ℤ) * r.h * r.Y) =
      -(I.q : ℤ) * ((I.A : ℤ) * r.vector.1 - (I.F₂ : ℤ) * r.vector.2) := by
    simp only [Rows.vector]
    linear_combination ((I.F₂ : ℤ) * r.h) * h₁ - (I.A : ℤ) * r.row₂
  rw [ht] at he
  have hgap : (I.A : ℤ) * r.vector.1 - (I.F₂ : ℤ) * r.vector.2 =
      -(p.2 : ℤ) * M.L * t := by
    apply mul_left_cancel₀ (a := (I.q : ℤ)) (by exact_mod_cast I.q_pos.ne')
    linear_combination he
  have hA : (I.A : ℤ) = (M.L : ℤ) * ((I.A / M.L : ℕ) : ℤ) := by
    exact_mod_cast ((Nat.div_mul_cancel hM.L_dvd_A).symm.trans (Nat.mul_comm _ _))
  have hlinear : M.a I * z₁ - M.b I * z₂ = -(p.2 : ℤ) * t := by
    apply mul_left_cancel₀ (a := (M.L : ℤ)) (by exact_mod_cast hM.L_pos.ne')
    rw [hA, hz₁, hz₂] at hgap
    simp only [MaskGroup.a, MaskGroup.b]
    linear_combination hgap
  obtain ⟨k, hk⟩ := hf
  have hdk : (p.2 : ℤ) = (M.m_d : ℤ) * f * k := by
    exact_mod_cast (calc
      p.2 = M.m_d * (p.2 / M.m_d) := denominator_eq_mask_mul hd
      _ = M.m_d * f * k := by rw [hk, mul_assoc])
  refine ⟨(z₁, z₂), Prod.ext hz₁ hz₂, Int.modEq_zero_iff_dvd.mpr ⟨-(k : ℤ) * j, ?_⟩⟩
  rw [hlinear, hdk, hj]
  ring

/-- At one mask, positive bin and strict crossing, at most two raw signed vectors
occur, and their positive divisor counts bound the number of actual columns. -/
public theorem card_crossing_bin {I : Input} {S : Finset Column} {M : MaskGroup}
    (rows : ∀ p : ↥S, Rows I p) (U : Finset ↥S) (hM : M.Valid I)
    {ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ} {x₀ : ℤ × ℤ} {B₀ T : ℝ} {f : ℕ}
    (h₀ : ℓ x₀ ≠ 0) (hB : 0 < B₀) (hT : 1 ≤ T) (hf : 4 * T < (f : ℝ))
    (hrows : ∀ p ∈ U, M.Contains (rows p) ∧ f ∣ p.val.2 / M.m_d)
    (hbin : ∀ p ∈ U, B₀ ≤ |(ℓ (rows p).vector : ℝ)| ∧ |(ℓ (rows p).vector : ℝ)| < 2 * B₀)
    (hpass : ∀ p ∈ U, M.Passes ℓ x₀ T (rows p).vector) :
    (U.image fun p => (rows p).vector).card ≤ 2 ∧
      U.card ≤ ∑ x ∈ U.image (fun p => (rows p).vector), x.2.natAbs.divisors.card := by
  refine ⟨?_, card_le_sum_vector_divisors rows U⟩
  have hL : (0 : ℤ) < M.L := by exact_mod_cast hM.L_pos
  have hm₁ : (0 : ℤ) < M.m₁ := by exact_mod_cast hM.m₁_pos
  have hm₂ : (0 : ℤ) < M.m₂ := by exact_mod_cast hM.m₂_pos
  have hm_d : (0 : ℤ) < M.m_d := by exact_mod_cast hM.m_d_pos
  have hm_t : (0 : ℤ) < M.m_t := by exact_mod_cast hM.m_t_pos
  have hf' : 4 * T < ((f : ℤ) : ℝ) := by simpa only [Int.cast_natCast] using hf
  have hv (x : ℤ × ℤ) (hx : x ∈ U.image (fun p => (rows p).vector)) := Finset.mem_image.mp hx
  exact (MaskedGapBracketBin.det_eq_zero_and_card_le_two ℓ x₀ hM.coprime hL hm₁ hm₂ hm_d hm_t
    hB hT hf' h₀
    (fun x hx => by obtain ⟨p, _, rfl⟩ := hv x hx; exact (rows p).vector_primitive)
    (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := hv x hx
      exact MaskGroup.crossing_coordinates hM (hrows p hp).1 (hrows p hp).2)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := hv x hx; exact hbin p hp)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := hv x hx; exact hpass p hp)).2

private theorem collinear_of_form_zero (ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ) {x₀ x y : ℤ × ℤ}
    (h₀ : ℓ x₀ ≠ 0) (hx : ℓ x = 0) (hy : ℓ y = 0) : x.1 * y.2 - y.1 * x.2 = 0 := by
  have eval (z : ℤ × ℤ) : ℓ z = z.1 * ℓ (1, 0) + z.2 * ℓ (0, 1) := by
    have hz : z.1 • ((1, 0) : ℤ × ℤ) + z.2 • ((0, 1) : ℤ × ℤ) = z := by
      ext <;> simp
    calc
      ℓ z = ℓ (z.1 • (1, 0) + z.2 • (0, 1)) := congrArg ℓ hz.symm
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  have hcoeff : ℓ (1, 0) ≠ 0 ∨ ℓ (0, 1) ≠ 0 := by
    by_contra! h
    exact h₀ (by simp [eval x₀, h.1, h.2])
  rw [eval x] at hx
  rw [eval y] at hy
  rcases hcoeff with h | h
  · refine (mul_eq_zero.mp (show ℓ (1, 0) * (x.1 * y.2 - y.1 * x.2) = 0 by
      linear_combination y.2 * hx - x.2 * hy)).resolve_left h
  · refine (mul_eq_zero.mp (show ℓ (0, 1) * (x.1 * y.2 - y.1 * x.2) = 0 by
      linear_combination x.1 * hy - y.1 * hx)).resolve_left h

/-- The zero-form branch has its own line of primitive vectors. No positive
bin, mask or crossing assumption is needed to lift this branch to columns. -/
public theorem card_zero_form {I : Input} {S : Finset Column}
    (rows : ∀ p : ↥S, Rows I p) (U : Finset ↥S) {ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ} {x₀ : ℤ × ℤ}
    (h₀ : ℓ x₀ ≠ 0) (hzero : ∀ p ∈ U, ℓ (rows p).vector = 0) :
    (U.image fun p => (rows p).vector).card ≤ 2 ∧
      U.card ≤ ∑ x ∈ U.image (fun p => (rows p).vector), x.2.natAbs.divisors.card := by
  refine ⟨MaskedGapDirections.card_le_two_of_primitive_collinear ?_ ?_,
    card_le_sum_vector_divisors rows U⟩
  · intro x hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact (rows p).vector_primitive
  · intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hy
    exact collinear_of_form_zero ℓ h₀ (hzero p hp) (hzero p' hp')

/-- At fixed `m_d`, each listed small quotient yields at most one original column:
its denominator is `m_d` times that quotient. No vector or divisor cost is paid. -/
public theorem card_small_quotients {I : Input} {S : Finset Column} {M : MaskGroup}
    (rows : ∀ p : ↥S, Rows I p) (U : Finset ↥S) (Q : Finset ℕ)
    (hQ : ∀ p ∈ U, M.m_d ∣ p.val.2 ∧ p.val.2 / M.m_d ∈ Q) : U.card ≤ Q.card := by
  refine Finset.card_le_card_of_injOn (fun p => p.val.2 / M.m_d) (fun p hp => (hQ p hp).2) ?_
  intro p hp p' hp' heq
  apply Subtype.ext
  apply (rows p).column_eq_of_denominator_eq (rows p')
  calc
    p.val.2 = M.m_d * (p.val.2 / M.m_d) := denominator_eq_mask_mul (hQ p hp).1
    _ = M.m_d * (p'.val.2 / M.m_d) := congrArg (M.m_d * ·) heq
    _ = p'.val.2 := (denominator_eq_mask_mul (hQ p' hp').1).symm

/-- Aggregate the actual columns passing the test at one fixed input/reference.
The finite tables must cover each nonzero-form passing column: the small branch
uses the entire quotient, and the large branch uses a bin and a strict crossing
divisor of that quotient. `D` bounds divisor counts of nonzero raw second
coordinates, not fibers of the column map. Overlaps between cells are allowed.

This is a finite budget in terms of the supplied tables. It does not bound the
number of full mask groups or bins, construct the eligible smooth-quotient and
crossing tables, or estimate those tables or `D` by subpower or half-power bounds. -/
public theorem card_le_branch_budget {I : Input} {S : Finset Column}
    (rows : ∀ p : ↥S, Rows I p) (groups : Finset MaskGroup)
    (small crossings : MaskGroup → Finset ℕ) (bins : MaskGroup → Finset ℝ)
    {ℓ : (ℤ × ℤ) →ₗ[ℤ] ℤ} {x₀ : ℤ × ℤ} {T : ℝ} {D : ℕ}
    (h₀ : ℓ x₀ ≠ 0) (hT : 1 ≤ T)
    (hD : ∀ p : ↥S, (rows p).vector.2.natAbs.divisors.card ≤ D)
    (hgroups : ∀ M ∈ groups, M.Valid I)
    (hB : ∀ M ∈ groups, ∀ B ∈ bins M, 0 < B)
    (hf : ∀ M ∈ groups, ∀ f ∈ crossings M, 4 * T < (f : ℝ))
    (hcover : ∀ p : ↥S, ℓ (rows p).vector ≠ 0 →
      ∃ M ∈ groups, M.Contains (rows p) ∧ M.Passes ℓ x₀ T (rows p).vector ∧
        ((p.val.2 / M.m_d ∈ small M ∧ ((p.val.2 / M.m_d : ℕ) : ℝ) ≤ 4 * T) ∨
          ∃ B ∈ bins M, (B ≤ |(ℓ (rows p).vector : ℝ)| ∧ |(ℓ (rows p).vector : ℝ)| < 2 * B) ∧
            ∃ f ∈ crossings M, f ∣ p.val.2 / M.m_d)) :
    S.card ≤ 2 * D + ∑ M ∈ groups, ((small M).card + (bins M).card * (crossings M).card * (2 * D)) := by
  classical
  let zero : Finset ↥S := S.attach.filter fun p => ℓ (rows p).vector = 0
  let smallCell (M : MaskGroup) : Finset ↥S := S.attach.filter fun p =>
    M.m_d ∣ p.val.2 ∧ p.val.2 / M.m_d ∈ small M
  let crossCell (M : MaskGroup) (B : ℝ) (f : ℕ) : Finset ↥S := S.attach.filter fun p =>
    (M.Contains (rows p) ∧ f ∣ p.val.2 / M.m_d) ∧
    (B ≤ |(ℓ (rows p).vector : ℝ)| ∧ |(ℓ (rows p).vector : ℝ)| < 2 * B) ∧
      M.Passes ℓ x₀ T (rows p).vector
  let crossGroup (M : MaskGroup) : Finset ↥S :=
    (bins M).biUnion fun B => (crossings M).biUnion (crossCell M B)
  let covered : Finset ↥S := groups.biUnion fun M => smallCell M ∪ crossGroup M
  have hsub : S.attach ⊆ zero ∪ covered := by
    intro p hp
    by_cases hz : ℓ (rows p).vector = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hz⟩)
    · obtain ⟨M, hM, hm, hpass, hbranch⟩ := hcover p hz
      apply Finset.mem_union_right _
      apply Finset.mem_biUnion.mpr
      refine ⟨M, hM, ?_⟩
      rcases hbranch with ⟨hq, _⟩ | ⟨B, hBmem, hb, f, hfmem, hdiv⟩
      · obtain ⟨_, _, _, _, hd, _⟩ := hm
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hd, hq⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨B, hBmem,
          Finset.mem_biUnion.mpr ⟨f, hfmem, Finset.mem_filter.mpr ⟨hp, ⟨hm, hdiv⟩, hb, hpass⟩⟩⟩)
  have hzero : zero.card ≤ 2 * D :=
    card_le_two_mul_of_card_vectors_le_two rows zero
      (card_zero_form rows zero h₀ (fun _ hp => (Finset.mem_filter.mp hp).2)).1 (fun p _ => hD p)
  have hsmall (M : MaskGroup) : (smallCell M).card ≤ (small M).card :=
    card_small_quotients rows (smallCell M) (small M) (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hcross (M : MaskGroup) (hM : M ∈ groups) (B : ℝ) (hb : B ∈ bins M)
      (f : ℕ) (hfm : f ∈ crossings M) : (crossCell M B f).card ≤ 2 * D := by
    have hm p (hp : p ∈ crossCell M B f) := (Finset.mem_filter.mp hp).2
    exact card_le_two_mul_of_card_vectors_le_two rows (crossCell M B f)
      (card_crossing_bin rows (crossCell M B f) (hgroups M hM) h₀ (hB M hM B hb) hT (hf M hM f hfm)
        (fun p hp => (hm p hp).1) (fun p hp => (hm p hp).2.1) (fun p hp => (hm p hp).2.2)).1
      (fun p _ => hD p)
  have hcrossGroup (M : MaskGroup) (hM : M ∈ groups) :
      (crossGroup M).card ≤ (bins M).card * (crossings M).card * (2 * D) := by
    calc
      (crossGroup M).card ≤ ∑ B ∈ bins M, ((crossings M).biUnion (crossCell M B)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _B ∈ bins M, (crossings M).card * (2 * D) := by
        apply Finset.sum_le_sum
        intro B hb
        calc
          ((crossings M).biUnion (crossCell M B)).card ≤ ∑ f ∈ crossings M, (crossCell M B f).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _f ∈ crossings M, 2 * D := Finset.sum_le_sum (hcross M hM B hb)
          _ = _ := by simp
      _ = _ := by simp [Nat.mul_assoc]
  calc
    S.card = S.attach.card := Finset.card_attach.symm
    _ ≤ (zero ∪ covered).card := Finset.card_le_card hsub
    _ ≤ zero.card + covered.card := Finset.card_union_le _ _
    _ ≤ 2 * D + ∑ M ∈ groups, ((smallCell M ∪ crossGroup M).card) :=
      Nat.add_le_add hzero Finset.card_biUnion_le
    _ ≤ _ := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro M hM
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hsmall M) (hcrossGroup M hM))

end MaskedBracketColumns
