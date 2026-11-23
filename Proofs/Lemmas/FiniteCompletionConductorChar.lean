module

public import Theorems.FiniteAdeleTraceCharacter
public import Theorems.FiniteCompletionDifferentScale
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.MulChar.Basic

import Lemmas.FiniteCompletionCodifferentFourier
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Conductor characters on finite completion quotients -/

open IsDedekindDomain IsLocalRing NumberField
open scoped Masullo nonZeroDivisors

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "m" => maximalIdeal O
local notation "Q" n:max => (O ⧸ m ^ n)
local notation:max "qmk[" n "]" => Ideal.Quotient.mk (m ^ n)

attribute [local instance] finiteCompletion_moduleFinite finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree

/-- With `π` a uniformizer and `d` the different exponent, the positive trace
phase at level `n` is evaluated at frequency `π⁻⁽ᵈ⁺ⁿ⁾`. -/
@[expose] public noncomputable def finiteCompletionConductorFrequency (π : O) (n : ℕ) : F :=
  ((π : F) ^ (finiteCompletionDifferentExponent v + n))⁻¹

private theorem mem_pow_iff_scaled_integral (π : O) (hπ : Irreducible π) (n : ℕ) (b : O) :
    (b : F) * ((π : F) ^ n)⁻¹ ∈ O ↔ b ∈ m ^ n := by
  have hne : (π : F) ^ n ≠ 0 := pow_ne_zero _ (fun h ↦ hπ.ne_zero (Subtype.ext h))
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · intro hb
    refine ⟨⟨_, hb⟩, Subtype.ext ?_⟩
    change (b : F) = (π : F) ^ n * ((b : F) * ((π : F) ^ n)⁻¹)
    rw [mul_left_comm, mul_inv_cancel₀ hne, mul_one]
  · rintro ⟨y, rfl⟩
    change (π : F) ^ n * (y : F) * ((π : F) ^ n)⁻¹ ∈ O
    rw [mul_right_comm, mul_inv_cancel₀ hne, one_mul]
    exact y.property

/-- An integer's scaled trace phase is trivial on all integral multiples
exactly when the integer belongs to the modulus. This identifies the radical
of the residue-ring pairing, not the pointwise kernel of the phase. -/
public theorem finiteCompletion_conductorPhase_annihilator_iff
    (π : O) (hπ : Irreducible π) (n : ℕ) (b : O) :
    (∀ y : O, finiteCompletionTraceAddChar v
      ((finiteCompletionConductorFrequency v π n * (b : F)) * (y : F)) = 1) ↔ b ∈ m ^ n := by
  let d := finiteCompletionDifferentExponent v
  have hgen : Ideal.span ({π ^ d} : Set O) = differentIdeal ℤ_[finiteCompletionBasePrime v] O := by
    rw [finiteCompletion_differentIdeal_eq_maximalIdeal_pow v, hπ.maximalIdeal_eq,
      Ideal.span_singleton_pow]
  simp only [finiteCompletionTraceAddChar_apply]
  rw [finiteCompletion_traceChar_trivial_iff, finiteCompletion_traceDual_eq_inv_differentIdeal]
  change _ ∈ (_ : FractionalIdeal O⁰ F) ↔ _
  rw [finiteCompletion_mem_codifferent_iff v _ hgen]
  have hne : (π : F) ^ d ≠ 0 := pow_ne_zero _ (fun h ↦ hπ.ne_zero (Subtype.ext h))
  change (π : F) ^ d * (((π : F) ^ (d + n))⁻¹ * (b : F)) ∈ O ↔ _
  rw [pow_add, mul_inv_rev, ← mul_assoc, mul_left_comm ((π : F) ^ d),
    mul_inv_cancel₀ hne, mul_one, mul_comm _ (b : F)]
  exact mem_pow_iff_scaled_integral v π hπ n b

private noncomputable def conductorPhase (π : O) (n : ℕ) : AddChar O ℂ :=
  (finiteCompletionTraceAddChar v).compAddMonoidHom
    ((AddMonoidHom.mulLeft (finiteCompletionConductorFrequency v π n)).comp (O).subtype.toAddMonoidHom)

/-- The positive trace phase descends modulo the indicated power of the
maximal ideal, since it is trivial on that ideal. -/
public noncomputable def finiteCompletionConductorAddChar (π : O) (hπ : Irreducible π) (n : ℕ) :
    AddChar (Q n) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift (m ^ n : Ideal O).toAddSubgroup (conductorPhase v π n).toAddMonoidHom
      fun b hb ↦ by
        change finiteCompletionTraceAddChar v
          (finiteCompletionConductorFrequency v π n * (b : F)) = 1
        have h := (finiteCompletion_conductorPhase_annihilator_iff v π hπ n b).2 hb 1
        simpa only [show ((1 : O) : F) = 1 from rfl, mul_one] using h

@[simp] public theorem finiteCompletionConductorAddChar_mk
    (π : O) (hπ : Irreducible π) (n : ℕ) (b : O) :
    finiteCompletionConductorAddChar v π hπ n (qmk[n] b) =
      finiteCompletionTraceAddChar v (finiteCompletionConductorFrequency v π n * (b : F)) := by
  unfold finiteCompletionConductorAddChar conductorPhase
  rfl

/-- On quotient representatives the additive factor is the actual local trace phase. -/
public theorem finiteCompletionConductorAddChar_mulShift_mk
    (π : O) (hπ : Irreducible π) (n : ℕ) (a b : O) :
    ((finiteCompletionConductorAddChar v π hπ n).mulShift (qmk[n] b)) (qmk[n] a) =
      finiteCompletionTraceAddChar v (finiteCompletionConductorFrequency v π n * (b : F) * (a : F)) := by
  rw [AddChar.mulShift_apply, ← map_mul, finiteCompletionConductorAddChar_mk, mul_assoc]
  rfl

/-- The descended phase has no nonzero principal ideal in its kernel. -/
public theorem finiteCompletionConductorAddChar_isPrimitive (π : O) (hπ : Irreducible π) (n : ℕ) :
    (finiteCompletionConductorAddChar v π hπ n).IsPrimitive := by
  intro t ht h
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  apply ht
  rw [Ideal.Quotient.eq_zero_iff_mem, ← finiteCompletion_conductorPhase_annihilator_iff v π hπ]
  intro y
  have hy := DFunLike.congr_fun h (qmk[n] y)
  rw [finiteCompletionConductorAddChar_mulShift_mk, one_apply] at hy
  exact hy

/-- Reduction on the units of the completion integers, including reduction to
the trivial quotient at level zero. -/
public noncomputable def finiteCompletionUnitReduction (n : ℕ) : Oˣ →* (Q n)ˣ :=
  Units.map (qmk[n]).toMonoidHom

/-- The kernel of unit reduction at level `n` consists of units congruent to `1`. -/
public theorem mem_finiteCompletionUnitReduction_ker (n : ℕ) (u : Oˣ) :
    u ∈ (finiteCompletionUnitReduction v n).ker ↔ (u : O) - 1 ∈ m ^ n := by
  rw [MonoidHom.mem_ker, ← Ideal.Quotient.mk_eq_one_iff_sub_mem]
  exact ⟨congrArg Units.val, fun h ↦ Units.ext h⟩

private theorem quotientMk_isLocalHom {n : ℕ} (hn : 0 < n) : IsLocalHom (qmk[n]) := by
  have : Nontrivial (Q n) := Ideal.Quotient.nontrivial_iff.mpr fun h ↦
    (maximalIdeal.isMaximal O).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self hn.ne'))
  exact IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- At positive level a residue is a unit exactly when its representative is a unit. -/
public theorem isUnit_finiteCompletionQuotient_mk {n : ℕ} (hn : 0 < n) (b : O) :
    IsUnit (qmk[n] b) ↔ IsUnit b := by
  let := quotientMk_isLocalHom v hn
  exact isUnit_map_iff (qmk[n]) b

/-- Every unit of the positive-level quotient lifts to a unit. -/
public theorem finiteCompletionUnitReduction_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (finiteCompletionUnitReduction v n) :=
  surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective (quotientMk_isLocalHom v hn)

/-- The conductor level is the least exponent at which the character on integral
units descends. In particular, level zero means the character is trivial. -/
@[expose] public def IsFiniteCompletionConductor (χ : Oˣ →* ℂˣ) (n : ℕ) : Prop :=
  IsLeast {k : ℕ | (finiteCompletionUnitReduction v k).ker ≤ χ.ker} n

/-- Level zero is equivalent to triviality on the integral units. -/
@[simp] public theorem isFiniteCompletionConductor_zero_iff (χ : Oˣ →* ℂˣ) :
    IsFiniteCompletionConductor v χ 0 ↔ χ = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro u
    exact h.1 ((mem_finiteCompletionUnitReduction_ker v 0 u).2 (by simp))
  · rintro rfl
    exact ⟨fun u _ ↦ rfl, fun k _ ↦ Nat.zero_le k⟩

/-- Descend a character on integral units at any positive level where it is
trivial on the reduction kernel, then extend by zero to the full quotient. -/
public noncomputable def finiteCompletionConductorMulChar {n : ℕ} (hn : 0 < n)
    (χ : Oˣ →* ℂˣ) (hχ : (finiteCompletionUnitReduction v n).ker ≤ χ.ker) : MulChar (Q n) ℂ :=
  let r := finiteCompletionUnitReduction v n
  let e := QuotientGroup.quotientKerEquivOfSurjective r
    (finiteCompletionUnitReduction_surjective v hn)
  MulChar.ofUnitHom ((QuotientGroup.lift r.ker χ hχ).comp e.symm.toMonoidHom)

/-- The descended multiplicative character agrees with the original on every lifted unit. -/
@[simp] public theorem finiteCompletionConductorMulChar_apply_reduction {n : ℕ} (hn : 0 < n)
    (χ : Oˣ →* ℂˣ) (hχ : (finiteCompletionUnitReduction v n).ker ≤ χ.ker) (u : Oˣ) :
    finiteCompletionConductorMulChar v hn χ hχ (finiteCompletionUnitReduction v n u : (Q n)) =
      (χ u : ℂ) := by
  let r := finiteCompletionUnitReduction v n
  let e := QuotientGroup.quotientKerEquivOfSurjective r
    (finiteCompletionUnitReduction_surjective v hn)
  have he : e (u : Oˣ ⧸ r.ker) = r u := rfl
  unfold finiteCompletionConductorMulChar
  rw [MulChar.ofUnitHom_coe]
  change ((QuotientGroup.lift r.ker χ hχ (e.symm (r u))) : ℂ) = _
  rw [← he, MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]

private theorem exists_unit_nontrivial_at_lower_level {χ : Oˣ →* ℂˣ} {k n : ℕ}
    (hχ : IsFiniteCompletionConductor v χ n) (hk : k < n) :
    ∃ u : Oˣ, (u : O) - 1 ∈ m ^ k ∧ χ u ≠ 1 := by
  by_contra! h
  apply (not_le_of_gt hk) (hχ.2 ?_)
  intro u hu
  exact h u ((mem_finiteCompletionUnitReduction_ker v k u).mp hu)

/-- Minimality supplies a unit on which the quotient character is nontrivial,
fixing every nonunit under multiplication. At level one all nonunits are zero;
at higher levels the witness is a principal unit at the preceding level. -/
public theorem finiteCompletionConductorMulChar_nonunit_stabilizer {n : ℕ} (hn : 0 < n)
    (χ : Oˣ →* ℂˣ) (hχ : IsFiniteCompletionConductor v χ n) (b : Q n) (hb : ¬ IsUnit b) :
    ∃ u : (Q n)ˣ, b * (u : Q n) = b ∧ finiteCompletionConductorMulChar v hn χ hχ.1 u ≠ 1 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have ha : a ∈ m := fun hu ↦ hb (hu.map (qmk[n]))
  have hwitness (u : Oˣ) (hu : χ u ≠ 1) :
      finiteCompletionConductorMulChar v hn χ hχ.1 (finiteCompletionUnitReduction v n u : Q n) ≠ 1 := by
    rw [finiteCompletionConductorMulChar_apply_reduction]
    exact fun h ↦ hu (Units.ext h)
  by_cases h₁ : n = 1
  · have hz : qmk[n] a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [h₁] using ha)
    obtain ⟨u, hu⟩ : ∃ u : Oˣ, χ u ≠ 1 := by
      by_contra! h
      have h₀ : IsFiniteCompletionConductor v χ 0 :=
        (isFiniteCompletionConductor_zero_iff v χ).2 (MonoidHom.ext h)
      exact (not_le_of_gt hn) (hχ.2 h₀.1)
    exact ⟨finiteCompletionUnitReduction v n u, by rw [hz, zero_mul], hwitness u hu⟩
  · obtain ⟨u, hu, hne⟩ := exists_unit_nontrivial_at_lower_level v hχ (by omega : n - 1 < n)
    refine ⟨finiteCompletionUnitReduction v n u, ?_, hwitness u hne⟩
    change qmk[n] a * qmk[n] (u : O) = qmk[n] a
    rw [← map_mul, Ideal.Quotient.eq,
      show a * (u : O) - a = a * ((u : O) - 1) by rw [mul_sub, mul_one]]
    have h := Ideal.mul_mem_mul ha hu
    rwa [← pow_succ', Nat.sub_add_cancel hn] at h

end Masullo
