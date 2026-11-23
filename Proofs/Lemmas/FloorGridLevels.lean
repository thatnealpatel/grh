module

public import Lemmas.FloorGridPhysical
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Interval.Finset.Nat

/-! # Finite dyadic floor-grid levels

The level at `j` is the span of the physical columns with indices in `[2, 4^j]`.
Passing from the coarse phase to the fine phase expresses each coarse column as a
linear combination of the fine columns at indices `2 * k` and `2`.
-/

open Filter MeasureTheory

namespace Masullo

noncomputable section

private theorem nat_mul_fract (k : ℕ) (v : ℝ) :
    (k : ℝ) * Int.fract v = (k : ℝ) * v - (((k : ℤ) * ⌊v⌋ : ℤ) : ℝ) := by
  rw [Int.fract, mul_sub, Int.cast_mul, Int.cast_natCast]

/-- The coarser phase is the fractional part of twice the finer phase. -/
public theorem floorGridPhase_eq_fract_two_mul (j : ℕ) (x : ℝ) :
    floorGridPhase j x = Int.fract (2 * floorGridPhase (j + 1) x) := by
  let v := Real.exp x / (2 : ℝ) ^ (j + 1)
  have h : Real.exp x / (2 : ℝ) ^ j = 2 * v := by
    dsimp [v]
    rw [pow_succ]
    field_simp
  change Int.fract (Real.exp x / (2 : ℝ) ^ j) = Int.fract (2 * Int.fract v)
  rw [h]
  have htwo := nat_mul_fract 2 v
  simp only [Nat.cast_ofNat] at htwo
  rw [htwo, Int.fract_sub_intCast]

private theorem floor_mul_fract_two (k : ℕ) (u : ℝ) :
    ⌊(k : ℝ) * Int.fract (2 * u)⌋ = ⌊((2 * k : ℕ) : ℝ) * u⌋ - (k : ℤ) * ⌊2 * u⌋ := by
  rw [nat_mul_fract, Int.floor_sub_intCast]
  push_cast
  rw [mul_left_comm (k : ℝ), mul_assoc]

/-- The exact dyadic relation between physical columns, as an equality in `L²`. -/
public theorem floorGridColumn_succ_eq (a : ℝ) (ha : a < 1 / 2) (j k : ℕ) :
    floorGridColumn a ha j k =
      floorGridColumn a ha (j + 1) (2 * k) - (k : ℝ) • floorGridColumn a ha (j + 1) 2 := by
  apply Lp.ext
  filter_upwards [floorGridColumn_ae a ha j k, floorGridColumn_ae a ha (j + 1) (2 * k),
    floorGridColumn_ae a ha (j + 1) 2,
    Lp.coeFn_sub (floorGridColumn a ha (j + 1) (2 * k))
      ((k : ℝ) • floorGridColumn a ha (j + 1) 2),
    Lp.coeFn_smul (k : ℝ) (floorGridColumn a ha (j + 1) 2)] with x hj h2k h2 hsub hsmul
  rw [hj, hsub]
  change _ = floorGridColumn a ha (j + 1) (2 * k) x -
    ((k : ℝ) • floorGridColumn a ha (j + 1) 2) x
  rw [hsmul]
  change _ = floorGridColumn a ha (j + 1) (2 * k) x -
    (k : ℝ) * floorGridColumn a ha (j + 1) 2 x
  rw [h2k, h2, floorGridPhase_eq_fract_two_mul j x, floor_mul_fract_two]
  push_cast
  ring

/-- The span of the physical floor-grid columns with natural indices `2 ≤ k ≤ 4^j`. -/
@[expose] public def floorGridLevel (a : ℝ) (ha : a < 1 / 2) (j : ℕ) :
    Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  Submodule.span ℝ (floorGridColumn a ha j '' (Finset.Icc 2 (4 ^ j) : Set ℕ))

public instance instFiniteDimensionalFloorGridLevel (a : ℝ) (ha : a < 1 / 2) (j : ℕ) :
    FiniteDimensional ℝ (floorGridLevel a ha j) :=
  FiniteDimensional.span_of_finite ℝ ((Finset.Icc 2 (4 ^ j)).finite_toSet.image _)

/-- An index in the defining interval gives a column of the level. -/
public theorem floorGridColumn_mem_floorGridLevel (a : ℝ) (ha : a < 1 / 2) {j k : ℕ}
    (hklo : 2 ≤ k) (hkhi : k ≤ 4 ^ j) : floorGridColumn a ha j k ∈ floorGridLevel a ha j :=
  Submodule.subset_span ⟨k, Finset.mem_Icc.mpr ⟨hklo, hkhi⟩, rfl⟩

/-- To contain a level it suffices to contain each column in its defining interval. -/
public theorem floorGridLevel_le_iff (a : ℝ) (ha : a < 1 / 2) (j : ℕ)
    (V : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ))) :
    floorGridLevel a ha j ≤ V ↔ ∀ k : ℕ, 2 ≤ k → k ≤ 4 ^ j → floorGridColumn a ha j k ∈ V := by
  rw [floorGridLevel, Submodule.span_le]
  constructor
  · intro h k hklo hkhi
    exact h ⟨k, Finset.mem_Icc.mpr ⟨hklo, hkhi⟩, rfl⟩
  · rintro h _ ⟨k, hk, rfl⟩
    obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
    exact h k hklo hkhi

/-- The index interval for `j = 0` is empty. -/
public theorem floorGridLevel_zero (a : ℝ) (ha : a < 1 / 2) : floorGridLevel a ha 0 = ⊥ := by
  have h : Finset.Icc 2 ((4 : ℕ) ^ 0) = ∅ := Finset.Icc_eq_empty_of_lt (by decide)
  rw [floorGridLevel, h, Finset.coe_empty, Set.image_empty, Submodule.span_empty]

/-- The column at index `2` is present at every positive level. -/
public theorem floorGridColumn_two_mem_floorGridLevel (a : ℝ) (ha : a < 1 / 2) {j : ℕ}
    (hj : 1 ≤ j) : floorGridColumn a ha j 2 ∈ floorGridLevel a ha j :=
  floorGridColumn_mem_floorGridLevel a ha le_rfl
    ((show 2 ≤ (4 : ℕ) ^ 1 by decide).trans (Nat.pow_le_pow_right (by decide) hj))

/-- Each level is contained in the next dyadic level. -/
public theorem floorGridLevel_le_succ (a : ℝ) (ha : a < 1 / 2) (j : ℕ) :
    floorGridLevel a ha j ≤ floorGridLevel a ha (j + 1) := by
  apply (floorGridLevel_le_iff a ha j _).mpr
  intro k hklo hkhi
  have h2k : 2 * k ≤ 4 ^ (j + 1) := by
    rw [pow_succ]
    omega
  rw [floorGridColumn_succ_eq]
  exact Submodule.sub_mem _
    (floorGridColumn_mem_floorGridLevel a ha (by omega) h2k)
    (Submodule.smul_mem _ _ (floorGridColumn_two_mem_floorGridLevel a ha (by omega)))

/-- The floor-grid levels are increasing in the dyadic index. -/
public theorem floorGridLevel_mono (a : ℝ) (ha : a < 1 / 2) : Monotone (floorGridLevel a ha) :=
  monotone_nat_of_le_succ (floorGridLevel_le_succ a ha)

end

end Masullo
