module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Counting weights on a two-leg lift

The two-leg lift (12.2.2.1–2), p. 508, multiplies the quotient kernel
by the sum of products of the two indentation weights. This interface
uses finitely many constant principal-copy weights, not the
base-normalized indentation of Proposition 12.2.2.4.
-/

open scoped BigOperators

namespace Masullo.OperatorTrace

variable {G : Type*} [Group G] [DecidableEq G]

/-- For output in the base window and input in its translate by `h`, an
ordered pair of weighted copies `(i,j)` contributes when `i⁻¹ * j = h`. -/
public def copyDiagonalWeight (J : Finset G) (m : G → ℝ) (h : G) : ℝ :=
  ∑ i ∈ J, ∑ j ∈ J, if i⁻¹ * j = h then m i * m j else 0

/-- This is the simultaneous two-leg translate sum, with the input
weight extended by zero off the chosen copies. -/
public theorem copyDiagonalWeight_eq_translate_sum (J : Finset G) (m : G → ℝ) (h : G) :
    copyDiagonalWeight J m h = ∑ i ∈ J, m i * (if i * h ∈ J then m (i * h) else 0) := by
  unfold copyDiagonalWeight
  apply Finset.sum_congr rfl
  intro i _
  simp only [inv_mul_eq_iff_eq_mul, Finset.sum_ite_eq']
  split_ifs <;> simp

/-- Counting over relative copies preserves mass. The base retains the
coincident pairs; the positive shell retains all other pairs. -/
public theorem copyDiagonalWeight_split (J : Finset G) (m : G → ℝ)
    (hm : ∀ j ∈ J, 0 ≤ m j) (hmass : ∑ j ∈ J, m j = 1) :
    let c := copyDiagonalWeight J m
    (∀ h, 0 ≤ c h) ∧ c 1 = (∑ j ∈ J, m j ^ 2) ∧ c 1 ≤ 1 ∧
      HasSum c 1 ∧ HasSum (fun h : G ↦ if h = 1 then 0 else c h) (1 - c 1) := by
  let c := copyDiagonalWeight J m
  have hn (h : G) : 0 ≤ c h := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact mul_nonneg (hm i hi) (hm j hj)
    · exact le_rfl
  have hbase : c 1 = (∑ j ∈ J, m j ^ 2) := by
    unfold c copyDiagonalWeight
    apply Finset.sum_congr rfl
    intro i hi
    simp [inv_mul_eq_one, hi, pow_two]
  have hall : HasSum c 1 := by
    have hp (i j : G) : HasSum (fun h ↦ if i⁻¹ * j = h then m i * m j else 0)
        (m i * m j) := hasSum_ite_eq' (i⁻¹ * j) (m i * m j)
    have hsum := hasSum_sum (s := J) (fun i _ ↦ hasSum_sum (s := J) (fun j _ ↦ hp i j))
    change HasSum c (∑ i ∈ J, ∑ j ∈ J, m i * m j) at hsum
    rwa [← Finset.sum_mul_sum, hmass, one_mul] at hsum
  have hrest : HasSum (fun h : G ↦ if h = 1 then 0 else c h) (1 - c 1) := by
    refine (hall.sub (hasSum_ite_eq 1 (c 1))).congr_fun ?_
    intro h
    by_cases hh : h = 1 <;> simp [hh]
  exact ⟨hn, hbase, hall.summable.le_tsum 1 (fun h _ ↦ hn h) |>.trans_eq hall.tsum_eq,
    hall, hrest⟩

end Masullo.OperatorTrace
