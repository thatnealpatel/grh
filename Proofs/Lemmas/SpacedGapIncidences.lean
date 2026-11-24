module

public import Lemmas.SpacedGapModuli
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite spaced-gap incidences

Source: `a9dedc89666e:.godel/alice/spaced-product-cut.md:15–23`, used by
`.godel/alice/forced-output-cuts.md:57`. Lean pin: `52090c0259f5`.

Scope: the finite `s ≤ L` count of pairs of a smooth crossing modulus and a
nonvanishing affine solution in the translated box. This sums the actual
occupancy tails with a uniform direction-form divisor bound; it does not
estimate the smooth menus or give an asymptotic bound.

Owning check session: `01a20f88-43d7-7049-9647-cb18c5a08d70`.
-/

open scoped BigOperators

namespace SpacedGapIncidences

open SpacedGapModuli

/-- All `X`-smooth `8UV < f ≤ 8XUV` coprime to `AB`, including unoccupied moduli. -/
@[expose] public noncomputable def eligibleModuli (A B : ℤ) (U V : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Nat.smoothNumbersUpTo ⌊8 * (X : ℝ) * U * V⌋₊ (X + 1)).filter fun f =>
    8 * U * V < (f : ℝ) ∧ IsCoprime (f : ℤ) (A * B)

public theorem mem_eligibleModuli {A B : ℤ} {U V : ℝ} {X f : ℕ} :
    f ∈ eligibleModuli A B U V X ↔
      ((f : ℝ) ≤ 8 * (X : ℝ) * U * V ∧ f ∈ Nat.smoothNumbers (X + 1)) ∧
      8 * U * V < (f : ℝ) ∧ IsCoprime (f : ℤ) (A * B) := by
  simp only [eligibleModuli, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
  constructor
  · rintro ⟨⟨hf, hsm⟩, h⟩
    exact ⟨⟨(Nat.le_floor_iff' hsm.1).mp hf, hsm⟩, h⟩
  · rintro ⟨⟨hf, hsm⟩, h⟩
    exact ⟨⟨Nat.le_floor hf, hsm⟩, h⟩

/-- The number of actual modulus–point pairs, summed over the modulus fibers. -/
@[expose] public noncomputable def incidenceCount (a₀ s A B : ℤ) (j₀ b₀ L H : ℝ)
    (X : ℕ) : ℕ :=
  ∑ f ∈ eligibleModuli A B (L / (s : ℝ)) H X, (affineSolutions a₀ s A B j₀ b₀ L H f).card

private theorem filter_eligibleModuli_eq_crossingModuli
    {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {X m : ℕ} :
    (eligibleModuli A B (L / (s : ℝ)) H X).filter
        (fun f => m + 1 ≤ (affineSolutions a₀ s A B j₀ b₀ L H f).card) =
      crossingModuli a₀ s A B j₀ b₀ L H X m := by
  ext f
  simp only [Finset.mem_filter, mem_eligibleModuli, mem_crossingModuli, and_assoc]

private theorem sum_occupancy_indicators {n M : ℕ} (hn : n ≤ M) :
    (∑ m ∈ Finset.Ico 2 M, if m + 1 ≤ n then 1 else 0) = n - 2 := by
  rw [← Finset.card_filter]
  have h : (Finset.Ico 2 M).filter (fun m => m + 1 ≤ n) = Finset.Ico 2 n := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [h, Nat.card_Ico]

/-- Each fiber contributes its first two points (or fewer), then one unit at each
met occupancy threshold. Interchanging the sums counts each modulus once per
met threshold, with no multiplicity from the choice of a short direction. -/
private theorem incidenceCount_eq_sum_crossingModuli
    {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {X : ℕ} :
    let U := L / (s : ℝ)
    let F := eligibleModuli A B U H X
    let M := (integerBox j₀ b₀ U H).card
    let S := affineSolutions a₀ s A B j₀ b₀ L H
    incidenceCount a₀ s A B j₀ b₀ L H X =
      (∑ f ∈ F, min (S f).card 2) +
        ∑ m ∈ Finset.Ico 2 M, (crossingModuli a₀ s A B j₀ b₀ L H X m).card := by
  intro U F M S
  calc
    _ = ∑ f ∈ F, (min (S f).card 2 +
        ∑ m ∈ Finset.Ico 2 M, if m + 1 ≤ (S f).card then 1 else 0) := by
      change (∑ f ∈ F, (S f).card) = _
      apply Finset.sum_congr rfl
      intro f _
      have hcard : (S f).card ≤ M :=
        Finset.card_le_card fun _ hp => mem_integerBox.mpr (mem_affineSolutions.mp hp).1
      rw [sum_occupancy_indicators hcard]
      omega
    _ = (∑ f ∈ F, min (S f).card 2) +
        ∑ m ∈ Finset.Ico 2 M, ∑ f ∈ F, if m + 1 ≤ (S f).card then 1 else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm (s := F) (t := Finset.Ico 2 M)]
    _ = _ := by
      apply congrArg ((∑ f ∈ F, min (S f).card 2) + ·)
      apply Finset.sum_congr rfl
      intro m _
      rw [← Finset.card_filter, filter_eligibleModuli_eq_crossingModuli]

/-- The finite count of actual incidences in the translated spaced rectangle.
The first two possible points per modulus are charged to `2 * F.card`; the
remaining thresholds run from `2` through `M - 1`, where `M` is the actual
integer-box cardinality. This tail is empty for `M ≤ 2`. -/
public theorem incidenceCount_le
    {a₀ s A B : ℤ} {j₀ b₀ L H : ℝ} {X D : ℕ}
    (hL : 1 ≤ L) (hLH : L ≤ H) (hs : 1 ≤ s) (hsL : (s : ℝ) ≤ L)
    (hA : 2 * H < (A : ℝ)) (hB : B ≠ 0) (hAB : IsCoprime A B) :
    let U := L / (s : ℝ)
    let F := eligibleModuli A B U H X
    let M := (integerBox j₀ b₀ U H).card
    (∀ m ∈ Finset.Ico 2 M, ∀ k ∈ multiplierMenu U m, ∀ t ∈ crossingMenu B U H X m k,
      ∀ v, Direction A B s U H m k t v → (directionForm A B s v).natAbs.divisors.card ≤ D) →
    incidenceCount a₀ s A B j₀ b₀ L H X ≤ 2 * F.card +
      ∑ m ∈ Finset.Ico 2 M, ∑ k ∈ multiplierMenu U m, (crossingMenu B U H X m k).card * 2 * D := by
  intro U F M hD
  rw [incidenceCount_eq_sum_crossingModuli]
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ _f ∈ F, 2 := Finset.sum_le_sum fun _ _ => Nat.min_le_right _ _
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  · apply Finset.sum_le_sum
    intro m hm
    exact card_crossingModuli_le hL hLH hs hsL hA hB hAB (Finset.mem_Ico.mp hm).1 (hD m hm)

end SpacedGapIncidences
