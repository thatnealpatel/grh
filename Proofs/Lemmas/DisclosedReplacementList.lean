module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Fixed-mask counting with disclosed replacement lists

Source: `069b23dd:.godel/bob/replacement-frequency-lists.md:7–25`
(unchanged at `5e6920d1`). Owning check session: `01a20938-230d-71be-9082-772ff1e0dec6`.

Fix the removed slots, target signs on retained slots, and disclosed slots.
Under the original product law, `z` is the whole disclosed block, `x` the hidden
retained block, and `y` the hidden removed block. Their finite laws have mass one.
The source frequency is `sourceDisclosed z + g x + u y`; the partner frequency
is `targetDisclosed z + f x + s`. The disclosed source sum includes all disclosed
slots, while the target sum includes only disclosed retained slots with their
new signs. Likewise `g` uses the original retained signs and `f` the target
signs. The dictionary `D z` sees only the labeled disclosed values. Admissibility
of `s` may depend on the entire source. The two-hit mass counts sources, not
their witnesses.

This is the fixed-mask product-law step after dropping source separation. It
bounds the mass by `N * Cr * Cv` using at most `N` centers per disclosed value
and uniform interval prices `Cr` for `u` at radius `2π/t` and `Cv` for `f` at
radius `(2π+1)/t`. It specializes to `4 * N * Ur * Uv` at prices `2 * Ur` and
`2 * Uv`. The Fourier estimates, interpolation, and union over masks are
outside its scope.
-/

open scoped BigOperators

namespace Masullo.DisclosedReplacementList

/-- The law of a whole block of labeled values. Equal frequencies need not
identify atoms. -/
public structure FiniteWeightLaw (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

/-- The original weight of an event, counting each eligible atom once. -/
@[expose] public noncomputable def FiniteWeightLaw.mass {α : Type*} [Fintype α]
    (P : FiniteWeightLaw α) (event : α → Prop) : ℝ := by
  classical
  exact ∑ x, if event x then P.weight x else 0

private theorem mass_nonneg {α : Type*} [Fintype α] (P : FiniteWeightLaw α)
    (p : α → Prop) : 0 ≤ P.mass p := by
  classical
  unfold FiniteWeightLaw.mass
  exact Finset.sum_nonneg fun x _ ↦ by split <;> first | exact P.nonneg x | exact le_rfl

private theorem mass_mono {α : Type*} [Fintype α] (P : FiniteWeightLaw α)
    {p q : α → Prop} (h : ∀ x, p x → q x) : P.mass p ≤ P.mass q := by
  classical
  unfold FiniteWeightLaw.mass
  refine Finset.sum_le_sum fun x _ ↦ ?_
  by_cases hp : p x
  · simp only [ite_eq_left hp, ite_eq_left (h x hp), le_refl]
  · rw [ite_eq_right hp]
    split <;> first | exact P.nonneg x | exact le_rfl

private theorem mass_exists_le_sum {α ι : Type*} [Fintype α] (P : FiniteWeightLaw α)
    (A : Finset ι) (p : ι → α → Prop) :
    P.mass (fun x ↦ ∃ a ∈ A, p a x) ≤ ∑ a ∈ A, P.mass (p a) := by
  classical
  unfold FiniteWeightLaw.mass
  rw [Finset.sum_comm (s := A)]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  have hn : ∀ a ∈ A, 0 ≤ (if p a x then P.weight x else 0) := fun a _ ↦ by
    split <;> first | exact P.nonneg x | exact le_rfl
  by_cases h : ∃ a ∈ A, p a x
  · rw [ite_eq_left h]
    obtain ⟨a, ha, hp⟩ := h
    simpa only [ite_eq_left hp] using (Finset.single_le_sum hn ha)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg hn

/-- Both frequency hits, with a post-hoc existential replacement. The
predicate `admissible z x y s` can, for example, require `s` to be the signed
sum of an actual replacement block meeting the partner restrictions. -/
@[expose] public def TwoHits {Z X Y : Type*} (t : ℝ)
    (sourceDisclosed targetDisclosed : Z → ℝ) (g f : X → ℝ) (u : Y → ℝ)
    (D : Z → Finset ℝ) (admissible : Z → X → Y → ℝ → Prop) (z : Z) (x : X) (y : Y) : Prop :=
  |sourceDisclosed z + g x + u y| ≤ 2 * Real.pi / t ∧
    ∃ a ∈ D z, ∃ s : ℝ, admissible z x y s ∧ |s - a| ≤ 1 / t ∧
      |targetDisclosed z + f x + s| ≤ 2 * Real.pi / t

/-- The mass of the two-hit source event under the independent product law.
No law on replacements is involved. -/
@[expose] public noncomputable def twoHitMass {Z X Y : Type*} [Fintype Z] [Fintype X] [Fintype Y]
    (t : ℝ) (Pz : FiniteWeightLaw Z) (Px : FiniteWeightLaw X) (Py : FiniteWeightLaw Y)
    (sourceDisclosed targetDisclosed : Z → ℝ) (g f : X → ℝ) (u : Y → ℝ)
    (D : Z → Finset ℝ) (admissible : Z → X → Y → ℝ → Prop) : ℝ :=
  ∑ z, Pz.weight z * ∑ x, Px.weight x *
    Py.mass (TwoHits t sourceDisclosed targetDisclosed g f u D admissible z x)

/-- For a fixed mask, the two-hit source mass is bounded by the list budget times
one concentration price on each hidden block. The prices hold at every center. -/
public theorem twoHitMass_le {Z X Y : Type*} [Fintype Z] [Fintype X] [Fintype Y]
    {t : ℝ} (_ht : 0 < t) (Pz : FiniteWeightLaw Z) (Px : FiniteWeightLaw X) (Py : FiniteWeightLaw Y)
    (sourceDisclosed targetDisclosed : Z → ℝ) (g f : X → ℝ) (u : Y → ℝ)
    (D : Z → Finset ℝ) (admissible : Z → X → Y → ℝ → Prop) {N : ℕ} {Cr Cv : ℝ}
    (hcard : ∀ z, (D z).card ≤ N)
    (hr : ∀ c : ℝ, Py.mass (fun y ↦ |u y - c| ≤ 2 * Real.pi / t) ≤ Cr)
    (hv : ∀ c : ℝ, Px.mass (fun x ↦ |f x - c| ≤ (2 * Real.pi + 1) / t) ≤ Cv) :
    twoHitMass t Pz Px Py sourceDisclosed targetDisclosed g f u D admissible ≤
      (N : ℝ) * Cr * Cv := by
  classical
  let hit := TwoHits t sourceDisclosed targetDisclosed g f u D admissible
  let retained (z : Z) (a : ℝ) (x : X) :=
    |f x - (-(targetDisclosed z + a))| ≤ (2 * Real.pi + 1) / t
  let eligible (z : Z) (x : X) := ∃ a ∈ D z, retained z a x
  have hCr : 0 ≤ Cr := (mass_nonneg Py _).trans (hr 0)
  have hCv : 0 ≤ Cv := (mass_nonneg Px _).trans (hv 0)
  -- The actual replacement witness forces membership in a retained interval.
  have hnecessary (z : Z) (x : X) (y : Y) (h : hit z x y) : eligible z x := by
    obtain ⟨_, a, ha, s, _, hs, hp⟩ := h
    refine ⟨a, ha, ?_⟩
    change |f x - (-(targetDisclosed z + a))| ≤ (2 * Real.pi + 1) / t
    calc
      _ = |(targetDisclosed z + f x + s) + (a - s)| := by congr 1; ring
      _ ≤ |targetDisclosed z + f x + s| + |a - s| := abs_add_le _ _
      _ ≤ 2 * Real.pi / t + 1 / t := add_le_add hp (by simpa only [abs_sub_comm a s] using hs)
      _ = _ := (add_div _ _ _).symm
  -- Condition on both the disclosed and the retained labels for the source hit.
  have hslice (z : Z) (x : X) : Py.mass (hit z x) ≤ if eligible z x then Cr else 0 := by
    by_cases hx : eligible z x
    · rw [ite_eq_left hx]
      refine (mass_mono Py (fun y h ↦ ?_)).trans (hr (-(sourceDisclosed z + g x)))
      have heq : u y - (-(sourceDisclosed z + g x)) = sourceDisclosed z + g x + u y := by ring
      rw [heq]
      exact h.1
    · have hn (y : Y) : ¬ hit z x y := fun h ↦ hx (hnecessary z x y h)
      simp [FiniteWeightLaw.mass, hx, hn]
  -- Union over the dictionary after fixing `z`, then use the same cap for every `z`.
  have hretained (z : Z) : Px.mass (eligible z) ≤ (N : ℝ) * Cv := calc
    _ ≤ ∑ a ∈ D z, Px.mass (retained z a) := mass_exists_le_sum Px (D z) (retained z)
    _ ≤ ∑ _a ∈ D z, Cv := Finset.sum_le_sum fun a _ ↦ hv (-(targetDisclosed z + a))
    _ = ((D z).card : ℝ) * Cv := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard z)) hCv
  have hhidden (z : Z) : (∑ x, Px.weight x * Py.mass (hit z x)) ≤ (N : ℝ) * Cr * Cv := calc
    _ ≤ ∑ x, Px.weight x * (if eligible z x then Cr else 0) :=
      Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hslice z x) (Px.nonneg x)
    _ = Px.mass (eligible z) * Cr := by
      rw [FiniteWeightLaw.mass, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hx : eligible z x <;> simp [hx]
    _ ≤ ((N : ℝ) * Cv) * Cr := mul_le_mul_of_nonneg_right (hretained z) hCr
    _ = _ := mul_right_comm _ _ _
  calc
    _ ≤ ∑ z, Pz.weight z * ((N : ℝ) * Cr * Cv) :=
      Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_left (hhidden z) (Pz.nonneg z)
    _ = _ := by rw [← Finset.sum_mul, Pz.total, one_mul]

/-- Specialization to the two prices supplied by the window-majorant step. -/
public theorem twoHitMass_le_four {Z X Y : Type*} [Fintype Z] [Fintype X] [Fintype Y]
    {t : ℝ} (ht : 0 < t) (Pz : FiniteWeightLaw Z) (Px : FiniteWeightLaw X) (Py : FiniteWeightLaw Y)
    (sourceDisclosed targetDisclosed : Z → ℝ) (g f : X → ℝ) (u : Y → ℝ)
    (D : Z → Finset ℝ) (admissible : Z → X → Y → ℝ → Prop) {N : ℕ} {Ur Uv : ℝ}
    (hcard : ∀ z, (D z).card ≤ N)
    (hr : ∀ c : ℝ, Py.mass (fun y ↦ |u y - c| ≤ 2 * Real.pi / t) ≤ 2 * Ur)
    (hv : ∀ c : ℝ, Px.mass (fun x ↦ |f x - c| ≤ (2 * Real.pi + 1) / t) ≤ 2 * Uv) :
    twoHitMass t Pz Px Py sourceDisclosed targetDisclosed g f u D admissible ≤
      4 * (N : ℝ) * Ur * Uv := calc
  _ ≤ (N : ℝ) * (2 * Ur) * (2 * Uv) :=
    twoHitMass_le ht Pz Px Py sourceDisclosed targetDisclosed g f u D admissible hcard hr hv
  _ = _ := by ring

end Masullo.DisclosedReplacementList
