module

public import Lemmas.SpacedPhysicalBudget
import all Lemmas.SpacedProductFibers -- Unfold the fixed fiber only in the proofs.
import Mathlib.Tactic.Linarith

/-!
# Physical column budgets for sparse spacing

Source: `a9dedc89666e:.godel/alice/spaced-product-cut.md:15–27`, on the Lean pin
`00e46ec751ca`, unchanged in the assigned base `542813dac8cf`.

Scope: for `1 ≤ L ≤ H` and `L < s`, partition the actual columns at a fixed
cofactor pair and first-gap residue by their exact first gap. Apply
`SpacedPhysicalBudget.card_spacedGapFiber_le` at width and spacing one to each
part, keeping its finite reciprocal sum and separate divisor caps. At most
three gaps contribute, including when the gap menu is empty. A uniform unit
price `K * √H` gives the `hgap_gt` bound of
`SpacedProductFibers.card_productFiber_le` with common prefactor `3 * K`.
There is no asymptotic estimate or additional coprimality assumption here.

Owning check session: `01a21012-2ca1-71e9-a51f-6efd061fa400`.
-/

open scoped BigOperators

namespace SpacedSparseBudget

open Int AdaptivePlaneBin SpacedColumnRecovery SpacedGapIncidences SpacedGapModuli
open SpacedProductFibers (spacedGapFiber)

/-- The signed integer gaps in the original interval and residue, whether or not
there is a column at that gap. -/
public noncomputable def sparseGaps (s : ℕ) (r : ℤ) (center L : ℝ) : Finset ℤ :=
  (Finset.Icc ⌈center - L⌉ ⌊center + L⌋).filter fun g => g ≡ r [ZMOD (s : ℤ)]

public theorem mem_sparseGaps {s : ℕ} {r g : ℤ} {center L : ℝ} :
    g ∈ sparseGaps s r center L ↔ |(g : ℝ) - center| ≤ L ∧ g ≡ r [ZMOD (s : ℤ)] := by
  simp only [sparseGaps, Finset.mem_filter, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  constructor
  · rintro ⟨⟨hl, hu⟩, hr⟩
    exact ⟨⟨by linarith, by linarith⟩, hr⟩
  · rintro ⟨⟨hl, hu⟩, hr⟩
    exact ⟨⟨by linarith, by linarith⟩, hr⟩

/-- The original columns, retaining multiplicity of their projections, at an exact
first gap and cofactor pair. -/
public noncomputable def exactGapFiber {Column : Type*} (columns : Finset Column)
    (h₁ h₂ : Column → ℕ) (gap₁ : Column → ℤ) (u v : ℕ) (g : ℤ) : Finset Column :=
  columns.filter fun w => h₁ w = u ∧ h₂ w = v ∧ gap₁ w = g

public theorem mem_exactGapFiber {Column : Type*} {columns : Finset Column}
    {h₁ h₂ : Column → ℕ} {gap₁ : Column → ℤ} {u v : ℕ} {g : ℤ} {w : Column} :
    w ∈ exactGapFiber columns h₁ h₂ gap₁ u v g ↔ w ∈ columns ∧ h₁ w = u ∧ h₂ w = v ∧ gap₁ w = g := by
  simp only [exactGapFiber, Finset.mem_filter]

/-- The physical price at first-gap center `g` and half-width and spacing one. -/
@[expose] public noncomputable def unitGapBudget (g : ℤ) (b₀ H Z : ℝ)
    (X Ddir Dphys dMin : ℕ) : ℝ :=
  let M := (integerBox (g : ℝ) b₀ 1 H).card
  let R := ∑ m ∈ Finset.Ico 2 M, (1 / (m : ℝ)) * ∑ k ∈ multiplierMenu 1 m, 1 / (k : ℝ)
  2 * √(8 * (X : ℝ) * H) * smoothEulerPrice X * (1 + (Ddir : ℝ) * R) *
    (Dphys : ℝ) * (1 + (⌊Z / (dMin : ℝ)⌋₊ : ℝ))

/-- The physical hypotheses of the width-one, spacing-one estimate on an exact-gap
fiber `F`. The reduced row coefficients are `A` and `B`. -/
public structure UnitGapData {Column : Type*} (F : Finset Column)
    (completion : Column → Completion) (gap₁ gap₂ : Column → ℤ) (x₁ x₂ q A B g : ℤ)
    (b₀ H C Z : ℝ) (X Ddir Dphys dMin : ℕ) : Prop where
  q_pos : 0 < q
  dMin_pos : 0 < dMin
  Z_nonneg : 0 ≤ Z
  A_large : 2 * H < (A : ℝ)
  B_ne : B ≠ 0
  gap₂_le : ∀ w ∈ F, |(gap₂ w : ℝ) - b₀| ≤ H
  moduli : ∀ w ∈ F, let d := (completion w).d
    d ∈ Nat.smoothNumbers (X + 1) ∧ IsCoprime (A * B) (d : ℤ) ∧ 8 * H < (d : ℝ)
  dMin_le : ∀ w ∈ F, dMin ≤ (completion w).d
  gcd_eq_one : ∀ w ∈ F, Int.gcd x₁ ((completion w).d : ℤ) = 1
  c_mem : ∀ w ∈ F, C ≤ ((completion w).c : ℝ) ∧ ((completion w).c : ℝ) ≤ C + Z
  rows : ∀ w ∈ F, let k := completion w
    k.c * x₁ - (k.d : ℤ) * k.y₁ = q * gap₁ w ∧
    k.c * x₂ - (k.d : ℤ) * k.y₂ = q * gap₂ w
  injOn : Set.InjOn completion (↑F : Set Column)
  physical : ∀ w ∈ F, let N := A * gap₁ w - B * gap₂ w
    N ≠ 0 ∧ ((completion w).d : ℤ) ∣ N ∧ N.natAbs.divisors.card ≤ Dphys
  direction : ∀ m ∈ Finset.Ico 2 (integerBox (g : ℝ) b₀ 1 H).card,
    ∀ k ∈ multiplierMenu 1 m, ∀ t ∈ crossingMenu B 1 H X m k,
      ∀ v, Direction A B 1 1 H m k t v → (directionForm A B 1 v).natAbs.divisors.card ≤ Ddir

private theorem card_exactGapFiber_le {Column : Type*} (columns : Finset Column)
    (h₁ h₂ : Column → ℕ) (completion : Column → Completion) (gap₁ gap₂ : Column → ℤ)
    (u v : ℕ) (g : ℤ) (b₀ : ℝ) {x₁ x₂ q : ℤ} {H C Z : ℝ} {X Ddir Dphys dMin : ℕ}
    (hH : 1 ≤ H)
    (hdata : let d := Int.gcd x₁ x₂
      UnitGapData (exactGapFiber columns h₁ h₂ gap₁ u v g) completion gap₁ gap₂
        x₁ x₂ q (x₂ / (d : ℤ)) (x₁ / (d : ℤ)) g b₀ H C Z X Ddir Dphys dMin) :
    ((exactGapFiber columns h₁ h₂ gap₁ u v g).card : ℝ) ≤ unitGapBudget g b₀ H Z X Ddir Dphys dMin := by
  classical
  have hF : spacedGapFiber (columns.filter fun w => gap₁ w = g) h₁ h₂ gap₁ u v 1 0 (g : ℝ) 1 =
      exactGapFiber columns h₁ h₂ gap₁ u v g := by
    ext w
    simp only [spacedGapFiber, mem_exactGapFiber, Finset.mem_filter, Int.natCast_one, Int.modEq_one,
      and_true]
    constructor
    · rintro ⟨⟨hw, hg⟩, hu, hv, _⟩
      exact ⟨hw, hu, hv, hg⟩
    · rintro ⟨hw, hu, hv, hg⟩
      exact ⟨⟨hw, hg⟩, hu, hv, by simp [hg]⟩
  have hbound := SpacedPhysicalBudget.card_spacedGapFiber_le
    (columns.filter fun w => gap₁ w = g) h₁ h₂ completion gap₁ gap₂ u v 1 0 (g : ℝ) b₀
    (x₁ := x₁) (x₂ := x₂) (L := 1) (H := H) (C := C) (X := X) (Ddir := Ddir) (Dphys := Dphys)
    le_rfl (by simp) hH hdata.q_pos hdata.dMin_pos hdata.Z_nonneg
  simp only [hF, Nat.cast_one, Int.cast_zero, sub_zero, div_one, mul_one] at hbound
  exact hbound hdata.A_large hdata.B_ne hdata.gap₂_le hdata.moduli hdata.dMin_le
    hdata.gcd_eq_one hdata.c_mem hdata.rows hdata.injOn hdata.physical hdata.direction

/-- When `L < s`, the possible first gaps inject into an integer interval of
half-width one. The bound does not require the gap set to be nonempty. -/
public theorem card_sparseGaps_le {s : ℕ} {r : ℤ} {center L : ℝ}
    (hL : 1 ≤ L) (hLs : L < (s : ℝ)) : (sparseGaps s r center L).card ≤ 3 := by
  have hs : 0 < (s : ℝ) := zero_lt_one.trans (hL.trans_lt hLs)
  let j (g : ℤ) := (g - r) / (s : ℤ)
  let z := (center - (r : ℝ)) / (s : ℝ)
  have hj (g : ℤ) (hg : g ∈ sparseGaps s r center L) : j g * (s : ℤ) = g - r :=
    Int.ediv_mul_cancel (Int.modEq_iff_dvd.mp (mem_sparseGaps.mp hg).2.symm)
  calc
    (sparseGaps s r center L).card ≤ (Finset.Icc ⌈z - 1⌉ ⌊z + 1⌋).card := by
      refine Finset.card_le_card_of_injOn j ?_ ?_
      · intro g hg
        have hjR : (j g : ℝ) * (s : ℝ) = (g : ℝ) - (r : ℝ) := by exact_mod_cast hj g hg
        have hz : z * (s : ℝ) = center - (r : ℝ) := div_mul_cancel₀ _ hs.ne'
        have hscale : ((j g : ℝ) - z) * (s : ℝ) = (g : ℝ) - center := by
          rw [sub_mul, hjR, hz]
          ring
        have hin := (mem_sparseGaps.mp hg).1.trans hLs.le
        rw [← hscale, abs_mul, abs_of_pos hs] at hin
        have hn : |(j g : ℝ) - z| ≤ 1 := by
          simpa only [div_self hs.ne'] using (le_div_iff₀ hs).mpr hin
        obtain ⟨hl, hu⟩ := abs_le.mp hn
        exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩
      · intro g hg g' hg' heq
        have h := hj g hg
        rw [heq, hj g' hg'] at h
        omega
    _ ≤ 3 := by
      have hb : (⌊z + 1⌋ : ℤ) ≤ ⌈z - 1⌉ + 2 := by
        exact_mod_cast (show ((⌊z + 1⌋ : ℤ) : ℝ) ≤ ((⌈z - 1⌉ : ℤ) : ℝ) + 2 by
          linarith [Int.floor_le (z + 1), Int.le_ceil (z - 1)])
      rw [Int.card_Icc, Int.toNat_le]
      omega

/-- Partition the fixed-cofactor column count by exact first gaps. Each summand is
obtained from the physical theorem with half-width and spacing one; no column-count
hypothesis for the original interval is used. The sum identity also holds for an
empty menu, when it forces the original fiber to have cardinality zero. -/
public theorem card_spacedGapFiber_le_sum {Column : Type*} (columns : Finset Column)
    (h₁ h₂ : Column → ℕ) (completion : Column → Completion) (gap₁ gap₂ : Column → ℤ)
    (u v s : ℕ) (r : ℤ) (center b₀ : ℝ) {x₁ x₂ q : ℤ} {L H C Z : ℝ} {X dMin : ℕ}
    (Ddir Dphys : ℤ → ℕ) (hH : 1 ≤ H)
    (hdata : let d := Int.gcd x₁ x₂
      ∀ g ∈ sparseGaps s r center L,
        UnitGapData (exactGapFiber columns h₁ h₂ gap₁ u v g) completion gap₁ gap₂
          x₁ x₂ q (x₂ / (d : ℤ)) (x₁ / (d : ℤ)) g b₀ H C Z X (Ddir g) (Dphys g) dMin) :
    ((spacedGapFiber columns h₁ h₂ gap₁ u v s r center L).card : ℝ) ≤
      ∑ g ∈ sparseGaps s r center L, unitGapBudget g b₀ H Z X (Ddir g) (Dphys g) dMin := by
  classical
  let F := spacedGapFiber columns h₁ h₂ gap₁ u v s r center L
  let G := sparseGaps s r center L
  have hmaps : Set.MapsTo gap₁ (↑F : Set Column) (↑G : Set ℤ) := by
    intro w hw
    simp only [Finset.mem_coe, F, spacedGapFiber, Finset.mem_filter] at hw
    exact mem_sparseGaps.mpr hw.2.2.2
  have hfiber (g : ℤ) (hg : g ∈ G) : (F.filter fun w => gap₁ w = g) =
      exactGapFiber columns h₁ h₂ gap₁ u v g := by
    obtain ⟨hbox, hres⟩ := mem_sparseGaps.mp hg
    ext w
    simp only [F, spacedGapFiber, mem_exactGapFiber, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, hu, hv, _, _⟩, hgap⟩
      exact ⟨hw, hu, hv, hgap⟩
    · rintro ⟨hw, hu, hv, hgap⟩
      exact ⟨⟨hw, hu, hv, hgap ▸ hbox, hgap ▸ hres⟩, hgap⟩
  calc
    (F.card : ℝ) = ∑ g ∈ G, ((F.filter fun w => gap₁ w = g).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    _ ≤ _ := Finset.sum_le_sum fun g hg => by
      rw [hfiber g hg]
      exact card_exactGapFiber_le columns h₁ h₂ completion gap₁ gap₂ u v g b₀ hH (hdata g hg)

/-- The sparse branch for `SpacedProductFibers.card_productFiber_le`: with unit
price at most `K * √H`, use a common prefactor of `3 * K` (or larger) in the
product-fiber assembler. -/
public theorem card_spacedGapFiber_le_of_sparse {Column : Type*} (columns : Finset Column)
    (h₁ h₂ : Column → ℕ) (completion : Column → Completion) (gap₁ gap₂ : Column → ℤ)
    (u v s : ℕ) (r : ℤ) (center b₀ : ℝ) {x₁ x₂ q : ℤ} {L H C Z K : ℝ} {X dMin : ℕ}
    (Ddir Dphys : ℤ → ℕ) (hL : 1 ≤ L) (hLH : L ≤ H) (hLs : L < (s : ℝ)) (hK : 0 ≤ K)
    (hdata : let d := Int.gcd x₁ x₂
      ∀ g ∈ sparseGaps s r center L,
        UnitGapData (exactGapFiber columns h₁ h₂ gap₁ u v g) completion gap₁ gap₂
          x₁ x₂ q (x₂ / (d : ℤ)) (x₁ / (d : ℤ)) g b₀ H C Z X (Ddir g) (Dphys g) dMin)
    (hprice : ∀ g ∈ sparseGaps s r center L, unitGapBudget g b₀ H Z X (Ddir g) (Dphys g) dMin ≤ K * √H) :
    ((spacedGapFiber columns h₁ h₂ gap₁ u v s r center L).card : ℝ) ≤ 3 * K * √H := by
  calc
    _ ≤ ∑ g ∈ sparseGaps s r center L, unitGapBudget g b₀ H Z X (Ddir g) (Dphys g) dMin :=
      card_spacedGapFiber_le_sum columns h₁ h₂ completion gap₁ gap₂ u v s r center b₀
        Ddir Dphys (hL.trans hLH) hdata
    _ ≤ ∑ _g ∈ sparseGaps s r center L, K * √H := Finset.sum_le_sum hprice
    _ = ((sparseGaps s r center L).card : ℝ) * (K * √H) := by simp [nsmul_eq_mul]
    _ ≤ 3 * K * √H := by
      have hcard : ((sparseGaps s r center L).card : ℝ) ≤ 3 := by
        exact_mod_cast card_sparseGaps_le (r := r) (center := center) hL hLs
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hK (Real.sqrt_nonneg _))

end SpacedSparseBudget
