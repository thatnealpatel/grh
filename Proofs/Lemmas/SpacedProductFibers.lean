module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.Ring

/-!
# From spaced gaps to one-product deletion fibers

Source: `a9dedc89666e:.godel/alice/spaced-product-cut.md:5–27`, unchanged from
scan pin `42fca4a` to `03fd044fb601`. Consumer: the one-product deletion at
exponent `.88875` in that source.

Scope: from fixed-cofactor spaced **column** counts (both spacing branches) and
menu counts with a smooth-cofactor discount to the count of the actual deletion
fiber. Use column indices if columns have identical projections; neither the gap
nor the product is used as a deduplication key. The residue and the center may
vary with the cofactor pair; this prices one such choice per pair, not a union
over choices. There is no constraint on the other product or the column modulus.
Swapping the row roles amounts to exchanging the cofactor and gap projections.

`SpacedGapIncidences.incidenceCount_le_smoothEulerPrice` (landed at `759c00687ea9`)
prices modulus/point incidences for `s ≤ L`. To use it as a column price here
requires upstream rectangle-to-column recovery. This adapter proves neither that
recovery nor the `s > L` column price, the smooth-menu estimates, or the
`q`-exponent asymptotic.

Owning check session: `01a20fbf-64d4-7ae0-ac41-09f991160e63`.
-/

open scoped BigOperators
open Int

namespace SpacedProductFibers

/-- Solvability of the signed product congruence, including the empty-fiber criterion. -/
public theorem productCongruence_solvable_iff (e : ℕ) (h a : ℤ) :
    (∃ δ : ℤ, δ * h ≡ a [ZMOD (e : ℤ)]) ↔ (Int.gcd h (e : ℤ) : ℤ) ∣ a := by
  constructor
  · rintro ⟨δ, hδ⟩
    have hsub := dvd_trans (Int.gcd_dvd_right h (e : ℤ)) (Int.modEq_iff_dvd.mp hδ)
    have hmul := dvd_mul_of_dvd_right (Int.gcd_dvd_left h (e : ℤ)) δ
    simpa using dvd_add hsub hmul
  · rintro ⟨k, hk⟩
    refine ⟨k * Int.gcdA h (e : ℤ), Int.modEq_iff_dvd.mpr ⟨k * Int.gcdB h (e : ℤ), ?_⟩⟩
    rw [hk, Int.gcd_eq_gcd_ab h (e : ℤ)]
    ring

private theorem modEq_mul_right_iff {e : ℕ} (he : 0 < e) (h δ r : ℤ) :
    (δ * h ≡ r * h [ZMOD (e : ℤ)]) ↔ δ ≡ r [ZMOD ((e / Int.gcd h (e : ℤ) : ℕ) : ℤ)] := by
  rw [Int.natCast_ediv]
  constructor
  · intro hEq
    simpa only [Int.gcd_comm] using Int.ModEq.cancel_right_div_gcd (Int.natCast_pos.mpr he) hEq
  · intro hEq
    rw [Int.modEq_iff_dvd] at hEq ⊢
    obtain ⟨k, hk⟩ := hEq
    obtain ⟨m, hm⟩ := Int.gcd_dvd_left h (e : ℤ)
    refine ⟨k * m, ?_⟩
    calc
      r * h - δ * h = (r - δ) * h := (Int.sub_mul _ _ _).symm
      _ = ((e : ℤ) / Int.gcd h (e : ℤ) * k) * ((Int.gcd h (e : ℤ) : ℤ) * m) :=
        congrArg₂ (· * ·) hk hm
      _ = ((e : ℤ) / Int.gcd h (e : ℤ) * Int.gcd h (e : ℤ)) * (k * m) := by ring
      _ = _ := by rw [Int.ediv_mul_cancel (Int.gcd_dvd_right h (e : ℤ))]

/-- For positive `e`, a solvable product congruence is exactly one gap class modulo `e / gcd(h,e)`. -/
public theorem productCongruence_iff_modEq {e : ℕ} (he : 0 < e) {h a : ℤ}
    (ha : (Int.gcd h (e : ℤ) : ℤ) ∣ a) :
    ∃ r : ℤ, ∀ δ : ℤ, (δ * h ≡ a [ZMOD (e : ℤ)]) ↔
      δ ≡ r [ZMOD ((e / Int.gcd h (e : ℤ) : ℕ) : ℤ)] := by
  obtain ⟨r, hr⟩ := (productCongruence_solvable_iff e h a).mpr ha
  exact ⟨r, fun δ => ⟨fun hδ => (modEq_mul_right_iff he h δ r).mp (hδ.trans hr.symm),
    fun hδ => ((modEq_mul_right_iff he h δ r).mpr hδ).trans hr⟩⟩

/-- The original columns in a fixed cofactor pair, signed gap interval, and gap class. -/
public noncomputable def spacedGapFiber {Column : Type*} (columns : Finset Column)
    (h₁ h₂ : Column → ℕ) (gap : Column → ℤ) (u v s : ℕ) (r : ℤ) (center L : ℝ) :
    Finset Column :=
  columns.filter fun c => h₁ c = u ∧ h₂ c = v ∧ |(gap c : ℝ) - center| ≤ L ∧
    gap c ≡ r [ZMOD (s : ℤ)]

/-- The actual columns deleted by one product class and a gap interval, with one choice
of residue and center after each cofactor pair. -/
public noncomputable def productFiber {Column : Type*} (columns : Finset Column)
    (h₁ h₂ : Column → ℕ) (gap : Column → ℤ) (e : ℕ) (a : ℕ → ℕ → ℤ)
    (center : ℕ → ℕ → ℝ) (L : ℝ) : Finset Column :=
  columns.filter fun c => (gap c * (h₂ c : ℤ) ≡ a (h₁ c) (h₂ c) [ZMOD (e : ℤ)]) ∧
    |(gap c : ℝ) - center (h₁ c) (h₂ c)| ≤ L

private noncomputable def widthFactor (H L : ℝ) (s : ℕ) : ℝ :=
  √(H * max 1 (L / (s : ℝ)))

private theorem widthFactor_div_le {H L : ℝ} {e l : ℕ} (hH : 0 ≤ H) (hl : 0 < l)
    (hle : l ∣ e) : widthFactor H L (e / l) ≤ √(l : ℝ) * widthFactor H L e := by
  have hl₀ : (0 : ℝ) < l := Nat.cast_pos.mpr hl
  have hl₁ : (1 : ℝ) ≤ l := Nat.one_le_cast.mpr hl
  have hratio : L / ((e / l : ℕ) : ℝ) = (l : ℝ) * (L / (e : ℝ)) := by
    rw [Nat.cast_div hle hl₀.ne', div_div_eq_mul_div, ← mul_div_assoc, mul_comm L]
  calc
    widthFactor H L (e / l) ≤ √((l : ℝ) * (H * max 1 (L / (e : ℝ)))) := by
      unfold widthFactor
      apply Real.sqrt_le_sqrt
      rw [hratio, mul_left_comm (l : ℝ)]
      refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) hH
      · exact hl₁.trans (le_mul_of_one_le_right hl₀.le (le_max_left _ _))
      · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hl₀.le
    _ = _ := Real.sqrt_mul hl₀.le _

private theorem sum_gcd_weights_le {V : Finset ℕ} {e : ℕ} {H L C₂ : ℝ}
    (he : 0 < e) (hH : 0 ≤ H) (hC₂ : 0 ≤ C₂)
    (hdiscount : ∀ l ∈ e.divisors, ((V.filter fun v => l ∣ v).card : ℝ) ≤ C₂ / √(l : ℝ)) :
    (∑ v ∈ V, widthFactor H L (e / v.gcd e)) ≤
      (e.divisors.card : ℝ) * (C₂ * widthFactor H L e) := by
  let B (l : ℕ) := V.filter fun v => v.gcd e = l
  have hmaps (v : ℕ) (_ : v ∈ V) : v.gcd e ∈ e.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right v e, he.ne'⟩
  calc
    (∑ v ∈ V, widthFactor H L (e / v.gcd e)) =
        ∑ l ∈ e.divisors, (B l).card * widthFactor H L (e / l) := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun v => widthFactor H L (e / v.gcd e))]
      refine Finset.sum_congr rfl fun l _ => ?_
      calc
        _ = ∑ _v ∈ B l, widthFactor H L (e / l) := by
          refine Finset.sum_congr rfl fun v hv => ?_
          rw [(Finset.mem_filter.mp hv).2]
        _ = _ := by simp [nsmul_eq_mul]
    _ ≤ ∑ _l ∈ e.divisors, C₂ * widthFactor H L e := by
      refine Finset.sum_le_sum fun l hl => ?_
      have hle := Nat.dvd_of_mem_divisors hl
      have hlpos := Nat.pos_of_dvd_of_pos hle he
      have hsqrt : 0 < √(l : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hlpos)
      have hsub : B l ⊆ V.filter fun v => l ∣ v := by
        intro v hv
        obtain ⟨hv, hvl⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hv, hvl ▸ Nat.gcd_dvd_left v e⟩
      have hcard : ((B l).card : ℝ) ≤ C₂ / √(l : ℝ) :=
        (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hdiscount l hl)
      calc
        _ ≤ C₂ / √(l : ℝ) * widthFactor H L (e / l) :=
          mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)
        _ ≤ C₂ / √(l : ℝ) * (√(l : ℝ) * widthFactor H L e) :=
          mul_le_mul_of_nonneg_left (widthFactor_div_le hH hlpos hle) (div_nonneg hC₂ hsqrt.le)
        _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hsqrt.ne']
    _ = _ := by simp [nsmul_eq_mul]

/-- The finite from-gaps-to-products estimate. `C₁` prices the other cofactor menu,
`C₂ / √l` prices second cofactors divisible by `l`, and `K` is a common prefactor
for the two fixed-cofactor column prices (including any constant in the `s > L`
branch). The count is of columns, not distinct gaps, products, or cofactor pairs. -/
public theorem card_productFiber_le {Column : Type*} (columns : Finset Column)
    (h₁ h₂ : Column → ℕ) (gap : Column → ℤ) (U V : Finset ℕ) (e : ℕ)
    (a : ℕ → ℕ → ℤ) (center : ℕ → ℕ → ℝ) {H L K C₁ C₂ : ℝ}
    (he : 1 ≤ e ∧ (e : ℝ) ≤ H) (hL : 1 ≤ L) (hLH : L ≤ H)
    (hK : 0 ≤ K) (hC₂ : 0 ≤ C₂)
    (hcofactors : ∀ c ∈ columns, h₁ c ∈ U ∧ h₂ c ∈ V)
    (hother : (U.card : ℝ) ≤ C₁)
    (hdiscount : ∀ l ∈ e.divisors, ((V.filter fun v => l ∣ v).card : ℝ) ≤ C₂ / √(l : ℝ))
    (hgap_le : ∀ u ∈ U, ∀ v ∈ V, ∀ s : ℕ, 0 < s → (s : ℝ) ≤ L → ∀ r : ℤ,
      ((spacedGapFiber columns h₁ h₂ gap u v s r (center u v) L).card : ℝ) ≤
        K * √(H * (L / (s : ℝ))))
    (hgap_gt : ∀ u ∈ U, ∀ v ∈ V, ∀ s : ℕ, L < (s : ℝ) → ∀ r : ℤ,
      ((spacedGapFiber columns h₁ h₂ gap u v s r (center u v) L).card : ℝ) ≤ K * √H) :
    ((productFiber columns h₁ h₂ gap e a center L).card : ℝ) ≤
      K * C₁ * C₂ * (e.divisors.card : ℝ) * √(H * max 1 (L / (e : ℝ))) := by
  let D := productFiber columns h₁ h₂ gap e a center L
  let F (p : ℕ × ℕ) := D.filter fun c => (h₂ c, h₁ c) = p
  have hE : 0 < e := he.1
  have hH : 0 ≤ H := zero_le_one.trans (hL.trans hLH)
  have hC₁ : 0 ≤ C₁ := (Nat.cast_nonneg _).trans hother
  -- Each deleted column lies in exactly its original cofactor-pair fiber.
  have hpartition : (D.card : ℝ) = ∑ v ∈ V, ∑ u ∈ U, ((F (v, u)).card : ℝ) := by
    have hmaps : Set.MapsTo (fun c => (h₂ c, h₁ c)) (↑D) (↑(V ×ˢ U)) := by
      intro c hc
      obtain ⟨hu, hv⟩ := hcofactors c (Finset.mem_filter.mp hc).1
      exact Finset.mem_product.mpr ⟨hv, hu⟩
    have hcard := congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_eq_sum_card_fiberwise hmaps)
    simpa only [Nat.cast_sum, Finset.sum_product, F] using hcard
  have hlocal (v : ℕ) (hv : v ∈ V) (u : ℕ) (hu : u ∈ U) :
      ((F (v, u)).card : ℝ) ≤ K * widthFactor H L (e / v.gcd e) := by
    let l := v.gcd e
    let s := e / l
    have hl : 0 < l := Nat.gcd_pos_of_pos_right v hE
    have hs : 0 < s := Nat.div_pos (Nat.le_of_dvd hE (Nat.gcd_dvd_right v e)) hl
    have hs₀ : (0 : ℝ) < s := Nat.cast_pos.mpr hs
    have hlcast : Int.gcd (v : ℤ) (e : ℤ) = l := Int.gcd_natCast_natCast v e
    by_cases ha : (l : ℤ) ∣ a u v
    · obtain ⟨r, hr⟩ := productCongruence_iff_modEq hE (h := (v : ℤ)) (a := a u v)
        (by simpa only [hlcast] using ha)
      rw [hlcast] at hr
      have hfiber : F (v, u) = spacedGapFiber columns h₁ h₂ gap u v s r (center u v) L := by
        ext c
        simp only [F, D, productFiber, spacedGapFiber, Finset.mem_filter, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hc, hprod, hin⟩, hv', hu'⟩
          refine ⟨hc, hu', hv', ?_, (hr _).mp ?_⟩
          · simpa only [hu', hv'] using hin
          · simpa only [hu', hv'] using hprod
        · rintro ⟨hc, hu', hv', hin, hgap⟩
          refine ⟨⟨hc, ?_, ?_⟩, hv', hu'⟩
          · simpa only [hu', hv'] using (hr _).mpr hgap
          · simpa only [hu', hv'] using hin
      rw [hfiber]
      change _ ≤ K * √(H * max 1 (L / (s : ℝ)))
      by_cases hsL : (s : ℝ) ≤ L
      · rw [max_eq_right ((le_div_iff₀ hs₀).mpr (by simpa only [one_mul] using hsL))]
        exact hgap_le u hu v hv s hs hsL r
      · have hLs : L < (s : ℝ) := lt_of_not_ge hsL
        rw [max_eq_left ((div_le_iff₀ hs₀).mpr (by simpa only [one_mul] using hLs.le)), mul_one]
        exact hgap_gt u hu v hv s hLs r
    · have hempty : F (v, u) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro c hc
        simp only [F, D, productFiber, Finset.mem_filter, Prod.mk.injEq] at hc
        obtain ⟨⟨_, hprod, _⟩, hv', hu'⟩ := hc
        apply ha
        rw [← hlcast]
        exact (productCongruence_solvable_iff e (v : ℤ) (a u v)).mp
          ⟨gap c, by simpa only [hu', hv'] using hprod⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hK (Real.sqrt_nonneg _)
  calc
    (D.card : ℝ) = ∑ v ∈ V, ∑ u ∈ U, ((F (v, u)).card : ℝ) := hpartition
    _ ≤ ∑ v ∈ V, ∑ _u ∈ U, K * widthFactor H L (e / v.gcd e) :=
      Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun u hu => hlocal v hv u hu
    _ = ∑ v ∈ V, (U.card : ℝ) * (K * widthFactor H L (e / v.gcd e)) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ v ∈ V, C₁ * (K * widthFactor H L (e / v.gcd e)) :=
      Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right hother
        (mul_nonneg hK (Real.sqrt_nonneg _))
    _ = (C₁ * K) * ∑ v ∈ V, widthFactor H L (e / v.gcd e) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ (C₁ * K) * ((e.divisors.card : ℝ) * (C₂ * widthFactor H L e)) :=
      mul_le_mul_of_nonneg_left (sum_gcd_weights_le hE hH hC₂ hdiscount) (mul_nonneg hC₁ hK)
    _ = _ := by unfold widthFactor; ring

end SpacedProductFibers
