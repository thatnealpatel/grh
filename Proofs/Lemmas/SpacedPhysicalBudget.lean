module

public import Lemmas.SpacedColumnRecovery
public import Lemmas.SpacedGapSmoothPrice
public import Lemmas.SpacedProductFibers
import all Lemmas.SpacedProductFibers -- Unfold the fixed fiber only in the proof.
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-!
# A physical column budget for one spaced gap rectangle

Source: `a9dedc89666e:.godel/alice/spaced-product-cut.md:15–21`, unchanged at
`7f6ac23beeec` and Lean base `aaf7e47a237b`.

Scope: one fixed cofactor pair, with the first gap in a prescribed residue class
and interval, for `1 ≤ s ≤ L ≤ H`. Each actual smooth column modulus supplies a
crossing divisor. Incidences count modulus–point pairs; recovery accounts for
multiple physical columns at such a pair. The direction and physical divisor
caps are separate, and the original finite reciprocal sum is retained. There is
no coprimality requirement on `s` and `d`, and no asymptotic estimate here.

Owning check session: `01a20ff6-8a18-70ab-866d-9f5902b34d4c`.
-/

open scoped BigOperators

namespace SpacedPhysicalBudget

open AdaptivePlaneBin SpacedColumnRecovery SpacedGapIncidences SpacedGapModuli
open SpacedProductFibers (spacedGapFiber)

/-- Price the original columns at one cofactor pair and one first-gap residue.
The hypotheses on completions and actual moduli are only for this fixed fiber. -/
public theorem card_spacedGapFiber_le {Column : Type*} (columns : Finset Column)
    (h₁ h₂ : Column → ℕ) (completion : Column → Completion) (gap₁ gap₂ : Column → ℤ)
    (u₁ u₂ s : ℕ) (a₀ : ℤ) (center b₀ : ℝ)
    {x₁ x₂ q : ℤ} {L H C Z : ℝ} {X Ddir Dphys dMin : ℕ}
    (hs : 1 ≤ s) (hsL : (s : ℝ) ≤ L) (hLH : L ≤ H) (hq : 0 < q)
    (hmin : 0 < dMin) (hZ : 0 ≤ Z) :
    let F := spacedGapFiber columns h₁ h₂ gap₁ u₁ u₂ s a₀ center L
    let U := L / (s : ℝ)
    let j₀ := (center - (a₀ : ℝ)) / (s : ℝ)
    let g := Int.gcd x₁ x₂
    let A := x₂ / (g : ℤ)
    let B := x₁ / (g : ℤ)
    let M := (integerBox j₀ b₀ U H).card
    let R := ∑ m ∈ Finset.Ico 2 M, (1 / (m : ℝ)) * ∑ k ∈ multiplierMenu U m, 1 / (k : ℝ)
    2 * H < (A : ℝ) → B ≠ 0 →
    (∀ w ∈ F, |(gap₂ w : ℝ) - b₀| ≤ H) →
    (∀ w ∈ F, let d := (completion w).d
      d ∈ Nat.smoothNumbers (X + 1) ∧ IsCoprime (A * B) (d : ℤ) ∧ 8 * U * H < (d : ℝ)) →
    (∀ w ∈ F, dMin ≤ (completion w).d) →
    (∀ w ∈ F, Int.gcd x₁ ((completion w).d : ℤ) = 1) →
    (∀ w ∈ F, C ≤ ((completion w).c : ℝ) ∧ ((completion w).c : ℝ) ≤ C + Z) →
    (∀ w ∈ F, let k := completion w
      k.c * x₁ - (k.d : ℤ) * k.y₁ = q * gap₁ w ∧
      k.c * x₂ - (k.d : ℤ) * k.y₂ = q * gap₂ w) →
    Set.InjOn completion (↑F : Set Column) →
    (∀ w ∈ F, let N := A * gap₁ w - B * gap₂ w
      N ≠ 0 ∧ ((completion w).d : ℤ) ∣ N ∧ N.natAbs.divisors.card ≤ Dphys) →
    (∀ m ∈ Finset.Ico 2 M, ∀ k ∈ multiplierMenu U m, ∀ t ∈ crossingMenu B U H X m k,
      ∀ v, Direction A B (s : ℤ) U H m k t v →
        (directionForm A B (s : ℤ) v).natAbs.divisors.card ≤ Ddir) →
    (F.card : ℝ) ≤ 2 * √(8 * (X : ℝ) * U * H) * smoothEulerPrice X * (1 + (Ddir : ℝ) * R) *
      (Dphys : ℝ) * (1 + (⌊Z / (dMin : ℝ)⌋₊ : ℝ)) := by
  intro F U j₀ g A B M R hA hB hgap₂ hmoduli hdMin hgcd hc hrows hcompletion hphysical hDdir
  classical
  have hsZ : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
  have hs₁ : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs₀ : (0 : ℝ) < (s : ℝ) := zero_lt_one.trans_le hs₁
  have hL : 1 ≤ L := hs₁.trans hsL
  have hU : 1 ≤ U := (le_div_iff₀ hs₀).mpr (by simpa only [one_mul] using hsL)
  have hT : 1 ≤ 8 * U * H :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hU) (hL.trans hLH)
  have hAB : IsCoprime A B := by
    have hx₁ : x₁ ≠ 0 := by
      intro hx₁
      exact hB (by simp [B, hx₁])
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    rw [Int.gcd_comm A B]
    exact Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_left (m := x₂) hx₁
  -- Choose once for each distinct actual modulus, not from an input menu.
  let d (w : Column) := (completion w).d
  let actualModuli := F.image d
  have hexists (n : ℕ) (hn : n ∈ actualModuli) :
      ∃ f ∈ eligibleModuli A B U H X, f ∣ n := by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hdsm, hdAB, hdlarge⟩ := hmoduli w hw
    obtain ⟨f, hfd, hfsm, hflo, hfhi⟩ := exists_smooth_crossing_divisor hdsm hT hdlarge
    have hfhi' : (f : ℝ) ≤ 8 * (X : ℝ) * U * H := calc
      _ ≤ (X : ℝ) * (8 * U * H) := hfhi
      _ = _ := by ring
    have hfAB := hdAB.symm.of_isCoprime_of_dvd_left (Int.natCast_dvd_natCast.mpr hfd)
    exact ⟨f, mem_eligibleModuli.mpr ⟨⟨hfhi', hfsm⟩, hflo, hfAB⟩, hfd⟩
  let crossing (n : ℕ) : ℕ := if hn : n ∈ actualModuli then Classical.choose (hexists n hn) else 1
  have hcross (w : Column) (hw : w ∈ F) :
      crossing (d w) ∈ eligibleModuli A B U H X ∧ crossing (d w) ∣ d w := by
    have hd : d w ∈ actualModuli := Finset.mem_image_of_mem d hw
    simpa only [crossing, dite_eq_left hd] using Classical.choose_spec (hexists (d w) hd)
  -- The first coordinate is the integer parameter of the prescribed residue class.
  let point (w : Column) : ℤ × ℤ := ((gap₁ w - a₀) / (s : ℤ), gap₂ w)
  have hfirst (w : Column) (hw : w ∈ F) :
      |(gap₁ w : ℝ) - center| ≤ L ∧ gap₁ w ≡ a₀ [ZMOD (s : ℤ)] := by
    have hw' := hw
    simp only [F, spacedGapFiber, Finset.mem_filter] at hw'
    exact hw'.2.2.2
  have hgaps (w : Column) (hw : w ∈ F) :
      gap₁ w = a₀ + (s : ℤ) * (point w).1 ∧ gap₂ w = (point w).2 := by
    have hdvd := Int.modEq_iff_dvd.mp (hfirst w hw).2.symm
    have he := Int.ediv_mul_cancel hdvd
    change (point w).1 * (s : ℤ) = gap₁ w - a₀ at he
    rw [mul_comm] at he
    exact ⟨by omega, rfl⟩
  have hbox (w : Column) (hw : w ∈ F) :
      |((point w).1 : ℝ) - j₀| ≤ U ∧ |((point w).2 : ℝ) - b₀| ≤ H := by
    have hgapR : (gap₁ w : ℝ) = (a₀ : ℝ) + (s : ℝ) * ((point w).1 : ℝ) := by
      exact_mod_cast (hgaps w hw).1
    have hcenter : (s : ℝ) * j₀ = center - (a₀ : ℝ) := mul_div_cancel₀ _ hs₀.ne'
    have hscale : (gap₁ w : ℝ) - center = (s : ℝ) * (((point w).1 : ℝ) - j₀) := by
      rw [hgapR, mul_sub, hcenter]
      ring
    have hin := (hfirst w hw).1
    rw [hscale, abs_mul, abs_of_pos hs₀, mul_comm] at hin
    exact ⟨(le_div_iff₀ hs₀).mpr hin, hgap₂ w hw⟩
  have hsLZ : ((s : ℤ) : ℝ) ≤ L := by simpa only [Int.cast_natCast] using hsL
  -- Recovery charges each assigned pair by the physical divisor cap and the residue interval.
  have hrecover := card_columns_le F completion gap₁ gap₂ (fun w => crossing (d w)) point
    hsZ hsLZ hLH hq hmin hZ (by simpa only [Int.cast_natCast] using hbox) hgaps
    hdMin hgcd hc hrows hcompletion (by simpa only [Int.cast_natCast] using hcross) hphysical
  have hprice : (incidenceCount a₀ (s : ℤ) A B j₀ b₀ L H X : ℝ) ≤
      2 * (√(8 * (X : ℝ) * U * H) * smoothEulerPrice X) * (1 + (Ddir : ℝ) * R) := by
    simpa only [Int.cast_natCast] using
      (incidenceCount_le_smoothEulerPrice (a₀ := a₀) (j₀ := j₀) (b₀ := b₀) (X := X)
        hL hLH hsZ hsLZ hA hB hAB (by simpa only [Int.cast_natCast] using hDdir))
  have hfloor : 0 ≤ (1 + (⌊Z / (dMin : ℝ)⌋₊ : ℝ)) :=
    add_nonneg zero_le_one (Nat.cast_nonneg _)
  calc
    (F.card : ℝ) ≤ (incidenceCount a₀ (s : ℤ) A B j₀ b₀ L H X : ℝ) *
        (Dphys : ℝ) * (1 + (⌊Z / (dMin : ℝ)⌋₊ : ℝ)) := by
      exact_mod_cast hrecover
    _ ≤ _ := by
      rw [mul_assoc (2 : ℝ) (√(8 * (X : ℝ) * U * H)) (smoothEulerPrice X)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprice (Nat.cast_nonneg _)) hfloor

end SpacedPhysicalBudget
