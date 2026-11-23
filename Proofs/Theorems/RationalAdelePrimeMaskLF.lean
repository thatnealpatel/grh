module

public import Theorems.RationalThetaRadialCore
public import Theorems.RationalThetaPrimeMask

/-!
# The literal one-prime cut as a rational adelic Schwartz LF test

For a supplied unramified tensor, this realizes the disjoint unit cut with
the corrected outside-`S ∪ {p}` integer-ring factors (Masullo, §1.3.2,
p. 26). The finite support is contained in `ℤ̂`, and translations by `pℤ̂`
preserve both integrality and the unit condition at `p`.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "vₚ" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
local notation "Wf" => rationalFiniteIntegralAdeles

private theorem prime_valued_lt_one (p : Nat.Primes) : Valued.v ((p : ℕ) : (vₚ p).adicCompletion ℚ) < 1 := by
  let v := vₚ p
  have hgen : Rat.HeightOneSpectrum.natGenerator v = (p : ℕ) :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hmem : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    apply (Ideal.apply_mem_of_equiv_iff (f := e)).mp
    rw [map_natCast, ← hgen]
    exact (Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mp dvd_rfl
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := ℚ) v _).mpr hmem
  have hc := HeightOneSpectrum.adicCompletion.valued_coe ℚ v ((p : ℕ) : ℚ)
  change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((p : ℕ) : ℚ)) = _ at hc
  simpa only [map_natCast] using hc.trans_lt (by simpa only [map_natCast] using h)

/-- Cutting a rational unramified tensor by the unit condition at any finite
prime gives a Schwartz LF test on all additive adeles. -/
public theorem exists_rationalAdelePrimeMaskedLF (p : Nat.Primes) (b : 𝓢(ℝ, ℂ)) :
    ∃ g : RationalAdeleSchwartzLF, g.toUnion.val = rationalAdelePrimeMasked p b := by
  classical
  let H := rationalFiniteIntegralAdeles.map (AddMonoidHom.mulLeft ((p : ℕ) : F))
  refine exists_rationalAdeleLF_of_compactOpenStage _ H Wf
    (rationalAdeleBoxStage_isCompact_isOpen p.property.pos).2.1
    isCompact_rationalFiniteIntegralAdeles ?_ ?_ ?_
  · intro x hx
    change x ∉ (rationalIntegralAdeles : Set A) at hx
    simp [rationalAdelePrimeMasked, rationalAdeleUnramified, hx]
  · intro x z hz
    obtain ⟨w, hw, rfl⟩ := hz
    let y := x + rationalAdeleAt 0 (((p : ℕ) : F) * w)
    have hzW : ((p : ℕ) : F) * w ∈ Wf := by
      simpa only [nsmul_eq_mul] using rationalFiniteIntegralAdeles.nsmul_mem hw (p : ℕ)
    have hW : y ∈ (rationalIntegralAdeles : Set A) ↔ x ∈ (rationalIntegralAdeles : Set A) := by
      change x.2 + (rationalAdeleAt 0 (((p : ℕ) : F) * w)).2 ∈ Wf ↔ x.2 ∈ Wf
      rw [rationalAdeleAt_finite]
      refine ⟨fun h ↦ ?_, fun h ↦ rationalFiniteIntegralAdeles.add_mem h hzW⟩
      simpa only [add_sub_cancel_right] using rationalFiniteIntegralAdeles.sub_mem h hzW
    have hr : rationalAdeleReal y = rationalAdeleReal x := by
      rw [rationalAdeleReal_apply, rationalAdeleReal_apply]
      change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace + (rationalAdeleAt 0 (((p : ℕ) : F) * w)).1 Rat.infinitePlace) = _
      rw [map_add, ← rationalAdeleReal_apply, ← rationalAdeleReal_apply,
        rationalAdeleReal_at, add_zero]
    suffices hu : y ∈ rationalAdelePrimeUnits p ↔ x ∈ rationalAdelePrimeUnits p by
      change rationalAdelePrimeMasked p b y = _
      simp only [rationalAdelePrimeMasked, rationalAdeleUnramified, Set.indicator_apply, hW, hu, hr]
    let v := vₚ p
    let ev : F →+* v.adicCompletion ℚ := RestrictedProduct.evalRingHom _ v
    have hwv : Valued.v (ev w) ≤ 1 := hw v
    have hsmall : Valued.v (ev (((p : ℕ) : F) * w)) < 1 := by
      rw [map_mul, map_natCast, map_mul]
      exact (mul_le_mul_right hwv _).trans_lt (by rw [mul_one]; exact prime_valued_lt_one p)
    change Valued.v (ev (x.2 + (rationalAdeleAt 0 (((p : ℕ) : F) * w)).2)) = 1 ↔
      Valued.v (ev x.2) = 1
    rw [rationalAdeleAt_finite, map_add]
    -- Subtracting the same small coordinate proves the reverse implication.
    constructor
    · intro h
      have hlt : Valued.v (ev (((p : ℕ) : F) * w)) <
          Valued.v (ev x.2 + ev (((p : ℕ) : F) * w)) := h ▸ hsmall
      simpa only [add_sub_cancel_right, h] using Valuation.map_sub_eq_of_lt_left _ hlt
    · intro h
      exact (Valuation.map_add_eq_of_lt_left _ (h ▸ hsmall)).trans h
  · intro z
    have hW (t : ℝ) : rationalAdeleAt t z ∈ (rationalIntegralAdeles : Set A) ↔ z ∈ Wf := by
      change (rationalAdeleAt t z).2 ∈ Wf ↔ z ∈ Wf
      rw [rationalAdeleAt_finite]
    have hu (t : ℝ) : rationalAdeleAt t z ∈ rationalAdelePrimeUnits p ↔
        Valued.v (z (vₚ p)) = 1 := by
      change Valued.v ((rationalAdeleAt t z).2 (vₚ p)) = 1 ↔ Valued.v (z (vₚ p)) = 1
      rw [rationalAdeleAt_finite]
    by_cases h : Valued.v (z (vₚ p)) = 1 ∧ z ∈ Wf
    · exact ⟨b, fun t ↦ by
        simp [rationalAdelePrimeMasked, rationalAdeleUnramified, (hu t).mpr h.1, (hW t).mpr h.2]⟩
    · refine ⟨0, fun t ↦ ?_⟩
      have hn : rationalAdeleAt t z ∉ rationalAdelePrimeUnits p ∩ (rationalIntegralAdeles : Set A) :=
        fun ⟨h₁, h₂⟩ ↦ h ⟨(hu t).mp h₁, (hW t).mp h₂⟩
      simp only [zero_apply, rationalAdelePrimeMasked, rationalAdeleUnramified,
        Set.indicator_indicator, Set.indicator_of_notMem hn]

end Masullo
