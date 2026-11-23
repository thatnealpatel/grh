module

public import Theorems.RationalThetaRadialCore
public import Theorems.RationalThetaPrimeMask

/-!
# Literal one- and two-prime cuts as rational adelic Schwartz LF tests

For a supplied unramified tensor, these realize the disjoint unit cuts with
the corrected outside-`S ∪ P` integer-ring factors (Masullo, §1.3.2,
p. 26). The finite support is contained in `ℤ̂`, and translations by `pℤ̂`
preserve both integrality and the unit condition at `p`. For two primes
use the intersection of their translation subgroups.
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

private noncomputable def primeStage (p : Nat.Primes) : AddSubgroup F :=
  rationalFiniteIntegralAdeles.map (AddMonoidHom.mulLeft ((p : ℕ) : F))

private theorem isOpen_primeStage (p : Nat.Primes) : IsOpen (primeStage p : Set F) :=
  (rationalAdeleBoxStage_isCompact_isOpen p.property.pos).2.1

private theorem primeStage_le (p : Nat.Primes) : primeStage p ≤ Wf := by
  rintro z ⟨w, hw, rfl⟩
  change ((p : ℕ) : F) * w ∈ Wf
  simpa only [nsmul_eq_mul] using rationalFiniteIntegralAdeles.nsmul_mem hw (p : ℕ)

private theorem primeUnit_add_iff (p : Nat.Primes) (x z : F) (hz : z ∈ primeStage p) :
    Valued.v ((x + z) (vₚ p)) = 1 ↔ Valued.v (x (vₚ p)) = 1 := by
  obtain ⟨w, hw, rfl⟩ := hz
  let v := vₚ p
  let ev : F →+* v.adicCompletion ℚ := RestrictedProduct.evalRingHom _ v
  have hwv : Valued.v (ev w) ≤ 1 := hw v
  have hsmall : Valued.v (ev (((p : ℕ) : F) * w)) < 1 := by
    rw [map_mul, map_natCast, map_mul]
    exact (mul_le_mul_right hwv _).trans_lt (by rw [mul_one]; exact prime_valued_lt_one p)
  change Valued.v (ev (x + ((p : ℕ) : F) * w)) = 1 ↔ Valued.v (ev x) = 1
  rw [map_add]
  -- Subtracting the same small coordinate proves the reverse implication.
  constructor
  · intro h
    have hlt : Valued.v (ev (((p : ℕ) : F) * w)) <
        Valued.v (ev x + ev (((p : ℕ) : F) * w)) := h ▸ hsmall
    simpa only [add_sub_cancel_right, h] using Valuation.map_sub_eq_of_lt_left _ hlt
  · intro h
    exact (Valuation.map_add_eq_of_lt_left _ (h ▸ hsmall)).trans h

private theorem exists_finiteMaskedLF (b : 𝓢(ℝ, ℂ)) (U : Set F) (H : AddSubgroup F)
    (hH : IsOpen (H : Set F)) (hsub : H ≤ Wf)
    (hU : ∀ x z : F, z ∈ H → (x + z ∈ U ↔ x ∈ U)) :
    ∃ g : RationalAdeleSchwartzLF, g.toUnion.val =
      Set.indicator {x : A | x.2 ∈ U} (rationalAdeleUnramified b) := by
  classical
  refine exists_rationalAdeleLF_of_compactOpenStage _ H Wf
    hH isCompact_rationalFiniteIntegralAdeles ?_ ?_ ?_
  · intro x hx
    change x ∉ (rationalIntegralAdeles : Set A) at hx
    simp [rationalAdeleUnramified, hx]
  · intro x z hz
    let y := x + rationalAdeleAt 0 z
    have hzW := hsub hz
    have hW : y ∈ (rationalIntegralAdeles : Set A) ↔ x ∈ (rationalIntegralAdeles : Set A) := by
      change x.2 + (rationalAdeleAt 0 z).2 ∈ Wf ↔ x.2 ∈ Wf
      rw [rationalAdeleAt_finite]
      refine ⟨fun h ↦ ?_, fun h ↦ rationalFiniteIntegralAdeles.add_mem h hzW⟩
      simpa only [add_sub_cancel_right] using rationalFiniteIntegralAdeles.sub_mem h hzW
    have hr : rationalAdeleReal y = rationalAdeleReal x := by
      rw [rationalAdeleReal_apply, rationalAdeleReal_apply]
      change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace + (rationalAdeleAt 0 z).1 Rat.infinitePlace) = _
      rw [map_add, ← rationalAdeleReal_apply, ← rationalAdeleReal_apply,
        rationalAdeleReal_at, add_zero]
    have hu : y.2 ∈ U ↔ x.2 ∈ U := by
      change x.2 + (rationalAdeleAt 0 z).2 ∈ U ↔ x.2 ∈ U
      rw [rationalAdeleAt_finite, hU _ _ hz]
    change (Set.indicator {x : A | x.2 ∈ U} (rationalAdeleUnramified b)) y = _
    simp only [rationalAdeleUnramified, Set.indicator_apply, Set.mem_ofPred_eq, hW, hu, hr]
  · intro z
    have hW (t : ℝ) : rationalAdeleAt t z ∈ (rationalIntegralAdeles : Set A) ↔ z ∈ Wf := by
      change (rationalAdeleAt t z).2 ∈ Wf ↔ z ∈ Wf
      rw [rationalAdeleAt_finite]
    by_cases hu : z ∈ U <;> by_cases hw : z ∈ Wf
    · exact ⟨b, fun t ↦ by simp [rationalAdeleUnramified, hW, hu, hw]⟩
    all_goals exact ⟨0, fun t ↦ by simp [rationalAdeleUnramified, hW, hu, hw]⟩

/-- Cutting a rational unramified tensor by the unit condition at any finite
prime gives a Schwartz LF test on all additive adeles. -/
public theorem exists_rationalAdelePrimeMaskedLF (p : Nat.Primes) (b : 𝓢(ℝ, ℂ)) :
    ∃ g : RationalAdeleSchwartzLF, g.toUnion.val = rationalAdelePrimeMasked p b :=
  exists_finiteMaskedLF b {x | Valued.v (x (vₚ p)) = 1} (primeStage p)
    (isOpen_primeStage p) (primeStage_le p) (primeUnit_add_iff p)

/-- The joint unit cut at `p` and `q` of a supplied unramified LF tensor
is a single Schwartz LF test on all additive adeles. -/
public theorem exists_rationalAdeleUnramifiedTwoPrimeMaskLF (p q : Nat.Primes) (b : 𝓢(ℝ, ℂ))
    (f : RationalAdeleSchwartzLF) (hf : f.toUnion.val = rationalAdeleUnramified b) :
    ∃ g : RationalAdeleSchwartzLF, g.toUnion.val =
      Set.indicator (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q) f.toUnion.val := by
  rw [hf]
  exact exists_finiteMaskedLF b {x | Valued.v (x (vₚ p)) = 1 ∧ Valued.v (x (vₚ q)) = 1}
    (primeStage p ⊓ primeStage q) ((isOpen_primeStage p).inter (isOpen_primeStage q))
    (inf_le_left.trans (primeStage_le p))
    (fun x z hz ↦ (primeUnit_add_iff p x z hz.1).and (primeUnit_add_iff q x z hz.2))

end Masullo
