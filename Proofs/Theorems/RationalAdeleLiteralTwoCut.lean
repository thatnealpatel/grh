module

public import Lemmas.RationalAdeleResidues
public import Lemmas.RationalAdeleStageSampling
public import Theorems.RationalThetaPrimeMask

/-!
# The literal first-prime unit cut on the level-two rational adelic cells

The integral-finite cylinder splits into the two level-two cells of indices
`0` and `2`. This identifies the actual coordinate cut in Masullo, §1.3.2,
pp. 26–27, for `P₁ = {2}`, without replacing it by a product away from `S`.
-/

open NumberField IsDedekindDomain

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "K" v:max => HeightOneSpectrum.adicCompletion ℚ v
local notation "O" v:max => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "p₂" => (Subtype.mk 2 Nat.prime_two : Nat.Primes)
local notation "v₂" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) p₂
local notation "ι" => algebraMap ℚ A
local notation "W" => rationalIntegralAdeles
local notation "Wf" => rationalFiniteIntegralAdeles

private theorem valued_two_lt_one : Valued.v (2 : K v₂) < 1 := by
  have hgen : Rat.HeightOneSpectrum.natGenerator v₂ = 2 :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p₂)
  have hmem : (2 : 𝓞 ℚ) ∈ (v₂).asIdeal := by
    let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
    have hdiv : Rat.HeightOneSpectrum.natGenerator v₂ ∣ 2 := by rw [hgen]
    have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff v₂).mp hdiv
    change (2 : ℤ) ∈ _ at h
    exact (Ideal.apply_mem_of_equiv_iff (f := e)).mp (by simpa only [map_ofNat] using h)
  have h : (v₂).valuation ℚ (algebraMap (𝓞 ℚ) ℚ 2) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem v₂ _).mpr hmem
  have hc := HeightOneSpectrum.adicCompletion.valued_coe ℚ v₂ (2 : ℚ)
  change Valued.v (algebraMap ℚ (K v₂) 2) = _ at hc
  simpa only [map_ofNat] using hc.trans_lt (by simpa only [map_ofNat] using h)

private theorem valued_two_mul_lt_one {z : K v₂} (hz : Valued.v z ≤ 1) :
    Valued.v (2 * z) < 1 := by
  rw [map_mul]
  exact (mul_le_mul_right hz _).trans_lt (by simpa only [mul_one] using valued_two_lt_one)

private theorem mem_two_cells_of_integral (x : A) (hx : x ∈ W) :
    x ∈ rationalAdeleStageCell 2 0 ∨ x ∈ rationalAdeleStageCell 2 2 := by
  have ht : ι (2 : ℚ) * (ι ((2 : ℚ)⁻¹) * x) ∈ W := by
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ (by norm_num : (2 : ℚ) ≠ 0), map_one, one_mul]
  obtain ⟨j, hj⟩ := rationalAdele_residue_exists (N := 2) (by decide) _ ht
  fin_cases j
  · left
    norm_num [rationalAdeleStageCell] at hj ⊢
    exact hj
  · right
    norm_num [rationalAdeleStageCell] at hj ⊢
    exact hj

/-- At level two, the actual prime-unit cut keeps the cell of index `2` and
removes the cell of index `0` from the integral-finite cylinder. -/
public theorem rationalAdeleStageCell_two_eq_primeUnits :
    rationalAdeleStageCell 2 0 = (W : Set A) \ rationalAdelePrimeUnits ⟨2, Nat.prime_two⟩ ∧
    rationalAdeleStageCell 2 2 = (W : Set A) ∩ rationalAdelePrimeUnits ⟨2, Nat.prime_two⟩ := by
  let eval : F →+* K v₂ := RestrictedProduct.evalRingHom _ v₂
  have hmul {z : F} (hz : z ∈ Wf) : (2 : F) * z ∈ Wf := by
    simpa only [two_mul] using rationalFiniteIntegralAdeles.add_mem hz hz
  have h₀ {x : A} (hx : x ∈ rationalAdeleStageCell 2 0) :
      x ∈ W ∧ x ∉ rationalAdelePrimeUnits p₂ := by
    obtain ⟨z, hz, h⟩ : ∃ z ∈ Wf, x.2 = (2 : F) * z := by
      simpa [rationalAdeleStageRepresentative] using
        (mem_rationalAdeleStageCell_iff (by decide : 0 < 2) 0 x).mp hx
    constructor
    · change x.2 ∈ Wf
      rw [h]
      exact hmul hz
    · change Valued.v (eval x.2) ≠ 1
      rw [h, map_mul, map_ofNat]
      exact (valued_two_mul_lt_one (hz v₂)).ne
  have h₂ {x : A} (hx : x ∈ rationalAdeleStageCell 2 2) :
      x ∈ W ∧ x ∈ rationalAdelePrimeUnits p₂ := by
    obtain ⟨z, hz, h⟩ : ∃ z ∈ Wf, x.2 = 1 + (2 : F) * z := by
      simpa [rationalAdeleStageRepresentative, show (2 : ℚ) / 2 = 1 by norm_num] using
        (mem_rationalAdeleStageCell_iff (by decide : 0 < 2) 2 x).mp hx
    constructor
    · change x.2 ∈ Wf
      rw [h]
      exact rationalFiniteIntegralAdeles.add_mem (fun v ↦ (O v).one_mem) (hmul hz)
    · change Valued.v (eval x.2) = 1
      rw [h, map_add, map_one, map_mul, map_ofNat]
      have ht := valued_two_mul_lt_one (show Valued.v (eval z) ≤ 1 from hz v₂)
      calc
        _ = Valued.v (1 : K v₂) :=
          Valuation.map_add_eq_of_lt_left _ (by simpa only [map_one] using ht)
        _ = 1 := map_one _
  constructor
  · ext x
    refine ⟨h₀, fun hx ↦ ?_⟩
    exact (mem_two_cells_of_integral x hx.1).resolve_right (fun h ↦ hx.2 (h₂ h).2)
  · ext x
    refine ⟨h₂, fun hx ↦ ?_⟩
    exact (mem_two_cells_of_integral x hx.1).resolve_left (fun h ↦ (h₀ h).2 hx.2)

end Masullo
