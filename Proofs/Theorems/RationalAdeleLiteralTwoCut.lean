module

public import Lemmas.RationalAdeleResidues
public import Lemmas.RationalAdeleStageSampling
public import Theorems.RationalThetaPrimeMask
public import Theorems.RationalAdeleStageFourier
import Lemmas.SchwartzBandCorrection

/-!
# The literal first-prime unit cut on the level-two rational adelic cells

The integral-finite cylinder splits into the two level-two cells of indices
`0` and `2`. This identifies the actual coordinate cut in Masullo, §1.3.2,
pp. 26–27, for `P₁ = {2}`, without replacing it by a product away from `S`.
The cut does not preserve the two-zero-moment test space.
-/

open NumberField IsDedekindDomain MeasureTheory
open scoped FourierTransform SchwartzMap

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

local notation "E" => RationalAdeleSchwartzLF
local notation "U" => rationalAdelePrimeUnits p₂
local notation "C" j => rationalAdeleStageCell 2 j
local notation "B" j:max b:max => Set.indicator (C j) (fun x ↦ b (rationalAdeleReal x))
local notation "Pr" => (Fin (2 ^ 2) → 𝓢(ℝ, ℂ))
local notation "asm" => rationalAdeleLFAssembly 1

private theorem real_zero : rationalAdeleReal (0 : A) = 0 := by
  simpa only [map_zero, Rat.cast_zero] using rationalAdeleReal_algebraMap 0

private theorem rep_two_zero : rationalAdeleStageRepresentative 2 0 = 0 := by
  simp [rationalAdeleStageRepresentative]

private theorem zero_mem_cell_zero : (0 : A) ∈ C 0 :=
  (mem_rationalAdeleStageCell_iff (by decide) 0 _).mpr
    ⟨0, rationalFiniteIntegralAdeles.zero_mem, by simp [rep_two_zero]⟩

private theorem assembly_two_apply (p : Pr) (x : A) : (asm p).toUnion.val x = ∑ j, (B j (p j)) x := by
  rw [rationalAdeleLFAssembly_toUnion 1 p, rationalAdeleFactorialStageAssembly_val 1 p]
  change ((rationalAdeleStageCoordinates (by decide : 0 < 2)).symm p).val x = _
  rw [rationalAdeleStageCoordinates_symm_eq_boxSum]
  simp only [rationalAdeleBoxSum, one_mul, rationalAdeleBox_stageCell]

set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]

private theorem assembly_two_fourier_zero (p : Pr) : rationalAdeleFourier (asm p).toUnion.val 0 =
    (2 : ℂ)⁻¹ * ∑ j, ∫ t : ℝ, p j t := by
  have hw (b : 𝓢(ℝ, ℂ)) : (𝓕 b) 0 = ∫ t : ℝ, b t := by
    rw [congrFun (SchwartzMap.fourier_coe b) 0, Real.fourier_eq]
    simp
  rw [← rationalAdeleLFAssembly_fourier 1 p, rationalAdeleLFAssembly_toUnion,
    rationalAdeleFactorialStageAssembly_val,
    ← rationalAdeleStageCoordinates_eq_on_cell (rationalAdeleFactorialLevel_pos 1) _ zero_mem_cell_zero,
    LinearEquiv.apply_symm_apply, real_zero]
  change (rationalAdeleStageFourier 2 p 0) 0 = _
  rw [rationalAdeleStageFourier_apply]
  simp only [rep_two_zero, mul_zero, AddChar.map_zero_eq_one, map_one, mul_one,
    sum_apply, smul_apply, smul_eq_mul, hw, Finset.mul_sum, Nat.cast_ofNat]

/-- The level-two cell difference and its actual prime-unit cut are rational
LF tests. The two equal Haar weights cancel before cutting, but not after. -/
public theorem rationalAdeleLiteralTwoCut_moments (b : 𝓢(ℝ, ℂ)) :
    ∃ f g : E, f.toUnion.val = (B 2 b) - (B 0 b) ∧
      g.toUnion.val = Set.indicator U f.toUnion.val ∧ g.toUnion.val = B 2 b ∧
      f.toUnion.val 0 = -b 0 ∧ rationalAdeleFourier f.toUnion.val 0 = 0 ∧
      rationalAdeleFourier g.toUnion.val 0 = (1 / 2 : ℂ) * ∫ t : ℝ, b t := by
  classical
  let p : Pr := ![-b, 0, b, 0]
  let q : Pr := ![0, 0, b, 0]
  have hf : (asm p).toUnion.val = (B 2 b) - (B 0 b) := by
    funext x
    rw [assembly_two_apply]
    by_cases hx : x ∈ C 0 <;> simp [p, Fin.sum_univ_succ, Set.indicator, hx, sub_eq_add_neg, add_comm]
  have hg : (asm q).toUnion.val = B 2 b := by
    funext x
    rw [assembly_two_apply]
    simp [q, Fin.sum_univ_succ, Set.indicator]
  obtain ⟨h₀, h₂⟩ := rationalAdeleStageCell_two_eq_primeUnits
  have hcut : Set.indicator U ((B 2 b) - (B 0 b)) = B 2 b := by
    rw [h₀, h₂]
    funext x
    by_cases hx : x ∈ U <;> simp [Set.indicator, hx]
  have hz : (0 : A) ∉ C 2 := by
    have h := zero_mem_cell_zero
    rw [h₀] at h
    rw [h₂]
    exact fun h' ↦ h.2 h'.2
  refine ⟨asm p, asm q, hf, ?_, hg, ?_, ?_, ?_⟩
  · rw [hf, hcut, hg]
  · rw [hf, Pi.sub_apply, Set.indicator_of_notMem hz,
      Set.indicator_of_mem zero_mem_cell_zero, real_zero, zero_sub]
  · rw [assembly_two_fourier_zero]
    simp [p, Fin.sum_univ_succ, integral_neg]
  · rw [assembly_two_fourier_zero]
    simp [q, Fin.sum_univ_succ]

/-- The literal prime-two cut takes a two-zero-moment rational LF test to a
rational LF test with nonzero Fourier zero mode. -/
public theorem rationalAdeleLiteralTwoCut_loses_moment :
    ∃ f g : E, g.toUnion.val = Set.indicator U f.toUnion.val ∧
      f.toUnion.val 0 = 0 ∧ rationalAdeleFourier f.toUnion.val 0 = 0 ∧
      rationalAdeleFourier g.toUnion.val 0 ≠ 0 := by
  obtain ⟨f, g, _, hcut, _, h₀, hF, hG⟩ := rationalAdeleLiteralTwoCut_moments (bandSchwartzBump 2)
  refine ⟨f, g, hcut, ?_, hF, ?_⟩
  · simpa only [bandSchwartzBump_two_zero, neg_zero] using h₀
  · rw [hG]
    exact mul_ne_zero (by norm_num) bandSchwartzMass_bump_two_ne

end Masullo
