module

public import Lemmas.RationalAdeleStageSampling
public import Theorems.RationalThetaPrimeMask
public import Theorems.RationalAdeleStageFourier
import Lemmas.RationalAdeleResidues

/-! # The Fourier zero mode of the rational joint unit cut at 2 and 3 -/

open NumberField IsDedekindDomain MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "F" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "W" => rationalIntegralAdeles
local notation "Wf" => rationalFiniteIntegralAdeles
local notation "ι" => algebraMap ℚ A
local notation "vₚ" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
local notation "p₂" => (Subtype.mk 2 Nat.prime_two : Nat.Primes)
local notation "p₃" => (Subtype.mk 3 Nat.prime_three : Nat.Primes)
local notation "U" => Set.inter (rationalAdelePrimeUnits p₂) (rationalAdelePrimeUnits p₃)
local notation "C" => rationalAdeleStageCell 6

private def sixIndex (n : Fin 6) : Fin (6 ^ 2) := ⟨6 * n.val, by omega⟩

private theorem rep_sixIndex (n : Fin 6) :
    rationalAdeleStageRepresentative 6 (sixIndex n) = (n.val : F) := by
  rw [rationalAdeleStageRepresentative]
  change algebraMap ℚ F (((6 * n.val : ℕ) : ℚ) / 6) = _
  rw [Nat.cast_mul, Nat.cast_ofNat, mul_comm (6 : ℚ), mul_div_cancel_right₀ _ (by norm_num),
    map_natCast]

private theorem exists_sixIndex_of_integral (x : A) (hx : x ∈ W) :
    ∃ n : Fin 6, x ∈ C (sixIndex n) := by
  have ht : ι (6 : ℚ) * (ι ((6 : ℚ)⁻¹) * x) ∈ W := by
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ (by norm_num : (6 : ℚ) ≠ 0), map_one, one_mul]
  obtain ⟨n, hn⟩ := rationalAdele_residue_exists (N := 6) (by decide) _ ht
  refine ⟨n, ?_⟩
  change ι ((6 : ℚ)⁻¹) * x - ι (((6 * n.val : ℕ) : ℚ) / (6 : ℚ) ^ 2) ∈ W
  rwa [show ((6 * n.val : ℕ) : ℚ) / (6 : ℚ) ^ 2 = (n.val : ℚ) / 6 by push_cast; ring]

private theorem valued_natCast (p : Nat.Primes) (n : ℕ) :
    Valued.v (n : (vₚ p).adicCompletion ℚ) =
      (vₚ p).valuation ℚ (algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ)) := by
  let v := vₚ p
  have hc := HeightOneSpectrum.adicCompletion.valued_coe ℚ v (n : ℚ)
  change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)) = _ at hc
  simpa only [map_natCast] using hc

private theorem valued_natCast_eq_one (p : Nat.Primes) (n : ℕ) :
    Valued.v (n : (vₚ p).adicCompletion ℚ) = 1 ↔ ¬ (p : ℕ) ∣ n := by
  let v := vₚ p
  have hgen : Rat.HeightOneSpectrum.natGenerator v = (p : ℕ) :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hmem : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ (p : ℕ) ∣ n := by
    rw [← Ideal.apply_mem_of_equiv_iff (f := e), map_natCast,
      ← Rat.HeightOneSpectrum.natGenerator_dvd_iff, hgen]
  rw [valued_natCast, HeightOneSpectrum.valuation_eq_one_iff_notMem, hmem]

private theorem sixCell_integral_units {x : A} {n : Fin 6} (hx : x ∈ C (sixIndex n)) :
    x ∈ W ∧ ∀ p : Nat.Primes, (p : ℕ) ∣ 6 →
      (x ∈ rationalAdelePrimeUnits p ↔ ¬ (p : ℕ) ∣ n.val) := by
  obtain ⟨z, hz, he⟩ := (mem_rationalAdeleStageCell_iff (by decide) _ _).mp hx
  rw [rep_sixIndex] at he
  constructor
  · change x.2 ∈ Wf
    rw [he]
    exact rationalFiniteIntegralAdeles.add_mem (fun v ↦ natCast_mem (v.adicCompletionIntegers ℚ) _)
      (by simpa only [nsmul_eq_mul] using rationalFiniteIntegralAdeles.nsmul_mem hz 6)
  · intro p hp
    let v := vₚ p
    let ev : F →+* v.adicCompletion ℚ := RestrictedProduct.evalRingHom _ v
    have hle : Valued.v (6 : v.adicCompletion ℚ) ≤ 1 := by
      rw [← Nat.cast_ofNat, valued_natCast]
      exact HeightOneSpectrum.valuation_le_one v _
    have hlt : Valued.v (6 : v.adicCompletion ℚ) < 1 :=
      lt_of_le_of_ne hle (fun h ↦ (valued_natCast_eq_one p 6).mp h hp)
    have hzsmall : Valued.v ((6 : v.adicCompletion ℚ) * ev z) < 1 := by
      rw [map_mul]
      exact (mul_le_mul_right (show Valued.v (ev z) ≤ 1 from hz v) _).trans_lt
        (by rwa [mul_one])
    change Valued.v (ev x.2) = 1 ↔ _
    simp only [he, map_add, map_mul, map_natCast]
    let a : v.adicCompletion ℚ := n.val
    let w : v.adicCompletion ℚ := 6 * ev z
    change Valued.v (a + w) = 1 ↔ _
    refine Iff.trans ?_ (valued_natCast_eq_one p n.val)
    change Valued.v (a + w) = 1 ↔ Valued.v a = 1
    constructor
    · intro h
      have hlt' : Valued.v w < Valued.v (a + w) := by rw [h]; exact hzsmall
      have he' := Valuation.map_sub_eq_of_lt_left Valued.v hlt'
      rwa [add_sub_cancel_right, h] at he'
    · intro h
      have hlt' : Valued.v w < Valued.v a := by rw [h]; exact hzsmall
      rw [Valuation.map_add_eq_of_lt_left Valued.v hlt', h]

/-- The repaired joint unit cut retains the two integral cells with residues
`1` and `5` modulo `6`, or indices `6` and `30` in the `j/6` coordinate. -/
public theorem rationalAdeleStageCell_six_eq_jointPrimeUnits :
    (W : Set A) ∩ U = C 6 ∪ C 30 := by
  have hunits {x : A} {n : Fin 6} (hx : x ∈ C (sixIndex n)) :
      x ∈ U ↔ ¬ 2 ∣ n.val ∧ ¬ 3 ∣ n.val :=
    ((sixCell_integral_units hx).2 p₂ (by decide)).and
      ((sixCell_integral_units hx).2 p₃ (by decide))
  have hres : ∀ n : Fin 6, (¬ 2 ∣ n.val ∧ ¬ 3 ∣ n.val) ↔
      sixIndex n = 6 ∨ sixIndex n = 30 := by decide
  ext x
  constructor
  · rintro ⟨hw, hu⟩
    obtain ⟨n, hn⟩ := exists_sixIndex_of_integral x hw
    rcases (hres n).mp ((hunits hn).mp hu) with he | he
    · exact Or.inl (he ▸ hn)
    · exact Or.inr (he ▸ hn)
  · intro h
    have finish {n : Fin 6} (hn : x ∈ C (sixIndex n)) (hr : ¬ 2 ∣ n.val ∧ ¬ 3 ∣ n.val) :
        x ∈ (W : Set A) ∩ U := ⟨(sixCell_integral_units hn).1, (hunits hn).mpr hr⟩
    rcases h with hx | hx
    · exact finish (n := 1) hx (by decide)
    · exact finish (n := 5) hx (by decide)

set_option linter.concreteInstances false

/-- The additive Fourier zero mode of the joint unit mask is one third of the
real integral, with no LF witness or prior vanishing assumption on the profile. -/
public theorem rationalAdeleJointUnit_fourier_zero [MeasurableSpace A] [BorelSpace A]
    (b : 𝓢(ℝ, ℂ)) : rationalAdeleFourier (Set.indicator U (rationalAdeleUnramified b)) 0 =
      (1 / 3 : ℂ) * ∫ t : ℝ, b t := by
  classical
  let h : 0 < (6 : ℕ) := by decide
  let s : Finset (Fin (6 ^ 2)) := {6, 30}
  let p : Fin (6 ^ 2) → 𝓢(ℝ, ℂ) := fun j ↦ if j ∈ s then b else 0
  have hasm : ((rationalAdeleStageCoordinates h).symm p).val =
      Set.indicator U (rationalAdeleUnramified b) := by
    funext x
    rw [rationalAdeleStageCoordinates_symm_eq_boxSum]
    simp only [rationalAdeleBoxSum, one_mul, rationalAdeleBox_stageCell]
    rw [← Finset.sum_subset (Finset.subset_univ s) (fun j _ hj ↦ by simp [p, hj])]
    have hcut : Set.indicator U (rationalAdeleUnramified b) x =
        Set.indicator (C 6 ∪ C 30) (fun a ↦ b (rationalAdeleReal a)) x := by
      rw [← rationalAdeleStageCell_six_eq_jointPrimeUnits]
      by_cases hx : x ∈ U <;> simp [rationalAdeleUnramified, Set.indicator_apply, hx]
    have hdisjoint (h6 : x ∈ C 6) (h30 : x ∈ C 30) : False := by
      obtain ⟨_, _, hk⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell h x).mp
        (rationalAdeleStageCell_subset_support h _ h6)
      exact (by decide : (6 : Fin (6 ^ 2)) ≠ 30) ((hk _ h6).trans (hk _ h30).symm)
    rw [hcut]
    by_cases h6 : x ∈ C 6 <;> by_cases h30 : x ∈ C 30
    · exact (hdisjoint h6 h30).elim
    all_goals simp [s, p, Set.indicator_apply, h6, h30]
  have hrep : rationalAdeleStageRepresentative 6 0 = 0 := by
    simp [rationalAdeleStageRepresentative]
  have hz : (0 : A) ∈ C 0 := (mem_rationalAdeleStageCell_iff h _ _).mpr
    ⟨0, rationalFiniteIntegralAdeles.zero_mem, by simp [hrep]⟩
  have hr : rationalAdeleReal (0 : A) = 0 := by
    simpa only [map_zero, Rat.cast_zero] using rationalAdeleReal_algebraMap 0
  have hw (c : 𝓢(ℝ, ℂ)) : (𝓕 c) 0 = ∫ t : ℝ, c t := by
    rw [congrFun (SchwartzMap.fourier_coe c) 0, Real.fourier_eq]
    simp
  rw [← hasm, ← rationalAdeleStageCoordinates_symm_fourier h,
    ← rationalAdeleStageCoordinates_eq_on_cell h _ hz, LinearEquiv.apply_symm_apply, hr,
    rationalAdeleStageFourier_apply]
  simp only [hrep, mul_zero, AddChar.map_zero_eq_one, map_one, mul_one, sum_apply, smul_apply,
    smul_eq_mul, hw, ← Finset.mul_sum, Nat.cast_ofNat]
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun j _ hj ↦ by simp [p, hj])]
  simp [s, p]
  ring

end Masullo
