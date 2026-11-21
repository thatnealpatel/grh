module

public import Theorems.RationalAdeleIntegralStageHaar

import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Local calibration for the rational additive modulus -/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set
open scoped Padic

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation:max "F" v:max => adicCompletion ℚ v
local notation:max "O" v:max => adicCompletionIntegers ℚ v
local notation "p[" v "]" => (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)

local instance (v : V) : Fact (p[v] : ℕ).Prime := ⟨(p[v]).property⟩

private theorem prime_absNorm (v : V) : v.asIdeal.absNorm = (p[v] : ℕ) := by
  let p : ℕ := p[v]
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hspan : Ideal.span {(p : ℤ)} = v.asIdeal.map e :=
    Rat.HeightOneSpectrum.span_natGenerator v
  let E := (Ideal.quotientEquiv v.asIdeal (Ideal.span {(p : ℤ)}) e hspan).trans
    (Int.quotientSpanNatEquivZMod p)
  rw [Ideal.absNorm_eq_natCard, Nat.card_congr E.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

private theorem norm_local_prime (v : V) : ‖((p[v] : ℕ) : F v)‖ = ((p[v] : ℕ) : ℝ)⁻¹ := by
  let p : ℕ := p[v]
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hspan : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
    apply (v.asIdeal.comap_map_of_bijective e e.bijective).symm.trans
    rw [← show Ideal.span {(p : ℤ)} = v.asIdeal.map e from
      Rat.HeightOneSpectrum.span_natGenerator v, ← Ideal.map_symm, Ideal.map_span,
      Set.image_singleton, map_natCast]
  have hval := v.intValuation_singleton (Nat.cast_ne_zero.mpr (p[v]).property.ne_zero) hspan
  change ‖(p : F v)‖ = (p : ℝ)⁻¹
  rw [← map_natCast (FinitePlace.embedding (K := ℚ) v) p,
    ← map_natCast (algebraMap (𝓞 ℚ) ℚ) p,
    FinitePlace.norm_embedding_int, hval,
    WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      WithZero.exp_ne_zero, WithZero.log_exp, NNReal.coe_zpow, NNReal.coe_natCast,
    prime_absNorm, zpow_neg_one]

private theorem norm_eq_one_iff_norm_padicEquiv_eq_one (v : V) (a : F v) (ha : a ≠ 0) :
    ‖a‖ = 1 ↔ ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v a‖ = 1 := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hb := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
  have hint (b : F v) : ‖b‖ ≤ 1 ↔ ‖e b‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff, ← mem_adicCompletionIntegers]
    change b ∈ O v ↔ e b ∈ PadicInt.subring (p[v] : ℕ)
    refine ⟨fun h ↦ hb.mapsTo h, fun h ↦ ?_⟩
    obtain ⟨c, hc, hcb⟩ := hb.surjOn h
    exact e.injective hcb ▸ hc
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hepos : 0 < ‖e a‖ := norm_pos_iff.mpr ((map_ne_zero_iff e e.injective).mpr ha)
  have h := hint a⁻¹
  rw [map_inv₀, norm_inv, norm_inv, inv_le_one₀ hpos, inv_le_one₀ hepos] at h
  exact le_antisymm_iff.trans ((and_congr (hint a) h).trans le_antisymm_iff.symm)

/-- The continuous field equivalence with `ℚ_[p]` preserves the normalized norm. -/
public theorem norm_rationalLocal_padicEquiv (v : V) (a : F v) :
    ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v a‖ = ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let p : ℕ := p[v]
  let b : F v := (p : F v) ^ (e a).valuation
  have hb : b ≠ 0 := by
    apply (map_ne_zero_iff e e.injective).mp
    rw [show b = (p : F v) ^ (e a).valuation from rfl, map_zpow₀, map_natCast]
    exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (p[v]).property.ne_zero)
  have hnorm : ‖e b‖ = ‖b‖ := by
    simp only [b, map_zpow₀, map_natCast, norm_zpow, Padic.norm_p]
    rw [show ‖(p : F v)‖ = (p : ℝ)⁻¹ from norm_local_prime v]
  have hea := (map_ne_zero_iff e e.injective).mpr ha
  have hpadic : ‖e b‖ = ‖e a‖ := by
    change ‖e ((p : F v) ^ (e a).valuation)‖ = ‖e a‖
    rw [map_zpow₀, map_natCast, Padic.norm_p_zpow,
      Padic.norm_eq_zpow_neg_valuation hea]
  have hr : ‖e (a / b)‖ = 1 := by
    rw [map_div₀, norm_div, hpadic, div_self (norm_ne_zero_iff.mpr hea)]
  have hr' := (norm_eq_one_iff_norm_padicEquiv_eq_one v (a / b) (div_ne_zero ha hb)).mpr hr
  rw [norm_div, div_eq_iff (norm_ne_zero_iff.mpr hb), one_mul] at hr'
  exact hpadic.symm.trans (hnorm.trans hr'.symm)

/-- The transported additive Haar measure gives `a O_v` mass `‖a‖` in the
norm used by the adelic product formula. This is the finite local
calibration for the rational case of (A.3.1.4), p. 556. -/
public theorem rationalLocalFieldAddHaar_dilate_integers (v : V) (a : F v) (ha : a ≠ 0) :
    rationalLocalFieldAddHaar v ((fun x : F v ↦ a * x) '' (O v : Set (F v))) =
      ENNReal.ofReal ‖a‖ := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hball : e '' (O v : Set (F v)) = PadicInt.subring (p[v] : ℕ) :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).image_eq
  calc
    _ = padicAddHaar p[v] (e '' ((fun x : F v ↦ a * x) '' (O v : Set (F v)))) :=
      e.toHomeomorph.measurableEmbedding.comap_apply _ _
    _ = _ := by
      rw [← image_comp]
      change padicAddHaar p[v] ((fun x : F v ↦ e (a * x)) '' (O v : Set (F v))) = _
      simp_rw [map_mul]
      rw [show (fun x : F v ↦ e a * e x) = (fun x ↦ e a * x) ∘ e from rfl,
        image_comp, hball]
      exact (padicAddHaar_dilate_integralBall p[v] (e a)
        ((map_ne_zero_iff e e.injective).mpr ha)).trans
          (congrArg ENNReal.ofReal (norm_rationalLocal_padicEquiv v a))

end Masullo
