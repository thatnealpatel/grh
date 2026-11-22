module

public import Theorems.PadicRamifiedThreeFourier
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Haar.Basic

import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Ramified local zeta integrals over `ℚ_[p]`

The inverse residue character test and its negative-sign Fourier transform
pair with the forward twist and its dual in (3.3.1.7), p. 130. Each pairing
is constant on one compact multiplicative shell and zero elsewhere. The
forward-over-reflected ratio retains the conductor power, independently of
the Haar unit mass and of the central Fourier phase.
-/

open scoped Padic ENNReal
open MeasureTheory Set Filter Topology

namespace Masullo

variable (p : ℕ) [Fact p.Prime] {n : ℕ}

local notation "K" => ℚ_[p]
local notation "O" => ℤ_[p]
local notation "G" => (ℚ_[p])ˣ
local notation "ρ" => PadicInt.toZModPow (p := p) n
local notation "d" => ((p : K) ^ n)
local notation "A[" χ "]" => padicConductorFourier p χ d⁻¹
local notation "v[" x "]" => Padic.valuation (x : K)

private theorem prime_ne_zero : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)

private theorem valuation_eq_of_norm {x y : G} (h : ‖(x : K)‖ = ‖(y : K)‖) :
    v[x] = v[y] := by
  rw [Padic.norm_eq_zpow_neg_valuation x.ne_zero, Padic.norm_eq_zpow_neg_valuation y.ne_zero] at h
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hp) hp.ne' h)

private theorem eventually_norm_eq (x : G) : ∀ᶠ y : G in 𝓝 x, ‖(y : K)‖ = ‖(x : K)‖ := by
  have hc : Continuous fun y : G ↦ ‖(y : K) - (x : K)‖ :=
    (Units.continuous_val.sub continuous_const).norm
  have ht : ‖(x : K) - (x : K)‖ < ‖(x : K)‖ := by simp [norm_pos_iff, x.ne_zero]
  filter_upwards [hc.continuousAt.eventually_lt continuousAt_const ht] with y hy
  exact Padic.norm_eq_of_norm_sub_lt_right hy

/-- The integral unit obtained by removing the uniformizer power. -/
private noncomputable def unitPart (x : G) : O :=
  ⟨(x : K) * (p : K) ^ (-v[x]), by
    change ‖(x : K) * (p : K) ^ (-v[x])‖ ≤ 1
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation x.ne_zero, Padic.norm_p_zpow, neg_neg,
      ← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne p)), neg_add_cancel, zpow_zero]⟩

private theorem unitPart_mul (x y : G) : unitPart p (x * y) = unitPart p x * unitPart p y := by
  apply PadicInt.coe_inj.mp
  change ((x : K) * (y : K)) * (p : K) ^ (-((x : K) * (y : K)).valuation) =
    ((x : K) * (p : K) ^ (-v[x])) * ((y : K) * (p : K) ^ (-v[y]))
  rw [Padic.valuation_mul x.ne_zero y.ne_zero, neg_add, zpow_add₀ (prime_ne_zero p)]
  ring

/-- The residue character extended to `ℚ_[p]ˣ` with uniformizer value one. -/
public noncomputable def padicZetaCharacter (χ : DirichletCharacter ℂ (p ^ n)) : G →* ℂ where
  toFun x := χ (ρ (unitPart p x))
  map_one' := by
    have h : unitPart p 1 = 1 := PadicInt.coe_inj.mp (by
      change (1 : K) * (p : K) ^ (-(1 : K).valuation) = 1
      rw [Padic.valuation_one, neg_zero, zpow_zero, mul_one])
    rw [h, map_one, map_one]
  map_mul' x y := by rw [unitPart_mul, map_mul, map_mul]

private theorem padicZetaCharacter_continuous (χ : DirichletCharacter ℂ (p ^ n)) :
    Continuous (padicZetaCharacter p χ) := by
  rw [continuous_iff_continuousAt]
  intro x
  let a := (p : K) ^ (-v[x])
  have hc : Continuous (fun y : G ↦ ‖((y : K) - (x : K)) * a‖) :=
    ((Units.continuous_val.sub continuous_const).mul continuous_const).norm
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := by
    exact zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _
  have ht : ‖((x : K) - (x : K)) * a‖ < (p : ℝ) ^ (-(n : ℤ)) := by simpa using hpos
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_norm_eq p x,
    hc.continuousAt.eventually_lt continuousAt_const ht] with y hy hd
  have hv := valuation_eq_of_norm p hy
  have hr : ρ (unitPart p y) = ρ (unitPart p x) := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
      ← PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.norm_coe, PadicInt.coe_sub]
    change ‖(y : K) * (p : K) ^ (-v[y]) - (x : K) * a‖ ≤ _
    rw [hv, ← sub_mul]
    exact hd.le
  change χ (ρ (unitPart p x)) = χ (ρ (unitPart p y))
  rw [hr]

/-- The character is continuous, is one on the uniformizer, and pulls back
by residue reduction on the integral units. -/
public theorem padicZetaCharacter_spec (χ : DirichletCharacter ℂ (p ^ n)) :
    Continuous (padicZetaCharacter p χ) ∧
    padicZetaCharacter p χ (Units.mk0 (p : K) (Nat.cast_ne_zero.mpr (NeZero.ne p))) = 1 ∧
    ∀ u : Oˣ, padicZetaCharacter p χ (Units.mk0 (u : K) (PadicInt.coe_ne_zero.mpr u.ne_zero)) =
      χ (ρ (u : O)) := by
  refine ⟨padicZetaCharacter_continuous p χ, ?_, ?_⟩
  · have h : unitPart p (Units.mk0 (p : K) (prime_ne_zero p)) = 1 := PadicInt.coe_inj.mp (by
      change (p : K) * (p : K) ^ (-(p : K).valuation) = 1
      rw [Padic.valuation_p, zpow_neg, zpow_one, mul_inv_cancel₀ (prime_ne_zero p)])
    change χ (ρ (unitPart p (Units.mk0 (p : K) (prime_ne_zero p)))) = 1
    rw [h, map_one, map_one]
  · intro u
    let x : G := Units.mk0 (u : K) (PadicInt.coe_ne_zero.mpr u.ne_zero)
    have hx : ‖(x : K)‖ = ‖((1 : G) : K)‖ := by
      change ‖((u : O) : K)‖ = ‖(1 : K)‖
      rw [PadicInt.norm_coe, PadicInt.isUnit_iff.mp u.isUnit, norm_one]
    have hv : v[x] = 0 := (valuation_eq_of_norm p hx).trans Padic.valuation_one
    have h : unitPart p x = (u : O) := PadicInt.coe_inj.mp (by
      change (u : K) * (p : K) ^ (-v[x]) = (u : K)
      rw [hv, neg_zero, zpow_zero, mul_one])
    change χ (ρ (unitPart p x)) = _
    rw [h]

/-- The forward integrand in the multiplicative pairing. -/
public noncomputable def padicConductorZetaForwardIntegrand
    (χ : DirichletCharacter ℂ (p ^ n)) (s : ℂ) (x : G) : ℂ :=
  padicConductorTest p χ (x : K) * (padicZetaCharacter p χ x * (‖(x : K)‖ : ℂ) ^ s)

/-- The reflected integrand, using the inverse character and exponent `1 - s`. -/
public noncomputable def padicConductorZetaReflectedIntegrand
    (χ : DirichletCharacter ℂ (p ^ n)) (s : ℂ) (x : G) : ℂ :=
  padicConductorFourier p χ (x : K) *
    ((padicZetaCharacter p χ x)⁻¹ * (‖(x : K)‖ : ℂ) ^ (1 - s))

private def normOneShell : Set G := {x | ‖(x : K)‖ = 1}

local notation "U" => normOneShell p

private theorem isOpen_norm_one : IsOpen U :=
  isOpen_iff_mem_nhds.mpr fun x hx ↦ (eventually_norm_eq p x).mono fun _ hy ↦ hy.trans hx

private theorem isCompact_norm_one : IsCompact U := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have he : Units.val '' U = Metric.sphere (0 : K) 1 := by
    ext z
    rw [mem_image, Metric.mem_sphere, dist_zero_right]
    exact ⟨fun ⟨x, hx, he⟩ ↦ he ▸ hx, fun hz ↦
      ⟨Units.mk0 z (by rintro rfl; simp at hz), hz, rfl⟩⟩
  rw [he]
  exact isCompact_sphere _ _

private noncomputable def integralUnit (x : G) (h : x ∈ U) : Oˣ :=
  (PadicInt.isUnit_iff.mpr (show ‖(⟨(x : K), h.le⟩ : O)‖ = 1 from h)).unit

private theorem coe_integralUnit (x : G) (h : x ∈ U) : (integralUnit p x h : K) = (x : K) :=
  congrArg (fun a : O ↦ (a : K)) (IsUnit.unit_spec _)

private theorem forward_eq_indicator (hn : 0 < n) (χ : DirichletCharacter ℂ (p ^ n)) (s : ℂ) :
    padicConductorZetaForwardIntegrand p χ s = (U).indicator (fun _ ↦ 1) := by
  funext x
  by_cases hx : x ∈ U
  · let u := integralUnit p x hx
    have hu : (u : K) = (x : K) := coe_integralUnit p x hx
    have he : Units.mk0 (u : K) (PadicInt.coe_ne_zero.mpr u.ne_zero) = x := Units.ext hu
    have hχ := (padicZetaCharacter_spec p χ).2.2 u
    rw [he] at hχ
    have hχ0 : χ (ρ (u : O)) ≠ 0 := MulChar.apply_ne_zero_iff.mpr (u.isUnit.map ρ)
    rw [padicConductorZetaForwardIntegrand, ← hu, padicConductorTest_unit, hu,
      show ‖(x : K)‖ = 1 from hx, Complex.ofReal_one, Complex.one_cpow, mul_one,
      hχ, MulChar.inv_apply_eq_inv', inv_mul_cancel₀ hχ0, indicator_of_mem hx]
  · rw [padicConductorZetaForwardIntegrand, padicConductorTest_eq_zero_of_norm_ne_one p hn χ hx,
      zero_mul, indicator_of_notMem hx]

private noncomputable def conductorPower (n : ℕ) : G :=
  (Units.mk0 (p : K) (prime_ne_zero p)) ^ n

private noncomputable def reflectedShell (n : ℕ) : Set G := (fun x : G ↦ conductorPower p n * x) ⁻¹' U

local notation "V" => reflectedShell p n
local notation "P" => ((p : ℂ) ^ n)

private theorem reflected_eq_indicator (hn : 0 < n) (χ : DirichletCharacter ℂ (p ^ n))
    (hχ : χ.IsPrimitive) (s : ℂ) :
    padicConductorZetaReflectedIntegrand p χ s = (V).indicator (fun _ ↦ A[χ] * P ^ (1 - s)) := by
  funext x
  by_cases hx : x ∈ V
  · let y := conductorPower p n * x
    let u := integralUnit p y hx
    have hu : (u : K) = d * (x : K) := coe_integralUnit p y hx
    have hy : (u : K) / d = (x : K) := (div_eq_iff (pow_ne_zero _ (prime_ne_zero p))).mpr
      (hu.trans (mul_comm _ _))
    have he : Units.mk0 (u : K) (PadicInt.coe_ne_zero.mpr u.ne_zero) = y :=
      Units.ext (coe_integralUnit p y hx)
    have hc := (padicZetaCharacter_spec p χ).2.2 u
    rw [he, show y = conductorPower p n * x from rfl, map_mul,
      show padicZetaCharacter p χ (conductorPower p n) = 1 by
        rw [conductorPower, map_pow, (padicZetaCharacter_spec p χ).2.1, one_pow], one_mul] at hc
    have hnorm : ‖(x : K)‖ = (p : ℝ) ^ n := by
      have h : ‖d * (x : K)‖ = 1 := hx
      rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_eq_div, div_eq_iff] at h
      · simpa using h
      · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
    have hχ0 : χ (ρ (u : O)) ≠ 0 := MulChar.apply_ne_zero_iff.mpr (u.isUnit.map ρ)
    rw [padicConductorZetaReflectedIntegrand, ← hy, padicConductorFourier_unit p χ hχ, hy,
      hc, hnorm, Complex.ofReal_pow, Complex.ofReal_natCast, indicator_of_mem hx]
    field_simp
  · have hz : padicConductorFourier p χ (x : K) = 0 :=
      not_ne_iff.mp (mt (padicConductorFourier_ne_zero_iff p hn χ hχ _).mp hx)
    rw [padicConductorZetaReflectedIntegrand, hz, zero_mul, indicator_of_notMem hx]

variable [MeasurableSpace (ℚ_[p])ˣ] [BorelSpace (ℚ_[p])ˣ]

/-- The forward-over-reflected quotient of the two actual integrals. -/
public noncomputable def padicConductorZetaRatio
    (χ : DirichletCharacter ℂ (p ^ n)) (μ : Measure G) (s : ℂ) : ℂ :=
  (∫ x, padicConductorZetaForwardIntegrand p χ s x ∂μ) /
    (∫ x, padicConductorZetaReflectedIntegrand p χ s x ∂μ)

/-- Absolute convergence and values of the two local zeta integrals, for
any complex parameter and any multiplicative Haar normalization. -/
public theorem padicConductorZeta_integrals (hn : 0 < n) (χ : DirichletCharacter ℂ (p ^ n))
    (hχ : χ.IsPrimitive) (μ : Measure G) [μ.IsHaarMeasure] (s : ℂ) :
    Integrable (padicConductorZetaForwardIntegrand p χ s) μ ∧
    Integrable (padicConductorZetaReflectedIntegrand p χ s) μ ∧
    (∫ x, padicConductorZetaForwardIntegrand p χ s x ∂μ) = (μ.real {x : G | ‖(x : K)‖ = 1} : ℂ) ∧
    (∫ x, padicConductorZetaReflectedIntegrand p χ s x ∂μ) =
      (μ.real {x : G | ‖(x : K)‖ = 1} : ℂ) * A[χ] * P ^ (1 - s) := by
  change Integrable _ μ ∧ Integrable _ μ ∧ _ = (μ.real U : ℂ) ∧
    _ = (μ.real U : ℂ) * A[χ] * P ^ (1 - s)
  have hU := (isOpen_norm_one p).measurableSet
  have hV : MeasurableSet V := hU.preimage (continuous_const_mul (conductorPower p n)).measurable
  have hmass : μ V = μ U := measure_preimage_mul μ _ _
  have hfin : μ U ≠ ∞ := (isCompact_norm_one p).measure_lt_top.ne
  rw [forward_eq_indicator p hn χ s, reflected_eq_indicator p hn χ hχ s,
    integrable_indicator_iff hU, integrable_indicator_iff hV,
    integral_indicator_const _ hU, integral_indicator_const _ hV]
  refine ⟨integrableOn_const hfin, integrableOn_const (hmass ▸ hfin), ?_, ?_⟩
  · simp [Complex.real_smul]
  · simp [Complex.real_smul, Measure.real, hmass, mul_assoc]

/-- In the quotient at two parameters the nonzero Haar mass and central
Fourier amplitude cancel, leaving the conductor power. -/
public theorem padicConductorZeta_ratio_div (hn : 0 < n) (χ : DirichletCharacter ℂ (p ^ n))
    (hχ : χ.IsPrimitive) (μ : Measure G) [μ.IsHaarMeasure] (s t : ℂ) :
    padicConductorZetaRatio p χ μ s / padicConductorZetaRatio p χ μ t = P ^ (s - t) := by
  have hm : (μ.real U : ℂ) ≠ 0 := by
    have hpos := (isOpen_norm_one p).measure_pos μ (show (U).Nonempty from ⟨1, norm_one⟩)
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hpos.ne'
      (isCompact_norm_one p).measure_lt_top.ne).ne'
  have hA : A[χ] ≠ 0 := (padicConductorFourier_ne_zero_iff p hn χ hχ _).mpr (by
    rw [mul_inv_cancel₀ (pow_ne_zero _ (prime_ne_zero p)), norm_one])
  have hP : P ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  have hs := (padicConductorZeta_integrals p hn χ hχ μ s).2.2
  have ht := (padicConductorZeta_integrals p hn χ hχ μ t).2.2
  have hst : s - t = (1 - t) - (1 - s) := by ring
  rw [padicConductorZetaRatio, padicConductorZetaRatio, hs.1, hs.2, ht.1, ht.2,
    hst, Complex.cpow_sub (1 - t) (1 - s) hP]
  have hs0 : P ^ (1 - s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hP)
  have ht0 : P ^ (1 - t) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hP)
  field_simp
  exact div_self (mul_ne_zero hm (by simpa only [one_div] using hA))

-- Keep the same arbitrary Borel measure interface at the concrete prime.
set_option linter.concreteInstances false in
/-- For the nontrivial character modulo three, the two-point quotient is
`√3`, not the ratio of a nonzero constant finite factor. -/
public theorem padicRamifiedThreeZeta_ratio_div
    [MeasurableSpace (ℚ_[3])ˣ] [BorelSpace (ℚ_[3])ˣ]
    (μ : Measure (ℚ_[3])ˣ) [μ.IsHaarMeasure] :
    padicConductorZetaRatio 3 padicRamifiedThreeCharacter μ (3 / 4) /
      padicConductorZetaRatio 3 padicRamifiedThreeCharacter μ (1 / 4) = (Real.sqrt 3 : ℂ) := by
  rw [padicConductorZeta_ratio_div 3 Nat.one_pos _ padicRamifiedThreeCharacter_isPrimitive,
    pow_one, show (3 / 4 - 1 / 4 : ℂ) = (1 / 2 : ℝ) by norm_num,
    Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

end Masullo
