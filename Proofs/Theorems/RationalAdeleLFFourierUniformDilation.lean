module

public import Lemmas.RationalAdeleLFStageOperators
public import Theorems.RationalAdeleLFFourierDilation
public import Props.RationalAdeleSchwartzBounded
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Lemmas.SchwartzUniformDilation

/-! # Fourier dilation differentiation on bounded rational Schwartz families

This proves the convergence requested in Remark 2.2.4.6, p. 92, for
our rational LF topology and canonical positive real section. The quotient
uses inverse frequency dilation with its inverse norm weight. No moment
vanishing or Fourier inversion is needed.
-/

open Bornology Filter NumberField Set
open scoped SchwartzMap Topology

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "L" => rationalAdeleFactorialLevel
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)
local notation "F" => rationalAdeleLFFourier
local notation "V" => rationalAdeleLFWeightedInverseDilation
local notation "D" => rationalAdeleLFDilationDeriv
local notation "U" => schwartzWeightedInverseDilation
local notation "G" => schwartzInverseDilationGenerator

/-- Uniform convergence in this space uses the additive uniformity of the LF topology. -/
public noncomputable instance : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E

public instance : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- The Fourier-side generator includes the derivative of the reciprocal norm. -/
public theorem rationalAdeleLFFourier_dilationDeriv (f : E) :
    F (D f) = - F f - D (F f) := by
  apply RationalAdeleSchwartzLF.ext
  funext y
  have hneg := (hasDerivAt_rationalAdeleLF_logDilation (F f) y).scomp_of_eq 0
    (hasDerivAt_neg' (0 : ℝ)) (neg_zero : -(0 : ℝ) = 0).symm
  have hweight : HasDerivAt (fun s : ℝ ↦ Real.exp (-s)) (-1) 0 := by
    simpa using (hasDerivAt_neg' (0 : ℝ)).exp
  have h := hweight.fun_smul hneg
  simp only [Function.comp_def, neg_zero, Real.exp_zero, one_smul, neg_one_smul] at h
  have hcov := hasDerivAt_rationalAdeleFourier_LFDilation f y
  rw [← rationalAdeleLFFourier_eq f, ← rationalAdeleLFFourier_eq (D f)] at hcov
  have hzero : (rationalIdeleLogSection (Multiplicative.ofAdd (0 : ℝ)) : A) * y = y := by
    change (rationalIdeleLogSection 1 : A) * y = y
    simp
  rw [hzero] at h
  simpa only [map_add, map_neg, Submodule.coe_add, Submodule.coe_neg, Pi.add_apply, Pi.neg_apply,
    sub_eq_add_neg, add_comm] using hcov.unique h

omit [MeasurableSpace A] [BorelSpace A] in
private theorem stageGenerator (n : ℕ) (b : Profiles n) :
    (fun j ↦ G (b j)) = -b - rationalAdeleStageEuler n b := by
  funext j
  ext x
  simp only [schwartzInverseDilationGenerator_apply, Pi.sub_apply, Pi.neg_apply,
    sub_apply, neg_apply, rationalAdeleStageEuler_apply, Complex.real_smul]

private theorem uniformFourierDilation {ι : Type*} {l : Filter ι} {s r : ι → ℝ}
    (hs : Tendsto s l (𝓝[≠] 0)) (hr : Tendsto (fun t ↦ r t * s t) l (𝓝 1))
    {B : Set E} (hB : IsVonNBounded ℂ B) :
    TendstoUniformlyOn (fun t f ↦ r t • (V (s t) (F f) - F f)) (fun f ↦ F (D f)) l B := by
  obtain ⟨n, C, hC, rfl⟩ := rationalAdeleLF_bounded_iff.mp hB
  let T := rationalAdeleStageFourier (L n)
  let Q (t : ι) (b : Profiles n) (j : Fin ((L n) ^ 2)) :=
    r t • (U (s t) (T b j) - T b j)
  let R (b : Profiles n) (j : Fin ((L n) ^ 2)) := G (T b j)
  have hprofiles : TendstoUniformlyOn Q R l C := by
    rw [tendstoUniformlyOn_iff_sub, tendsto_pi_nhds]
    intro j
    let Tj := (ContinuousLinearMap.proj j).comp T
    have hj := tendstoUniformlyOn_schwartzWeightedInverseDilation hs hr (hC.image Tj)
    have hj' := (hj.comp Tj).mono (subset_preimage_image Tj C)
    exact tendstoUniformlyOn_iff_sub.mp hj'
  let As := rationalAdeleLFAssembly n
  have h := As.uniformContinuous.comp_tendstoUniformlyOn hprofiles
  have hQ (t : ι) (b : Profiles n) :
      As (Q t b) = r t • (V (s t) (F (As b)) - F (As b)) := by
    change As (r t • ((fun j ↦ U (s t) (T b j)) - T b)) = _
    rw [rationalAdeleLFFourier_assembly, rationalAdeleLFWeightedInverseDilation_assembly,
      As.map_smul_of_tower, map_sub]
  have hR (b : Profiles n) : As (R b) = F (D (As b)) := by
    change As (fun j ↦ G (T b j)) = _
    rw [stageGenerator, map_sub, map_neg, rationalAdeleLFFourier_dilationDeriv,
      rationalAdeleLFFourier_assembly, rationalAdeleLFDilationDeriv_assembly]
  intro W hW
  filter_upwards [h W hW] with t ht
  rintro f ⟨b, hb, rfl⟩
  have hmem := ht b hb
  simpa only [Function.comp_apply, hQ, hR] using hmem

/-- The weighted inverse Fourier dilation quotient tends to the Fourier transform
of the dilation generator, uniformly on each bounded family, in log scale. -/
public theorem tendstoUniformlyOn_rationalAdeleLFFourier_logDilation {B : Set E}
    (hB : IsVonNBounded ℂ B) :
    TendstoUniformlyOn (fun (s : ℝ) f ↦ s⁻¹ • (V s (F f) - F f))
      (fun f ↦ F (D f)) (𝓝[≠] 0) B := by
  refine uniformFourierDilation (s := id) (r := Inv.inv) tendsto_id ?_ hB
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := ({0} : Set ℝ)ᶜ)] with s hs
  exact (inv_mul_cancel₀ (show s ≠ 0 from hs)).symm

/-- The same bounded-set limit with the manuscript's scale denominator `t - 1`.
Near one, `t` is positive, `V (log t)` dilates the real frequency by `t⁻¹`,
and its weight is also `t⁻¹`. -/
public theorem tendstoUniformlyOn_rationalAdeleLFFourier_dilation {B : Set E}
    (hB : IsVonNBounded ℂ B) :
    TendstoUniformlyOn (fun (t : ℝ) f ↦ (t - 1)⁻¹ • (V (Real.log t) (F f) - F f))
      (fun f ↦ F (D f)) (𝓝[≠] 1) B :=
  uniformFourierDilation tendsto_log_nhdsNE_one tendsto_log_div_sub_one hB

end Masullo
