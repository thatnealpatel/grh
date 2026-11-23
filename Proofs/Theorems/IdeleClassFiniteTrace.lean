module

public import Props.IdeleClassStripTrace

import Lemmas.FinitePlaceSupport
import Lemmas.IdeleStageSinglePlace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Finite local terms of the open-strip trace

For the tests in Masullo's Theorem 12.5.1.1 (p. 519), the finite-place
terms (12.5.1.2) are absolutely integrable and only finitely many are
nonzero. The local argument accounts for the ordinary integral in
(B.4.4.5), p. 620, without evaluating an orbital or global trace.
-/

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v

private theorem continuous_finiteIdeleInsertion (v : V) :
    Continuous (IdeleGroup.ofAdicCompletion (𝓞 K) K v) := by
  let w : {w : V // w ∈ ({v} : Finset V)} := ⟨v, Finset.mem_singleton_self v⟩
  have h : Continuous (fun u : (F v)ˣ ↦
      (1, Pi.mulSingle w u, 1) : (F v)ˣ → IdeleFiniteStage K {v}) :=
    continuous_const.prodMk
      ((continuous_mulSingle (A := fun w : {w : V // w ∈ ({v} : Finset V)} ↦
        (F w.val)ˣ) w).prodMk continuous_const)
  refine ((isOpenEmbedding_ideleFiniteStageEmbedding K {v}).continuous.comp h).congr ?_
  intro u
  exact ideleFiniteStageEmbedding_single_active K {v} w u

private theorem locallyConstant_finiteRestriction {φ : C → ℂ} (hφ : IsIdeleClassTest φ)
    (v : V) : IsLocallyConstant (fun u ↦ φ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u
  let i := IdeleGroup.ofAdicCompletion (𝓞 K) K v
  let j := IdeleClassGroup.ofAdicCompletion (𝓞 K) K v
  obtain ⟨f, _, hf⟩ := hφ.2 (j u)
  -- Translate back to the identity before lifting the local increment.
  have hlift : Tendsto (fun y : (F v)ˣ ↦ i (u⁻¹ * y)) (𝓝 u) (𝓝 1) := by
    have h : Continuous (fun y : (F v)ˣ ↦ i (u⁻¹ * y)) :=
      (continuous_finiteIdeleInsertion v).comp (continuous_const.mul continuous_id)
    simpa only [inv_mul_cancel, map_one] using h.continuousAt.tendsto (x := u)
  have heq : ∀ᶠ y in 𝓝 u, φ (j y) = f 1 := by
    filter_upwards [hlift.eventually hf] with y hy
    have hmul : j u * QuotientGroup.mk (i (u⁻¹ * y)) = j y := by
      change j u * j (u⁻¹ * y) = j y
      rw [← map_mul, mul_inv_cancel_left]
    have harch : (i (u⁻¹ * y)).val.1 = 1 := rfl
    rw [hmul, harch, map_one] at hy
    exact hy
  exact heq.mono fun y hy ↦ hy.trans heq.self_of_nhds.symm

private theorem isCompact_finiteUnitAnnulus (v : V) {T : ℝ} (hT : 0 < T) :
    IsCompact {u : (F v)ˣ | ‖(u : F v)‖ ∈ Icc T⁻¹ T} := by
  let : ProperSpace (F v) :=
    (Valued.integer.properSpace_iff_compactSpace_integer (K := F v) (Γ₀ := ℤᵐ⁰)).2
      (compactSpace_finiteCompletionIntegers K v)
  -- In the units topology, bound both the value and its inverse.
  let B := Metric.closedBall (0 : F v) T
  let A := Units.embedProduct (F v) ⁻¹' (B ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' B))
  have hB : IsCompact B := isCompact_closedBall _ _
  have hA : IsCompact A := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hB.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hB))
  refine hA.of_isClosed_subset (isClosed_Icc.preimage Units.continuous_val.norm) ?_
  intro u hu
  change T⁻¹ ≤ ‖(u : F v)‖ ∧ ‖(u : F v)‖ ≤ T at hu
  change (u : F v) ∈ B ∧ (↑(u⁻¹) : F v) ∈ B
  have hn : 0 < ‖(u : F v)‖ := norm_pos_iff.mpr u.ne_zero
  simp only [B, Metric.mem_closedBall, dist_zero_right, Units.val_inv_eq_inv_val, norm_inv]
  exact ⟨hu.2, (inv_le_comm₀ hn hT).mpr hu.1⟩

/-- The kernel of (12.5.1.2) is integrable at every finite place for the
open-strip test, with respect to the local multiplicative Tamagawa Haar measure. -/
public theorem finiteTraceTermIntegrable_of_isIdeleClassTest (φ : C → ℂ)
    (hφ : IsIdeleClassTest φ) (hunit : ∀ x : ideleClassNormOne (K := K), φ x = 0) :
    ∀ v : V, FiniteTraceTermIntegrable v φ := by
  intro v
  let j := IdeleClassGroup.ofAdicCompletion (𝓞 K) K v
  have hloc := locallyConstant_finiteRestriction hφ v
  have hOne : φ (j 1) = 0 := by
    rw [map_one]
    exact hunit ⟨1, (ideleClassNormOne (K := K)).one_mem⟩
  have hcont : Continuous (finiteTraceKernel v φ) := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u = 1
    · subst u
      apply (continuousAt_const (y := (0 : ℂ))).congr
      filter_upwards [hloc.eventually_eq 1] with y hy
      change φ (j y) = φ (j 1) at hy
      change 0 = φ (j y) * _ / _
      rw [hy, hOne, zero_mul, zero_div]
    · have hne : (‖1 - (u : F v)‖ : ℂ) ≠ 0 := by
        intro h
        have h' : (1 : F v) = (u : F v) :=
          sub_eq_zero.mp (norm_eq_zero.mp (Complex.ofReal_eq_zero.mp h))
        exact hu (Units.ext h'.symm)
      have hsqrt : Continuous (fun y : (F v)ˣ ↦ (Real.sqrt ‖(y : F v)‖ : ℂ)) :=
        Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Units.continuous_val.norm)
      have hdisp : Continuous (fun y : (F v)ˣ ↦ (‖1 - (y : F v)‖ : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_const.sub Units.continuous_val).norm
      exact (hloc.continuous.continuousAt.mul hsqrt.continuousAt).div hdisp.continuousAt hne
  obtain ⟨T, hT, hband⟩ := exists_ideleClassNorm_band_of_hasCompactSupport φ hφ.1
  have hA := isCompact_finiteUnitAnnulus v (zero_lt_one.trans hT)
  have hsupp : HasCompactSupport (finiteTraceKernel v φ) := by
    refine HasCompactSupport.of_support_subset_isCompact hA ?_
    intro u hu
    have hval : φ (j u) ≠ 0 := by
      intro hz
      apply hu
      change φ (j u) * _ / _ = 0
      rw [hz, zero_mul, zero_div]
    have hnorm := hband (j u) (subset_tsupport φ hval)
    rw [ideleClassNorm_ofAdicCompletion v u] at hnorm
    exact Ioo_subset_Icc_self hnorm
  let : MeasurableSpace (F v)ˣ := borel _
  let : BorelSpace (F v)ˣ := ⟨rfl⟩
  change Integrable (finiteTraceKernel v φ) (finiteCompletionMultiplicativeHaar v)
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- Only finitely many finite places contribute to (12.5.1.2). -/
public theorem hasFiniteSupport_finiteTraceTerm_of_isIdeleClassTest (φ : C → ℂ)
    (hφ : IsIdeleClassTest φ) (hunit : ∀ x : ideleClassNormOne (K := K), φ x = 0) :
    Function.HasFiniteSupport (fun v ↦ finiteTraceTerm v φ) := by
  obtain ⟨S, hS, hvan⟩ := exists_finitePlaceRestriction_eq_zero_of_hasCompactSupport φ hφ.1
    (fun g h ↦ hunit ⟨g, (mem_ideleClassNormOne g).2 h⟩)
  apply hS.subset
  intro v hv
  by_contra ho
  have hz : finiteTraceKernel v φ = 0 := by
    funext u
    simp only [finiteTraceKernel, hvan v ho u, zero_mul, zero_div, Pi.zero_apply]
  have ht : finiteTraceTerm v φ = 0 := by simp [finiteTraceTerm, hz]
  exact hv ht

end Masullo
