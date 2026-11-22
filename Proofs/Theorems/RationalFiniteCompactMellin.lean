module

public import Lemmas.FiniteHeckeRestriction
public import Lemmas.RationalLocalNormShell
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Ring

/-! # Compactly supported Mellin pairings on rational finite completion units

This is the finite-place input to the repaired forward direction of Lemma 5.3.4.2(2),
PDF pp. 259–261, with the bilinear pairing of (3.3.1.7), p. 130, and the rational
finite Haar normalization of A.3.2.2, p. 560.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation:max "K" v:max => adicCompletion ℚ v
local notation "G" v => (K v)ˣ
local notation "p[" v "]" => (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)
local notation "P[" v "]" => ((p[v] : ℕ) : ℝ)

private theorem continuous_rationalLocalLogNorm (v : V) :
    Continuous (fun u : G v ↦ Real.log ‖(u : K v)‖) := by
  refine continuous_iff_continuousAt.mpr fun u ↦ ?_
  have hn : ContinuousAt (fun x : G v ↦ ‖(x : K v)‖) u :=
    (continuous_norm.comp Units.continuous_val).continuousAt
  exact ContinuousAt.comp (f := fun x : G v ↦ ‖(x : K v)‖)
    (Real.continuousAt_log (norm_ne_zero_iff.mpr u.ne_zero)) hn

private theorem exists_rationalLocalNormShell_Icc (v : V) {C : Set (G v)}
    (hc : IsCompact C) :
    ∃ L U : ℤ, L ≤ U ∧ C ⊆ (⋃ k ∈ Finset.Icc L U, rationalLocalNormShell v k) := by
  let t (u : G v) := -Real.log ‖(u : K v)‖ / Real.log P[v]
  have ht : Continuous t := (continuous_rationalLocalLogNorm v).neg.div_const _
  obtain ⟨a, ha⟩ := hc.bddBelow_image ht.continuousOn
  obtain ⟨b, hb⟩ := hc.bddAbove_image ht.continuousOn
  obtain ⟨L, hL⟩ := exists_int_le a
  obtain ⟨U, hU⟩ := exists_int_ge b
  refine ⟨L, max L U, le_max_left _ _, fun u hu ↦ ?_⟩
  have hmem : u ∈ ⋃ k, rationalLocalNormShell v k := by
    rw [RationalLocalNormShell.iUnion_eq_univ]; exact mem_univ _
  obtain ⟨k, hk⟩ := mem_iUnion.mp hmem
  have hlog : Real.log P[v] ≠ 0 := (Real.log_pos (RationalLocalNormShell.one_lt_prime v)).ne'
  have htk : t u = (k : ℝ) := by
    dsimp only [t]
    rw [RationalLocalNormShell.log_norm hk, neg_mul, neg_neg, mul_div_cancel_right₀ _ hlog]
  have htu := mem_image_of_mem t hu
  have hl : (L : ℝ) ≤ k := htk ▸ hL.trans (ha htu)
  have hu' : (k : ℝ) ≤ U := htk ▸ (hb htu).trans hU
  have hkI : k ∈ Finset.Icc L (max L U) := Finset.mem_Icc.mpr
    ⟨by exact_mod_cast hl, le_trans (by exact_mod_cast hu') (le_max_right _ _)⟩
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkI, hk⟩⟩

/-- Compact support in the completion units bounds both ends of the shell index,
independently of `s`. The full character-weighted test remains in each coefficient.
Continuity suffices for the test, and the character need not be unitary. -/
public theorem rationalFiniteCompactMellinPair (v : V) [MeasurableSpace (G v)] [BorelSpace (G v)]
    (χ : HeckeCharacter (𝓞 ℚ) ℚ) (b : (G v) → ℂ) (hb : Continuous b) (hc : HasCompactSupport b) :
    let A := fun u : G v ↦ b u * χ.restrict v (u : K v)
    let F := fun (s : ℂ) (u : G v) ↦ A u * (‖(u : K v)‖ : ℂ) ^ s
    (∃ L U : ℤ, L ≤ U ∧ tsupport b ⊆ (⋃ k ∈ Finset.Icc L U, rationalLocalNormShell v k) ∧
      ∀ s : ℂ, Integrable (F s) (rationalLocalMultiplicativeHaar v) ∧
        (∫ u, F s u ∂rationalLocalMultiplicativeHaar v) =
          ∑ k ∈ Finset.Icc L U, Complex.exp (-(k : ℂ) * s * (Real.log P[v] : ℂ)) *
            ∫ u in rationalLocalNormShell v k, A u ∂rationalLocalMultiplicativeHaar v) ∧
    Differentiable ℂ (fun s ↦ ∫ u, F s u ∂rationalLocalMultiplicativeHaar v) := by
  intro A F
  let μ := rationalLocalMultiplicativeHaar v
  let S := rationalLocalNormShell v
  obtain ⟨L, U, hLU, hsupport⟩ := exists_rationalLocalNormShell_Icc v hc
  let I := Finset.Icc L U
  let E (s : ℂ) (k : ℤ) := Complex.exp (-(k : ℂ) * s * (Real.log P[v] : ℂ))
  have hcpow (s : ℂ) (u : G v) :
      (‖(u : K v)‖ : ℂ) ^ s = Complex.exp (s * (Real.log ‖(u : K v)‖ : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero)),
      ← Complex.ofReal_log (norm_nonneg _), mul_comm]
  have hlocal (s : ℂ) : Integrable (F s) μ := by
    have hpow : Continuous (fun u : G v ↦ (‖(u : K v)‖ : ℂ) ^ s) := by
      simp_rw [hcpow]
      exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_rationalLocalLogNorm v)))
    exact Continuous.integrable_of_hasCompactSupport
      ((hb.mul (continuous_finiteHeckeRestriction χ v)).mul hpow) hc.mul_right.mul_right
  have hsum (s : ℂ) : (∫ u, F s u ∂μ) = ∑ k ∈ I, E s k * ∫ u in S k, A u ∂μ := by
    have hcut : (∫ u in ⋃ k ∈ I, S k, F s u ∂μ) = ∫ u, F s u ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      have hbu : b u = 0 := by
        by_contra h
        exact hu (hsupport (subset_tsupport b h))
      simp [F, A, hbu]
    rw [← hcut, integral_biUnion_finset I (fun k _ ↦ RationalLocalNormShell.measurableSet v k)
      (fun j _ k _ hjk ↦ RationalLocalNormShell.pairwiseDisjoint v hjk) (fun _ _ ↦ (hlocal s).integrableOn)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (RationalLocalNormShell.measurableSet v k)
    intro u hu
    have he : (‖(u : K v)‖ : ℂ) ^ s = E s k := by
      dsimp only [E]
      rw [hcpow, RationalLocalNormShell.log_norm hu]
      push_cast
      congr 1
      ring
    simp [F, he, mul_comm]
  refine ⟨⟨L, U, hLU, hsupport, fun s ↦ ⟨hlocal s, hsum s⟩⟩, ?_⟩
  rw [show (fun s ↦ ∫ u, F s u ∂μ) = _ from funext hsum]
  exact Differentiable.fun_sum fun k _ ↦
    (((differentiable_id.const_mul (-(k : ℂ))).mul_const _).cexp).mul_const _

end Masullo
