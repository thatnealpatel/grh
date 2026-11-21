module

public import Theorems.RationalThetaInversion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Finite support of the unramified rational theta sum

This identifies the summands in Masullo's (2.2.3.1), pp. 81–82, for the
unramified tensor and the positive real idele section with finite coordinates
one. We use the characteristic function of the product of the finite integer
rings, evaluated directly on the diagonal rational indices. This does not
construct the Schwartz–Bruhat space, the norm-fiber quotient, or its measure.
-/

open NumberField IsDedekindDomain
open scoped Classical SchwartzMap

namespace Masullo

private theorem rational_integral_at_finite_places_iff (q : ℚ) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ) ↔
    ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q
      (fun v ↦ by
        have hv := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (h v)
        rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
          Algebra.algebraMap_self_apply] at hv
        rwa [HeightOneSpectrum.adicCompletion.valued_coe ℚ v q] at hv)
    exact ⟨Rat.ringOfIntegersEquiv x, (Rat.ringOfIntegersEquiv_apply_coe x).trans hx⟩
  · rintro ⟨n, rfl⟩ v
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, ← Rat.ringOfIntegersEquiv_symm_apply_coe n]
    exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 ℚ) ℚ v (Rat.ringOfIntegersEquiv.symm n)

/-- The rational indices in the unramified sum (2.2.3.1) at the positive real
section are selected by finite integrality. The surviving nonzero indices
are the nonzero integers. -/
public theorem rationalTheta_eq_unramified_sum (b : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    let f : {q : ℚ // q ≠ 0} → ℂ := fun q ↦
      if ∀ v : HeightOneSpectrum (𝓞 ℚ),
        algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ) ∈ v.adicCompletionIntegers ℚ
      then b (t * ((q : ℚ) : ℝ)) else 0
    Summable (fun q ↦ ‖f q‖) ∧ (∑' q, f q) = rationalTheta b t := by
  let e (n : {n : ℤ // n ≠ 0}) : {q : ℚ // q ≠ 0} :=
    ⟨(n : ℤ), Int.cast_ne_zero.mpr n.property⟩
  intro f
  have he : Function.Injective e := by
    intro i j h
    exact Subtype.ext (Int.cast_injective (congrArg Subtype.val h : ((i : ℤ) : ℚ) = (j : ℤ)))
  have hsample (n : {n : ℤ // n ≠ 0}) : f (e n) = b (t * (n : ℤ)) := by
    have hi := (rational_integral_at_finite_places_iff (n : ℤ)).2 ⟨n, rfl⟩
    change (if _ then b (t * (((n : ℤ) : ℚ) : ℝ)) else 0) = _
    rw [ite_eq_left hi, Rat.cast_intCast]
  have hzero (q : {q : ℚ // q ≠ 0}) (hq : q ∉ Set.range e) : f q = 0 := by
    refine ite_eq_right fun h ↦ hq ?_
    obtain ⟨n, hn⟩ := (rational_integral_at_finite_places_iff q).1 h
    have hn0 : n ≠ 0 := by
      intro hz
      apply q.property
      simpa [hz] using hn.symm
    exact ⟨⟨n, hn0⟩, Subtype.ext hn⟩
  constructor
  · apply (he.summable_iff (f := fun q ↦ ‖f q‖) (fun q hq ↦ by rw [hzero q hq, norm_zero])).1
    simpa only [Function.comp_def, hsample] using
      (summable_norm_schwartz_int_mul b ht.ne').subtype (fun n : ℤ ↦ n ≠ 0)
  · calc
      (∑' q, f q) = ∑' n, f (e n) := (he.tsum_eq fun q hq ↦ by
        by_contra h
        exact hq (hzero q h)).symm
      _ = rationalTheta b t := by simp only [hsample, rationalTheta]

end Masullo
