module

public import Lemmas.RealSchwartzFlatMellin
public import Theorems.RealArchimedeanHeckeRestriction
public import Theorems.RealMultiplicativeHaarLogSign
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.Ring

/-! # The raw flat Schwartz pairing on real completion units

This is the real-place input to the repaired forward direction of Lemma 5.3.4.2(2),
PDF pp. 259–261. The test is paired bilinearly as in (3.3.1.7), p. 130,
against full real multiplicative Haar as in A.3.2.2(1), p. 560.
-/

open Complex MeasureTheory NumberField InfinitePlace.Completion Set
open scoped SchwartzMap

namespace Masullo

private theorem integrable_realSchwartzLogRays (b : 𝓢(ℝ, ℂ))
    (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0) (z : ℂ) :
    Integrable (fun t : ℝ ↦ b (Real.exp t) * exp (z * t)) ∧
      Integrable (fun t : ℝ ↦ b (-Real.exp t) * exp (z * t)) := by
  let E (t : ℝ) := realSchwartzParityLogProfile b 0 t * exp (z * t)
  let O (t : ℝ) := realSchwartzParityLogProfile b 1 t * exp (z * t)
  have hE : Integrable E := (hasDerivAt_realSchwartzParityLog_mellin b hflat 0 z).1
  have hO : Integrable O := (hasDerivAt_realSchwartzParityLog_mellin b hflat 1 z).1
  -- Folded integrability alone could come from cancellation. Recover both rays separately.
  constructor
  · refine ((hE.add hO).const_mul (1 / 2 : ℂ)).congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [E, O, Pi.add_apply, realSchwartzParityLogProfile, pow_zero, pow_one, one_mul, neg_one_mul]
    ring
  · refine ((hE.sub hO).const_mul (1 / 2 : ℂ)).congr (Filter.Eventually.of_forall fun t ↦ ?_)
    simp only [E, O, Pi.sub_apply, realSchwartzParityLogProfile, pow_zero, pow_one, one_mul, neg_one_mul]
    ring

/-- For a unitary Hecke character, the same parity and radial frequency identify the raw
flat Schwartz pairing at every complex parameter. Both real signs have Haar mass one in
log coordinates. -/
public theorem realCompletionSchwartzMellinPair {K : Type*} [Field K] [NumberField K]
    {v : InfinitePlace K} [MeasurableSpace v.Completionˣ] [BorelSpace v.Completionˣ]
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (hv : v.IsReal) (b : 𝓢(ℝ, ℂ)) (hflat : ∀ j : ℕ, iteratedDeriv j (b : ℝ → ℂ) 0 = 0) :
    ∃ (ε : ℕ) (τ : ℝ), ε ≤ 1 ∧
      (∀ u : v.Completionˣ,
        let y := extensionEmbeddingOfIsReal hv u.val
        χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) =
          (if 0 < y then (1 : ℂ) else -1) ^ ε * exp (((τ * Real.log |y| : ℝ) : ℂ) * I)) ∧
      ∀ s : ℂ,
        let F := fun u : v.Completionˣ ↦ b (extensionEmbeddingOfIsReal hv u.val) *
          χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) * (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ s)
        Integrable F (realCompletionHaar hv) ∧
          (∫ u, F u ∂realCompletionHaar hv) =
            ∫ t : ℝ, realSchwartzParityLogProfile b ε t * exp ((s + (τ : ℂ) * I) * t) := by
  obtain ⟨ε, τ, hε, hchar⟩ := exists_archimedeanHeckeRestriction_real χ hχ hv
  refine ⟨ε, τ, hε, hchar, fun s ↦ ?_⟩
  let z := s + (τ : ℂ) * I
  let G (p : ℝ × Bool) :=
    (if p.2 then b (Real.exp p.1) else (-1 : ℂ) ^ ε * b (-Real.exp p.1)) * exp (z * p.1)
  have hG : Measurable G := by
    apply Measurable.mul
    · exact Measurable.ite (measurable_snd (measurableSet_singleton true))
        (b.continuous.comp (Real.continuous_exp.comp continuous_fst)).measurable
        (continuous_const.mul (b.continuous.comp (Real.continuous_exp.comp continuous_fst).neg)).measurable
    · fun_prop
  obtain ⟨hp, hm⟩ := integrable_realSchwartzLogRays b hflat z
  have hp' : Integrable (fun t : ℝ ↦ G (t, true)) := by simpa only [G, ite_true] using hp
  have hm' : Integrable (fun t : ℝ ↦ G (t, false)) := by
    simpa only [G, Bool.false_eq_true, ite_false, mul_assoc] using hm.const_mul ((-1 : ℂ) ^ ε)
  have hGi : Integrable G ((volume : Measure ℝ).prod (Measure.count : Measure Bool)) := by
    refine (integrable_prod_iff hG.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun _ ↦ Integrable.of_finite
    · refine (hp'.norm.add hm'.norm).congr (Filter.Eventually.of_forall fun t ↦ ?_)
      simp only [Pi.add_apply, integral_count, Fintype.sum_bool]
  let J (u : v.Completionˣ) :=
    (Real.log ‖u.val‖, if 0 < extensionEmbeddingOfIsReal hv u.val then true else false)
  have hlog : Measurable (fun u : v.Completionˣ ↦ Real.log ‖u.val‖) :=
    Real.measurable_log.comp (continuous_norm.comp Units.continuous_val).measurable
  have hsign : Measurable (fun u : v.Completionˣ ↦
      if 0 < extensionEmbeddingOfIsReal hv u.val then true else false) :=
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const).comp
      (realCompletionEmbedding hv).measurable
  have hJ : Measurable J := hlog.prodMk hsign
  have hmap : Measure.map J (realCompletionHaar hv) = _ := realCompletionHaar_map_logSign hv
  have heq (u : v.Completionˣ) :
      b (extensionEmbeddingOfIsReal hv u.val) * χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) *
        (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ s) = G (J u) := by
    let y := extensionEmbeddingOfIsReal hv u.val
    have hy : y ≠ 0 := (map_ne_zero (extensionEmbeddingOfIsReal hv)).mpr u.ne_zero
    have hn : |y| = ‖u.val‖ :=
      (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) _
    have hr := abs_pos.mpr hy
    have hpow : ((|y| : ℝ) : ℂ) ^ z = exp (z * (Real.log |y| : ℝ)) := by
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le, mul_comm]
    dsimp only [G, J]
    rw [hv.mult_eq_one, pow_one, ← hn, hchar u, ← mul_assoc, mul_assoc (b _ * _),
      positive_cpow_add_radial hr, hpow, Real.exp_log hr]
    rcases lt_or_gt_of_ne hy with hn | hp
    · simp [y, hn.not_gt, abs_of_neg hn, mul_comm (b y)]
    · simp [y, hp, abs_of_pos hp]
  dsimp only
  simp_rw [heq]
  refine ⟨(hmap.symm ▸ hGi).comp_measurable hJ, ?_⟩
  rw [← integral_map_of_stronglyMeasurable hJ hG.stronglyMeasurable, hmap, integral_prod _ hGi]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun t ↦ ?_
  change (∫ q, G (t, q) ∂(Measure.count : Measure Bool)) =
    realSchwartzParityLogProfile b ε t * exp (z * t)
  simp only [integral_count, Fintype.sum_bool, G, Bool.false_eq_true, ite_false, ite_true,
    realSchwartzParityLogProfile, add_mul]

end Masullo
