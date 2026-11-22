module

public import Theorems.ArchimedeanHeckeRestriction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lemmas.OneParameterCharacter

/-! # Real Archimedean Hecke characters

Masullo, p. 121, (3.1.2.3)–(4), splits the real completion units into
positive radii and signs, and restricts the global character along `j_v`.
The two real Gamma cases on p. 123, (3.2.1.4), use that split. The
decomposition below identifies the parity and the imaginary radial shift
of the actual restricted character. The continuous positive-radius
classification used here is a project proof, not an appeal to the
parametrization cited in §3.1.2.1.
-/

open NumberField InfinitePlace.Completion

namespace Masullo

private noncomputable def expUnit : Multiplicative ℝ →* ℝˣ where
  toFun t := Units.mk0 (Real.exp t.toAdd) (Real.exp_ne_zero _)
  map_one' := Units.ext Real.exp_zero
  map_mul' s t := Units.ext (Real.exp_add s.toAdd t.toAdd)

private theorem continuous_expUnit : Continuous fun t : ℝ => expUnit (.ofAdd t) := by
  refine Units.continuous_iff.mpr ⟨Real.continuous_exp, ?_⟩
  change Continuous fun t : ℝ => (Real.exp t)⁻¹
  simpa only [← Real.exp_neg, Function.comp_def] using Real.continuous_exp.comp continuous_neg

/-- At a real place the restricted unitary character has parity `b` and
radial twist `exp (i τ log |y|)` in the real coordinate `y`. -/
public theorem exists_archimedeanHeckeRestriction_real {K : Type*} [Field K] [NumberField K]
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    {v : InfinitePlace K} (hv : v.IsReal) :
    ∃ (b : ℕ) (τ : ℝ), b ≤ 1 ∧ ∀ x : v.Completionˣ,
      let y := extensionEmbeddingOfIsReal hv (x : v.Completion)
      χ (IdeleClassGroup.ofCompletion (𝓞 K) K v x) =
        (if 0 < y then (1 : ℂ) else -1) ^ b *
          Complex.exp (((τ * Real.log |y| : ℝ) : ℂ) * Complex.I) := by
  let e := ringEquivRealOfIsReal hv
  let j := IdeleClassGroup.ofCompletion (𝓞 K) K v
  let f : ℝˣ →* ℂ := χ.toMonoidHom.comp (j.comp (Units.map e.symm.toMonoidHom))
  have hf : Continuous f :=
    (continuous_archimedeanHeckeRestriction χ v).comp
      (Units.continuous_map (f := e.symm.toMonoidHom)
        (isometryEquivRealOfIsReal hv).symm.continuous)
  -- The positive radii are a one-parameter group in the log coordinate.
  obtain ⟨τ, hτ, _⟩ := existsUnique_unitary_oneParameterCharacter
    (fun t => f (expUnit (.ofAdd t))) (hf.comp continuous_expUnit)
    (by change f (expUnit 1) = 1; rw [map_one, map_one])
    (fun s t => by change f (expUnit (.ofAdd s * .ofAdd t)) = _; rw [map_mul, map_mul])
    (fun _ => hχ _)
  -- The sign is determined by the image of the nontrivial element of μ₂.
  let m : ℝˣ := Units.mk0 (-1) (by norm_num)
  have hm : m ^ 2 = 1 := Units.ext (by change (-1 : ℝ) ^ 2 = 1; norm_num)
  have hm' : f m ^ 2 = 1 := by rw [← map_pow, hm, map_one]
  obtain ⟨b, hb, hparity⟩ : ∃ b : ℕ, b ≤ 1 ∧ f m = (-1 : ℂ) ^ b := by
    rcases sq_eq_one_iff.mp hm' with h | h
    · exact ⟨0, by decide, by simpa using h⟩
    · exact ⟨1, by decide, by simpa using h⟩
  refine ⟨b, τ, hb, fun x => ?_⟩
  let u := Units.map e.toMonoidHom x
  have hu : Units.map e.symm.toMonoidHom u = x := Units.ext (e.symm_apply_apply _)
  have hfu : f u = χ (j x) := by
    change χ (j (Units.map e.symm.toMonoidHom u)) = _
    rw [hu]
  change χ (j x) = (if 0 < (u : ℝ) then (1 : ℂ) else -1) ^ b *
    Complex.exp (((τ * Real.log |(u : ℝ)| : ℝ) : ℂ) * Complex.I)
  rw [← hfu]
  -- Recombine the radial and sign values on the given real unit.
  let r := expUnit (.ofAdd (Real.log (u : ℝ)))
  have hr : (r : ℝ) = |(u : ℝ)| := Real.exp_log_eq_abs u.ne_zero
  have hrad : f r = Complex.exp (((τ * Real.log |(u : ℝ)| : ℝ) : ℂ) * Complex.I) := by
    rw [Real.log_abs]
    exact hτ _
  rcases lt_or_gt_of_ne u.ne_zero with hneg | hpos
  · have hsplit : m * r = u := Units.ext (by
      change -1 * (r : ℝ) = (u : ℝ)
      rw [hr, abs_of_neg hneg, neg_one_mul, neg_neg])
    conv_lhs => rw [← hsplit, map_mul, hparity, hrad]
    rw [ite_eq_right hneg.not_gt]
  · have hsplit : r = u := Units.ext (hr.trans (abs_of_pos hpos))
    conv_lhs => rw [← hsplit, hrad]
    simp [hpos]

end Masullo
