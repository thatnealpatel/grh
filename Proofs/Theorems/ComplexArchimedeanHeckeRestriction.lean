module

public import Theorems.ArchimedeanHeckeRestriction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lemmas.OneParameterCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Complex Archimedean Hecke characters

Masullo, p. 121, (3.1.2.3)–(4), supplies the split into a positive radius
and a circle and the restriction along `j_v`. The complex Gamma factor
on p. 123, (3.2.1.5), uses the integer angular weight. We derive that
weight and the radial frequency for the actual restriction, using the
project's one-parameter classification and descent along the circle
cover. The radial coordinate is the squared Euclidean norm, as in
§A.1, p. 539. This theorem does not evaluate a complex local zeta integral.
-/

open NumberField InfinitePlace.Completion

namespace Masullo

private theorem continuous_circleToUnits : Continuous Circle.toUnits := by
  refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
  simp only [← map_inv]
  change Continuous fun w : Circle => ((w⁻¹ : Circle) : ℂ)
  exact continuous_subtype_val.comp continuous_inv

private noncomputable def complexRadialUnit : Multiplicative ℝ →* ℂˣ where
  toFun t := Units.mk0 (Real.exp (t.toAdd / 2) : ℂ) (by simp)
  map_one' := Units.ext (by change (Real.exp (0 / 2) : ℂ) = 1; simp)
  map_mul' s t := Units.ext (by
    change (Real.exp ((s.toAdd + t.toAdd) / 2) : ℂ) =
      (Real.exp (s.toAdd / 2) : ℂ) * (Real.exp (t.toAdd / 2) : ℂ)
    rw [add_div, Real.exp_add, Complex.ofReal_mul])

private theorem continuous_complexRadialUnit :
    Continuous fun t : ℝ => complexRadialUnit (.ofAdd t) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous fun t : ℝ => (Real.exp (t / 2) : ℂ)
    fun_prop
  · change Continuous fun t : ℝ => (Real.exp (t / 2) : ℂ)⁻¹
    simp only [← Complex.ofReal_inv, ← Real.exp_neg]
    fun_prop

/-- At a complex place the restricted unitary character is the product of
an integer angular character and a twist of the squared Euclidean norm. -/
public theorem exists_archimedeanHeckeRestriction_complex {K : Type*} [Field K] [NumberField K]
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    {v : InfinitePlace K} (hv : v.IsComplex) :
    ∃ (n : ℤ) (τ : ℝ), ∀ x : v.Completionˣ,
      let z := extensionEmbedding v (x : v.Completion)
      χ (IdeleClassGroup.ofCompletion (𝓞 K) K v x) =
        (z / (‖z‖ : ℂ)) ^ n *
          Complex.exp (((τ * Real.log (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) := by
  let e := ringEquivComplexOfIsComplex hv
  let j := IdeleClassGroup.ofCompletion (𝓞 K) K v
  let f : ℂˣ →* ℂ := χ.toMonoidHom.comp (j.comp (Units.map e.symm.toMonoidHom))
  have hf : Continuous f :=
    (continuous_archimedeanHeckeRestriction χ v).comp
      (Units.continuous_map (f := e.symm.toMonoidHom)
        (isometryEquivComplexOfIsComplex hv).symm.continuous)
  -- Pull back the angular character to the covering real line.
  let g := f.comp Circle.toUnits
  obtain ⟨a, ha, _⟩ := existsUnique_unitary_oneParameterCharacter
    (fun t => g (Circle.exp t)) ((hf.comp continuous_circleToUnits).comp Circle.exp.continuous)
    (by rw [Circle.exp_zero, map_one]) (fun s t => by rw [Circle.exp_add, map_mul])
    (fun _ => hχ _)
  -- One full turn forces the frequency to be an integer, so it descends.
  have hperiod : Circle.exp (a * (2 * Real.pi)) = 1 := by
    apply Subtype.ext
    rw [Circle.coe_exp, ← ha, Circle.exp_two_pi, map_one]
    rfl
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hperiod
  have han : a = (n : ℝ) := mul_right_cancel₀ (by positivity : 2 * Real.pi ≠ 0) hn
  have hang (w : Circle) : g w = (w : ℂ) ^ n := by
    obtain ⟨t, rfl⟩ := Circle.exp_surjective w
    rw [ha, han, ← Circle.coe_exp, Circle.exp_intCast_mul, Circle.coe_zpow]
  -- The radial pullback is parametrized by the logarithm of the squared norm.
  obtain ⟨τ, hτ, _⟩ := existsUnique_unitary_oneParameterCharacter
    (fun t => f (complexRadialUnit (.ofAdd t))) (hf.comp continuous_complexRadialUnit)
    (by change f (complexRadialUnit 1) = 1; rw [map_one, map_one])
    (fun s t => by change f (complexRadialUnit (.ofAdd s * .ofAdd t)) = _; rw [map_mul, map_mul])
    (fun _ => hχ _)
  refine ⟨n, τ, fun x => ?_⟩
  let u := Units.map e.toMonoidHom x
  have hfu : f u = χ (j x) := by
    change χ (j (Units.map e.symm.toMonoidHom u)) = _
    rw [show Units.map e.symm.toMonoidHom u = x from Units.ext (e.symm_apply_apply _)]
  let z : ℂ := u
  change χ (j x) = (z / (‖z‖ : ℂ)) ^ n *
    Complex.exp (((τ * Real.log (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I)
  rw [← hfu]
  -- Multiply the two values on the polar factors of the given unit.
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr u.ne_zero
  have hzC : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  let w : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hz.le, div_self hz.ne'])⟩
  let t := Real.log (‖z‖ ^ 2)
  have hr : (complexRadialUnit (.ofAdd t) : ℂ) = (‖z‖ : ℂ) := by
    change (Real.exp (Real.log (‖z‖ ^ 2) / 2) : ℂ) = (‖z‖ : ℂ)
    rw [Real.log_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.exp_log hz]
  have hsplit : Circle.toUnits w * complexRadialUnit (.ofAdd t) = u := Units.ext (by
    rw [Units.val_mul, hr]
    exact div_mul_cancel₀ z hzC)
  conv_lhs => rw [← hsplit, map_mul, show f (Circle.toUnits w) = (w : ℂ) ^ n from hang w, hτ t]

end Masullo
