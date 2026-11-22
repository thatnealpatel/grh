module

public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Pointwise reduction by Archimedean torsion

Masullo specifies the half-open sector in Definition A.2.3.6, (A.2.3.13), PDF p. 549,
and uses it as a fundamental domain for the torsion action in the proof of Lemma A.2.3.8(2),
PDF p. 551 (provisional reading from the text and PDF layout). Here we supply the pointwise
argument: identify the images of torsion and reduce the phase, including the sector boundaries.
-/

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K] {v : InfinitePlace K}

private def torsionNegOne (K : Type*) [Field K] : NumberField.Units.torsion K :=
  ⟨-1, neg_one_mem_torsion⟩

private theorem torsion_eq_one_or_negOne (hv : v.IsReal) (ζ : NumberField.Units.torsion K) :
    ζ = 1 ∨ ζ = torsionNegOne K := by
  have hnorm : |embedding_of_isReal hv (ζ.val : K)| = 1 := by
    rw [← Real.norm_eq_abs, norm_embedding_of_isReal]
    exact (NumberField.Units.mem_torsion K).mp ζ.property v
  have hinj : Function.Injective
      (fun a : NumberField.Units.torsion K ↦ embedding_of_isReal hv (a.val : K)) :=
    (embedding_of_isReal hv).injective.comp
      ((NumberField.Units.coe_injective K).comp Subtype.val_injective)
  rcases (abs_eq zero_le_one).mp hnorm with h | h
  · left
    apply hinj
    simpa only [Subgroup.coe_one, NumberField.Units.coe_one, map_one] using h
  · right
    apply hinj
    simpa only [torsionNegOne, NumberField.Units.coe_neg_one, map_neg, map_one] using h

/-- At a real place exactly one torsion multiplier sends a nonzero real number to the
positive ray. -/
public theorem existsUnique_torsion_real_pos (hv : v.IsReal) {x : ℝ} (hx : x ≠ 0) :
    ∃! ζ : NumberField.Units.torsion K, 0 < embedding_of_isReal hv (ζ.val : K) * x := by
  have hpos (ζ : NumberField.Units.torsion K) (hζ : ζ = 1) :
      (0 < embedding_of_isReal hv (ζ.val : K) * x) ↔ 0 < x := by
    simp [hζ]
  have hneg (ζ : NumberField.Units.torsion K) (hζ : ζ = torsionNegOne K) :
      (0 < embedding_of_isReal hv (ζ.val : K) * x) ↔ x < 0 := by
    simp [hζ, torsionNegOne]
  rcases hx.lt_or_gt with h | h
  · refine ⟨torsionNegOne K, (hneg _ rfl).2 h, ?_⟩
    intro ζ hζ
    rcases torsion_eq_one_or_negOne hv ζ with h₁ | h₁
    · exact False.elim (h.not_gt ((hpos _ h₁).1 hζ))
    · exact h₁
  · refine ⟨1, (hpos _ rfl).2 h, ?_⟩
    intro ζ hζ
    rcases torsion_eq_one_or_negOne hv ζ with h₁ | h₁
    · exact h₁
    · exact False.elim (h.not_gt ((hneg _ h₁).1 hζ))

/-- A number field with a real place has precisely the two torsion units `1` and `-1`. -/
public theorem torsionOrder_eq_two_of_isReal (hv : v.IsReal) :
    NumberField.Units.torsionOrder K = 2 := by
  classical
  let := Fintype.ofFinite (NumberField.Units.torsion K)
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  apply Finset.card_eq_two.mpr
  refine ⟨1, torsionNegOne K, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun a : NumberField.Units.torsion K ↦ (a.val : K)) h
    simp only [Subgroup.coe_one, NumberField.Units.coe_one, torsionNegOne,
      NumberField.Units.coe_neg_one] at hh
    exact (Ring.neg_one_ne_one_of_char_ne_two (ringChar.eq_zero.trans_ne (by decide))) hh.symm
  · ext ζ
    simpa using torsion_eq_one_or_negOne hv ζ

private noncomputable def torsionCircle (v : InfinitePlace K)
    (ζ : NumberField.Units.torsion K) : Circle :=
  ⟨v.embedding (ζ.val : K), by
    change v.embedding (ζ.val : K) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_embedding_eq]
    exact (NumberField.Units.mem_torsion K).mp ζ.property v⟩

private theorem torsionCircle_injective (v : InfinitePlace K) :
    Function.Injective (torsionCircle v) := by
  intro a b h
  exact Subtype.ext (NumberField.Units.coe_injective K
    (v.embedding.injective (congrArg Subtype.val h)))

private theorem circle_exp_arg_mul (r : Circle) {z : ℂ} (hz : z ≠ 0) :
    Circle.exp (Complex.arg ((r : ℂ) * z)) = r * Circle.exp (Complex.arg z) := by
  apply Circle.ext
  simp only [Circle.coe_mul, Circle.coe_exp]
  apply mul_left_cancel₀ (a := (‖z‖ : ℂ)) (by exact_mod_cast norm_ne_zero_iff.mpr hz)
  calc
    (‖z‖ : ℂ) * Complex.exp (Complex.arg ((r : ℂ) * z) * Complex.I) = (r : ℂ) * z := by
      simpa only [norm_mul, Circle.norm_coe, one_mul] using
        Complex.norm_mul_exp_arg_mul_I ((r : ℂ) * z)
    _ = (‖z‖ : ℂ) * ((r : ℂ) * Complex.exp (Complex.arg z * Complex.I)) := by
      rw [← mul_left_comm, Complex.norm_mul_exp_arg_mul_I]

/-- At a complex embedding exactly one torsion multiplier puts a nonzero number's
principal argument in the half-open sector beginning at zero. -/
public theorem existsUnique_torsion_complex_arg {z : ℂ} (hz : z ≠ 0) :
    ∃! ζ : NumberField.Units.torsion K,
      Complex.arg (v.embedding (ζ.val : K) * z) ∈
        Set.Ico 0 (2 * Real.pi / (NumberField.Units.torsionOrder K : ℝ)) := by
  let w := NumberField.Units.torsionOrder K
  have hw : (0 : ℝ) < w := by exact_mod_cast NumberField.Units.torsionOrder_pos K
  have hw₂ : (2 : ℝ) ≤ w := by
    have hn := NumberField.Units.torsionOrder_pos K
    obtain ⟨k, hk⟩ := NumberField.Units.even_torsionOrder K
    have : 2 ≤ NumberField.Units.torsionOrder K := by omega
    exact_mod_cast this
  let s := 2 * Real.pi / (w : ℝ)
  have hs : 0 < s := div_pos Real.two_pi_pos hw
  have hsπ : s ≤ Real.pi := (div_le_iff₀ hw).2 (by nlinarith [Real.pi_pos])
  have hws : (w : ℝ) * s = 2 * Real.pi := by
    rw [mul_comm, div_mul_cancel₀ _ hw.ne']
  have hroot (ζ : NumberField.Units.torsion K) : torsionCircle v ζ ^ w = 1 := by
    apply Circle.ext
    simp only [Circle.coe_pow, Circle.coe_one]
    change v.embedding (ζ.val : K) ^ w = 1
    have h := NumberField.Units.pow_torsionOrder_eq_one K ζ.property
    simpa only [map_pow, map_one, NumberField.Units.coe_pow, NumberField.Units.coe_one] using
      congrArg (fun u : (𝓞 K)ˣ ↦ v.embedding (u : K)) h
  -- Reduce the argument by an integer number of sector widths.
  obtain ⟨m, hm, -⟩ := existsUnique_add_zsmul_mem_Ico hs z.arg 0
  rw [zero_add] at hm
  let r := Circle.exp (m • s)
  have hr : r ^ w = 1 := by
    rw [← Circle.exp_natCast_mul, zsmul_eq_mul, mul_left_comm, hws, Circle.exp_int_mul_two_pi]
  have hmap : Circle.toUnits r ∈ (NumberField.Units.torsion K).map
      (NumberField.Units.complexEmbedding v.embedding) := by
    rw [NumberField.Units.map_complexEmbedding_torsion, mem_rootsOfUnity, ← map_pow, hr, map_one]
  obtain ⟨u, hu, hemb⟩ := Subgroup.mem_map.mp hmap
  let ζ : NumberField.Units.torsion K := ⟨u, hu⟩
  have hζr : torsionCircle v ζ = r :=
    Circle.ext (congrArg Units.val hemb)
  let θ := z.arg + m • s
  have harg : Complex.arg (v.embedding (ζ.val : K) * z) = θ := by
    let a := Complex.arg (v.embedding (ζ.val : K) * z)
    have he : Circle.exp a = Circle.exp θ := by
      change Circle.exp (Complex.arg ((torsionCircle v ζ : ℂ) * z)) = _
      rw [circle_exp_arg_mul _ hz, hζr, Circle.exp_add]
      exact mul_comm _ _
    calc
      a = Complex.arg (Circle.exp a : ℂ) :=
        (Circle.arg_exp (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _)).symm
      _ = Complex.arg (Circle.exp θ : ℂ) := congrArg (fun q : Circle ↦ Complex.arg q) he
      _ = θ := Circle.arg_exp (by linarith [Real.pi_pos, hm.1]) (hm.2.le.trans hsπ)
  have hζarg : Complex.arg (v.embedding (ζ.val : K) * z) ∈ Set.Ico 0 s := by
    rw [harg]
    exact hm
  refine ⟨ζ, hζarg, ?_⟩
  intro η hη
  -- Raising the phases to `w` kills both multipliers. The two scaled principal
  -- arguments lie in `[0, 2π)`, where the circle exponential is injective.
  let argOf (a : NumberField.Units.torsion K) := Complex.arg (v.embedding (a.val : K) * z)
  have hpow (a : NumberField.Units.torsion K) :
      Circle.exp ((w : ℝ) * argOf a) = Circle.exp (z.arg) ^ w := by
    rw [Circle.exp_natCast_mul, show Circle.exp (argOf a) =
      torsionCircle v a * Circle.exp (z.arg) from circle_exp_arg_mul (torsionCircle v a) hz,
      mul_pow, hroot, one_mul]
  have hmem {t : ℝ} (ht : t ∈ Set.Ico 0 s) : (w : ℝ) * t ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨mul_nonneg hw.le ht.1, hws ▸ mul_lt_mul_of_pos_left ht.2 hw⟩
  have hθ : argOf η = argOf ζ := by
    apply mul_left_cancel₀ hw.ne'
    apply Circle.exp_injOn_Ico (by rw [sub_zero]) (hmem hη) (hmem hζarg)
    exact (hpow η).trans (hpow ζ).symm
  apply torsionCircle_injective v
  apply mul_right_cancel (b := Circle.exp z.arg)
  rw [← circle_exp_arg_mul (torsionCircle v η) hz, ← circle_exp_arg_mul (torsionCircle v ζ) hz]
  exact congrArg Circle.exp hθ

end NumberField.InfinitePlace
