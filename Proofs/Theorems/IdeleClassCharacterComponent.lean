module

public import Theorems.IdeleClassCompactHausdorff
public import Mathlib.NumberTheory.NumberField.HeckeLFunction
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Lemmas.OneParameterCharacter
import Mathlib.Topology.Instances.RealVectorSpace

/-! # The component of the trivial idelic quasi-character

In §3.1.1, (3.1.1.1), p. 119, the fibre of restriction to the trivial
norm-one character consists of the complex norm powers. For the actual
idele class group we identify this fibre with the connected component of
one in the compact-open topology, and identify its unitary points. This
justifies the unitary base point in §1.1.4, second bullet, p. 12.
-/

open Complex NumberField Topology

namespace Masullo

private theorem existsUnique_complex_oneParameter (f : Multiplicative ℝ →ₜ* ℂ) :
    ∃! s : ℂ, ∀ t : ℝ, f (Multiplicative.ofAdd t) = Complex.exp (s * (t : ℂ)) := by
  let h (t : ℝ) := f (Multiplicative.ofAdd t)
  have hc : Continuous h := f.continuous.comp continuous_ofAdd
  have h0 : h 0 = 1 := map_one f
  have ha (t u : ℝ) : h (t + u) = h t * h u := map_mul f _ _
  have hnz (t : ℝ) : h t ≠ 0 := (f.toMonoidHom.toHomUnits (Multiplicative.ofAdd t)).ne_zero
  let a : ℝ →+ ℝ :=
    { toFun := fun t ↦ Real.log ‖h t‖
      map_zero' := by simp [h0]
      map_add' := fun t u ↦ by
        rw [ha, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hnz t))
          (norm_ne_zero_iff.mpr (hnz u))] }
  have hac : Continuous a := hc.norm.log fun t ↦ norm_ne_zero_iff.mpr (hnz t)
  have hreal (t : ℝ) : Real.log ‖h t‖ = t * a 1 := by
    change a t = _
    simpa only [smul_eq_mul, mul_one] using map_real_smul a hac t (1 : ℝ)
  let g (t : ℝ) := Complex.exp (-(a 1 : ℂ) * t) * h t
  have hgc : Continuous g := (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal)).mul hc
  have hg0 : g 0 = 1 := by simp [g, h0]
  have hga (t u : ℝ) : g (t + u) = g t * g u := by
    simp only [g, ofReal_add, mul_add, Complex.exp_add, ha]
    ac_rfl
  have hgn (t : ℝ) : ‖g t‖ = 1 := by
    dsimp only [g]
    rw [norm_mul, show ‖h t‖ = Real.exp (t * a 1) from (Real.exp_log (norm_pos_iff.mpr (hnz t))).symm.trans
      (congrArg Real.exp (hreal t))]
    simp only [Complex.norm_exp, neg_mul, ← ofReal_mul, neg_re, ofReal_re,
      ← Real.exp_add, mul_comm (a 1) t, neg_add_cancel, Real.exp_zero]
  obtain ⟨τ, hτ, _⟩ := existsUnique_unitary_oneParameterCharacter g hgc hg0 hga hgn
  let s : ℂ := (a 1 : ℂ) + (τ : ℂ) * Complex.I
  have hs (t : ℝ) : h t = Complex.exp (s * (t : ℂ)) := calc
    h t = Complex.exp ((a 1 : ℂ) * t) * g t := by
      dsimp only [g]
      rw [← mul_assoc, ← Complex.exp_add, ← add_mul, add_neg_cancel, zero_mul,
        Complex.exp_zero, one_mul]
    _ = Complex.exp (s * (t : ℂ)) := by
      rw [hτ, ← Complex.exp_add]
      congr 1
      push_cast
      dsimp [s]
      ring
  refine ⟨s, hs, fun k hk ↦ ?_⟩
  have deriv (b : ℂ) : HasDerivAt (fun t : ℝ ↦ Complex.exp (b * (t : ℂ))) b 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul b).cexp)
  exact (show HasDerivAt h k 0 from (funext hk : h = _).symm ▸ deriv k).unique
    ((funext hs : h = _).symm ▸ deriv s)

variable {K : Type*} [Field K] [NumberField K]

local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)
local notation "Ω" => HeckeCharacter (𝓞 K) K

private def complexUnitVal : ℂˣ →ₜ* ℂ :=
  ⟨Units.coeHom ℂ, Units.isEmbedding_val₀.continuous⟩

/-- Mathlib's complex-valued realization of the quasi-character space has
exactly the compact-open topology of the manuscript's `ℂˣ`-valued one. -/
public noncomputable def ideleClassQuasiCharacterHomeomorph : (C →ₜ* ℂˣ) ≃ₜ Ω := by
  let f : (C →ₜ* ℂˣ) → Ω := fun χ ↦ complexUnitVal.comp χ
  have hf : IsEmbedding f := (ContinuousMonoidHom.isEmbedding_toContinuousMap C ℂ).of_comp_iff.mp
    ((complexUnitVal.toContinuousMap.isEmbedding_postcomp Units.isEmbedding_val₀).comp
      (ContinuousMonoidHom.isEmbedding_toContinuousMap C ℂˣ))
  refine hf.toHomeomorphOfSurjective fun χ ↦ ?_
  let ψ : C →ₜ* ℂˣ := ⟨χ.toMonoidHom.toHomUnits,
    Units.isEmbedding_val₀.isInducing.continuous_iff.mpr χ.continuous⟩
  exact ⟨ψ, ContinuousMonoidHom.ext fun _ ↦ rfl⟩

public theorem ideleClassQuasiCharacterHomeomorph_apply (χ : C →ₜ* ℂˣ) (c : C) :
    ideleClassQuasiCharacterHomeomorph χ c = (χ c : ℂ) := by rfl

/-- The norm power `|·|_K^s` on actual idele classes, written in log coordinates. -/
public noncomputable def ideleClassNormPower (s : ℂ) : Ω where
  toFun c := Complex.exp (s * ((ideleClassLogNorm c).toAdd : ℂ))
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul]
    change Complex.exp (s * (((ideleClassLogNorm x).toAdd + (ideleClassLogNorm y).toAdd : ℝ) : ℂ)) = _
    rw [ofReal_add, mul_add, Complex.exp_add]
  continuous_toFun := Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_toAdd.comp ideleClassLogNorm.continuous)))

public theorem ideleClassNormPower_apply (s : ℂ) (c : C) :
    ideleClassNormPower s c = (ideleClassNorm c : ℂ) ^ s := by
  change Complex.exp (s * ((ideleClassLogNorm c).toAdd : ℂ)) = _
  rw [ideleClassLogNorm_apply, Complex.ofReal_log (ideleClassNorm_pos c).le,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ideleClassNorm_pos c).ne'), mul_comm]

/-- Norm twists are a continuous family for the compact-open topology. -/
public theorem continuous_ideleClassNormPower : Continuous (ideleClassNormPower (K := K)) :=
  ContinuousMonoidHom.continuous_of_continuous_uncurry _ (Complex.continuous_exp.comp
    (continuous_fst.mul ((Complex.continuous_ofReal.comp
      (continuous_toAdd.comp ideleClassLogNorm.continuous)).comp continuous_snd)))

public theorem ideleClassNormPower_on_normOne (s : ℂ) (c : C₁) :
    ideleClassNormPower s (c : C) = 1 := by
  have hc : ideleClassLogNorm (c : C) = 1 := Multiplicative.toAdd.injective (by
    rw [ideleClassLogNorm_apply, (mem_ideleClassNormOne _).mp c.property, Real.log_one]
    rfl)
  change Complex.exp (s * ((ideleClassLogNorm (c : C)).toAdd : ℂ)) = _
  rw [hc]
  simp

private theorem normPower_injective : Function.Injective (ideleClassNormPower (K := K)) := by
  intro s t h
  let v : InfinitePlace K := Classical.choice inferInstance
  let f := (ideleClassNormPower (K := K) s).comp (ideleClassLogSection v)
  obtain ⟨_, _, hu⟩ := existsUnique_complex_oneParameter f
  have hs (u : ℝ) : f (Multiplicative.ofAdd u) = Complex.exp (s * (u : ℂ)) := by
    change Complex.exp (s * ((ideleClassLogNorm (ideleClassLogSection v (Multiplicative.ofAdd u))).toAdd : ℂ)) = _
    rw [ideleClassLogNorm_section]
    rfl
  have ht (u : ℝ) : f (Multiplicative.ofAdd u) = Complex.exp (t * (u : ℂ)) := by
    have hst := congrArg (fun ψ : Ω ↦ ψ (ideleClassLogSection v (Multiplicative.ofAdd u))) h
    change f (Multiplicative.ofAdd u) = _ at hst
    rw [hst]
    change Complex.exp (t * ((ideleClassLogNorm (ideleClassLogSection v (Multiplicative.ofAdd u))).toAdd : ℂ)) = _
    rw [ideleClassLogNorm_section]
    rfl
  exact (hu _ hs).trans (hu _ ht).symm

/-- A quasi-character trivial on the actual norm-one classes is a unique
complex norm power, with no unitary hypothesis. -/
public theorem ideleClassNormPower_existsUnique (χ : Ω) (hχ : ∀ c : C₁, χ (c : C) = 1) :
    ∃! s : ℂ, χ = ideleClassNormPower s := by
  let v : InfinitePlace K := Classical.choice inferInstance
  let f := χ.comp (ideleClassLogSection v)
  obtain ⟨s, hs, _⟩ := existsUnique_complex_oneParameter f
  have he : χ = ideleClassNormPower s := by
    ext c
    let z : C₁ := ⟨(ideleClassLogSection v (ideleClassLogNorm c))⁻¹ * c, by
      apply (mem_ideleClassNormOne _).mpr
      have hl : ideleClassLogNorm ((ideleClassLogSection v (ideleClassLogNorm c))⁻¹ * c) = 1 := by
        rw [map_mul, map_inv, ideleClassLogNorm_section, inv_mul_cancel]
      have hz := congrArg Multiplicative.toAdd hl
      rw [ideleClassLogNorm_apply] at hz
      rw [← Real.exp_log (ideleClassNorm_pos _), hz]
      exact Real.exp_zero⟩
    have hz : ideleClassLogSection v (ideleClassLogNorm c) * (z : C) = c := mul_inv_cancel_left _ _
    calc
      χ c = χ (ideleClassLogSection v (ideleClassLogNorm c) * (z : C)) := congrArg χ hz.symm
      _ = f (ideleClassLogNorm c) := by rw [map_mul, hχ z, mul_one]; rfl
      _ = _ := hs (ideleClassLogNorm c).toAdd
  exact ⟨s, he, fun t ht ↦ normPower_injective (ht.symm.trans he)⟩

private theorem compact_character_norm {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (χ : G →ₜ* ℂ) (x : G) : ‖χ x‖ = 1 := by
  obtain ⟨M, hM⟩ := (isCompact_range χ.continuous.norm).bddAbove
  have hb (z : G) : ‖χ z‖ ≤ 1 := by
    by_contra! hz
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hz
    exact (not_lt_of_ge (hM ⟨z ^ n, by
      change ‖χ (z ^ n)‖ = _
      rw [map_pow, norm_pow]⟩)) hn
  have hi : ‖χ x‖ * ‖χ x⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  exact le_antisymm (hb x) (by nlinarith [mul_le_mul_of_nonneg_left (hb x⁻¹) (norm_nonneg (χ x))])

/-- Restrict a quasi-character to the norm-one subgroup. Compactness gives
unitarity there, so the codomain really is the Pontryagin dual. -/
public noncomputable def ideleClassNormOneRestriction (χ : Ω) : PontryaginDual C₁ := by
  let : CompactSpace C₁ := compactHausdorff_ideleClassNormOne.1
  let f : C₁ →ₜ* ℂ := χ.comp ⟨Subgroup.subtype C₁, continuous_subtype_val⟩
  exact { toFun := fun c ↦ ⟨f c, mem_sphere_zero_iff_norm.mpr (compact_character_norm f c)⟩
          map_one' := Subtype.ext (map_one f)
          map_mul' := fun x y ↦ Subtype.ext (map_mul f x y)
          continuous_toFun := f.continuous.subtype_mk _ }

public theorem ideleClassNormOneRestriction_apply (χ : Ω) (c : C₁) :
    (ideleClassNormOneRestriction χ c : ℂ) = χ (c : C) := by rfl

public theorem continuous_ideleClassNormOneRestriction :
    Continuous (ideleClassNormOneRestriction (K := K)) := by
  let : CompactSpace C₁ := compactHausdorff_ideleClassNormOne.1
  let incl : C₁ →ₜ* C := ⟨Subgroup.subtype C₁, continuous_subtype_val⟩
  have h : Continuous (fun p : Ω × C₁ ↦ (p.1.comp incl) p.2) :=
    continuous_eval.comp ((incl.continuous_comp_left.comp continuous_fst).prodMk continuous_snd)
  exact ContinuousMonoidHom.continuous_of_continuous_uncurry _ (h.subtype_mk _)

/-- The component containing the trivial quasi-character consists exactly
of the quasi-characters trivial on the norm-one subgroup. -/
public theorem ideleClass_component_one (χ : Ω) :
    χ ∈ connectedComponent (1 : Ω) ↔ ∀ c : C₁, χ (c : C) = 1 := by
  let : CompactSpace C₁ := compactHausdorff_ideleClassNormOne.1
  have h1 : ideleClassNormOneRestriction (1 : Ω) = 1 := by
    ext c
    rfl
  constructor
  · intro hχ c
    have h := continuous_ideleClassNormOneRestriction.mapsTo_connectedComponent (1 : Ω) hχ
    rw [h1, connectedComponent_eq_singleton, Set.mem_singleton_iff] at h
    simpa only [ideleClassNormOneRestriction_apply, PontryaginDual.one_apply, Circle.coe_one]
      using congrArg (fun ψ : PontryaginDual C₁ ↦ (ψ c : ℂ)) h
  · intro hχ
    obtain ⟨s, rfl, _⟩ := ideleClassNormPower_existsUnique χ hχ
    have h0 : ideleClassNormPower (K := K) 0 = 1 := by
      ext c
      change Complex.exp (0 * ((ideleClassLogNorm c).toAdd : ℂ)) = 1
      simp
    have hz : (1 : Ω) ∈ Set.range (ideleClassNormPower (K := K)) := ⟨0, h0⟩
    exact (isPreconnected_range continuous_ideleClassNormPower).subset_connectedComponent hz ⟨s, rfl⟩

/-- The norm power is unitary if and only if its exponent is imaginary. -/
public theorem ideleClassNormPower_unitary_iff (s : ℂ) :
    (∀ c : C, ‖ideleClassNormPower s c‖ = 1) ↔ s.re = 0 := by
  have hnorm (c : C) : ‖ideleClassNormPower s c‖ =
      Real.exp (s.re * (ideleClassLogNorm c).toAdd) := by
    change ‖Complex.exp (s * ((ideleClassLogNorm c).toAdd : ℂ))‖ = _
    simp [Complex.norm_exp, Complex.mul_re]
  constructor
  · intro h
    let v : InfinitePlace K := Classical.choice inferInstance
    have h' := h (ideleClassLogSection v (Multiplicative.ofAdd 1))
    rw [hnorm, ideleClassLogNorm_section] at h'
    change Real.exp (s.re * 1) = 1 at h'
    rw [mul_one] at h'
    exact Real.exp_injective (h'.trans Real.exp_zero.symm)
  · intro h c
    simp [hnorm, h]

/-- Exactly the imaginary norm powers are the unitary points in the component
of one, with unique real frequency. -/
public theorem ideleClass_component_one_unitary (χ : Ω) :
    (χ ∈ connectedComponent (1 : Ω) ∧ ∀ c : C, ‖χ c‖ = 1) ↔
      ∃! τ : ℝ, χ = ideleClassNormPower ((τ : ℂ) * Complex.I) := by
  constructor
  · rintro ⟨hc, hn⟩
    obtain ⟨s, rfl, _⟩ := ideleClassNormPower_existsUnique χ ((ideleClass_component_one χ).mp hc)
    have hs := (ideleClassNormPower_unitary_iff (K := K) s).mp hn
    have he : s = (s.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hs, mul_re, mul_im]
    refine ⟨s.im, congrArg (ideleClassNormPower (K := K)) he, fun τ hτ ↦ ?_⟩
    simpa [mul_im] using congrArg Complex.im (normPower_injective hτ).symm
  · rintro ⟨τ, rfl, _⟩
    exact ⟨(ideleClass_component_one _).mpr (ideleClassNormPower_on_normOne _),
      (ideleClassNormPower_unitary_iff _).mpr (by simp [mul_re])⟩

/-- The printed choice of the trivial character as a unitary base point:
it belongs to the same component as the given unitary character, which
is itself an imaginary norm twist with a unique frequency. -/
public theorem ideleClass_trivial_basePoint (χ : Ω) (hu : ∀ c : C, ‖χ c‖ = 1)
    (hχ : ∀ c : C₁, χ (c : C) = 1) :
    (1 : Ω) ∈ connectedComponent χ ∧
      ∃! τ : ℝ, χ = ideleClassNormPower ((τ : ℂ) * Complex.I) := by
  have hc := (ideleClass_component_one χ).mpr hχ
  refine ⟨?_, (ideleClass_component_one_unitary χ).mp ⟨hc, hu⟩⟩
  rw [← connectedComponent_eq hc]
  exact mem_connectedComponent

end Masullo
