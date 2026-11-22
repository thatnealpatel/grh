module

public import Lemmas.FinitePlaceSupport
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

import Lemmas.ArchimedeanLogRadius

/-!
# Single-place sections of the idelic norm

Masullo's Definition A.2.2.5, (A.2.2.10), PDF p. 547, inserts the
positive root of the radius into a chosen Archimedean place. In
logarithmic coordinates the root is `exp (x / v.mult)`. Lemma A.2.2.6
computes its idelic norm using the first power at a real place and the
square at a complex place. The section descends to the actual class group
as in Lemma A.1.3.4(3), (A.1.3.6), p. 542. This does not identify the
norm-one Haar measure or compute its volume.
-/

open NumberField IsDedekindDomain
open scoped Classical

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : InfinitePlace K)

private noncomputable def logSectionValue : Multiplicative ℝ →* AdeleRing (𝓞 K) K :=
  (AdeleRing.ofCompletion (𝓞 K) K v).comp (completionLogRadius v)

private theorem continuous_logSectionValue : Continuous (logSectionValue v) := by
  change Continuous (fun x : Multiplicative ℝ ↦ (Pi.mulSingle v (completionLogRadius v x),
    (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)))
  exact ((continuous_mulSingle v).comp (continuous_completionLogRadius v)).prodMk continuous_const

/-- The homomorphic single-place section in log coordinates, on actual ideles. -/
public noncomputable def ideleLogSection : Multiplicative ℝ →ₜ* IdeleGroup (𝓞 K) K where
  toMonoidHom := (logSectionValue v).toHomUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_logSectionValue v, (continuous_logSectionValue v).comp continuous_inv⟩

/-- All infinite coordinates are one except for the specified positive real radius at `v`. -/
public theorem ideleLogSection_infinite (x : Multiplicative ℝ) (w : InfinitePlace K) :
    InfinitePlace.Completion.extensionEmbedding w
        ((ideleLogSection v x : AdeleRing (𝓞 K) K).1 w) =
      if w = v then (Real.exp (x.toAdd / (v.mult : ℝ)) : ℂ) else 1 := by
  change InfinitePlace.Completion.extensionEmbedding w (Pi.mulSingle v (completionLogRadius v x) w) = _
  by_cases h : w = v
  · subst w
    rw [Pi.mulSingle_eq_same, ite_eq_left rfl, extensionEmbedding_completionLogRadius]
  · rw [Pi.mulSingle_eq_of_ne h, ite_eq_right h, map_one]

public theorem ideleLogSection_finite (x : Multiplicative ℝ) (w : HeightOneSpectrum (𝓞 K)) :
    (ideleLogSection v x : AdeleRing (𝓞 K) K).2 w = 1 := by
  unfold ideleLogSection logSectionValue
  rfl

/-- The normalized local power at `v` cancels the root in the section. -/
public theorem ideleNorm_ideleLogSection (x : Multiplicative ℝ) :
    ideleNorm (ideleLogSection v x) = Real.exp x.toAdd := by
  rw [ideleNorm_apply, AdeleRing.norm_apply_of_isUnit (ideleLogSection v x).isUnit]
  change (∏ w : InfinitePlace K, ‖(ideleLogSection v x : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 K), ‖(ideleLogSection v x : AdeleRing (𝓞 K) K).2 w‖) = _
  simp only [ideleLogSection_finite, norm_one, finprod_one, mul_one]
  -- Only the chosen Archimedean place contributes to the norm.
  rw [Finset.prod_eq_single v]
  · rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
      ideleLogSection_infinite, ite_eq_left rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr v.mult_ne_zero)]
  · intro w _ hw
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
      ideleLogSection_infinite, ite_eq_right hw, norm_one, one_pow]
  · simp

/-- Compose the section with the quotient by the principal ideles. -/
public noncomputable def ideleClassLogSection : Multiplicative ℝ →ₜ* IdeleClassGroup (𝓞 K) K where
  toMonoidHom := (QuotientGroup.mk' _).comp (ideleLogSection v).toMonoidHom
  continuous_toFun := QuotientGroup.continuous_mk.comp (map_continuous (ideleLogSection v))

public theorem ideleClassLogSection_apply (x : Multiplicative ℝ) :
    ideleClassLogSection v x = QuotientGroup.mk (ideleLogSection v x) := by
  unfold ideleClassLogSection
  rfl

public theorem ideleClassNorm_logSection (x : Multiplicative ℝ) :
    ideleClassNorm (ideleClassLogSection v x) = Real.exp x.toAdd := by
  rw [ideleClassLogSection_apply, ideleClassNorm_mk, ideleNorm_ideleLogSection]

end Masullo
