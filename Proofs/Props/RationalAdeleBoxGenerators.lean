module

public import Theorems.RationalAdeleBoxFourier
import Lemmas.RationalAdeleFiniteStage

/-! # The translated generators of Example 2.1.3.1 over ℚ

A real Schwartz factor times local translated ball indicators, with the
standard integral ball at almost all places, is a single rational adelic box.
This is an algebraic realization and does not identify any LF topology.
-/

open NumberField IsDedekindDomain Set
open scoped SchwartzMap

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "F" v => HeightOneSpectrum.adicCompletion ℚ v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "eℝ" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

private noncomputable def centerStage (S : Finset V) (a : (v : V) → F v) :
    RationalAdeleFiniteStage S := (0, (fun v ↦ a v.val, fun _ ↦ 0))

private noncomputable def scaleStage (S : Finset V) (u : (v : V) → (F v)ˣ) :
    (RationalAdeleFiniteStage S)ˣ where
  val := (1, (fun v ↦ (u v.val : F v.val), fun _ ↦ 1))
  inv := (1, (fun v ↦ (↑((u v.val)⁻¹) : F v.val), fun _ ↦ 1))
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

/-- Given finitely many local centers and nonzero scales, the tensor with real
factor `b` and finite indicators of `aᵥ + uᵥ Oᵥ` is a rational adelic box.
Its adelic center has real coordinate zero, and its idelic scale has real
coordinate one, so the real Schwartz factor is unchanged. -/
public theorem exists_rationalAdeleBox_eq_localTensor (b : 𝓢(ℝ, ℂ)) (S : Finset V)
    (a : (v : V) → F v) (u : (v : V) → (F v)ˣ)
    (h : ∀ v ∉ S, a v = 0 ∧ u v = 1) :
    ∃ (center : A) (scale : J), rationalAdeleReal center = 0 ∧
      rationalAdeleReal (scale : A) = 1 ∧
      rationalAdeleBox b center scale =
        {x : A | ∀ v : V, ∃ t : O v, x.2 v = a v + (u v : F v) * (t : F v)}.indicator
          (fun x ↦ b (rationalAdeleReal x)) := by
  classical
  let emb := rationalAdeleFiniteStageEmbedding S
  let center := emb (centerStage S a)
  let scale := Units.map emb (scaleStage S u)
  have hcenter : rationalAdeleReal center = 0 := by
    rw [rationalAdeleReal_apply]
    exact rationalAdeleFiniteStageEmbedding_real S (centerStage S a)
  have hscale : rationalAdeleReal (scale : A) = 1 := by
    rw [rationalAdeleReal_apply]
    exact rationalAdeleFiniteStageEmbedding_real S (scaleStage S u).val
  have hscaleInv : rationalAdeleReal (↑(scale⁻¹) : A) = 1 := by
    rw [rationalAdeleReal_apply]
    exact rationalAdeleFiniteStageEmbedding_real S (scaleStage S u).inv
  refine ⟨center, scale, hcenter, hscale, ?_⟩
  have hc (v : V) : center.2 v = a v := by
    by_cases hv : v ∈ S
    · exact rationalAdeleFiniteStageEmbedding_finite_mem S _ v hv
    · rw [rationalAdeleFiniteStageEmbedding_finite_notMem S _ v hv, (h v hv).1]
      rfl
  have hu (v : V) : (↑(scale⁻¹) : A).2 v = (↑((u v)⁻¹) : F v) := by
    change (emb (↑((scaleStage S u)⁻¹))).2 v = _
    by_cases hv : v ∈ S
    · exact rationalAdeleFiniteStageEmbedding_finite_mem S _ v hv
    · rw [rationalAdeleFiniteStageEmbedding_finite_notMem S _ v hv, (h v hv).2, inv_one]
      rfl
  funext x
  let z : A := (↑(scale⁻¹) : A) * (x - center)
  have hreal : rationalAdeleReal z = rationalAdeleReal x := by
    rw [rationalAdeleReal_apply z]
    change eℝ ((↑(scale⁻¹) : A).1 Rat.infinitePlace *
      (x.1 Rat.infinitePlace - center.1 Rat.infinitePlace)) = _
    rw [map_mul, map_sub, ← rationalAdeleReal_apply, ← rationalAdeleReal_apply,
      ← rationalAdeleReal_apply, hcenter, hscaleInv, sub_zero, one_mul]
  have hfin : z ∈ rationalIntegralAdeles ↔
      ∀ v : V, ∃ t : O v, x.2 v = a v + (u v : F v) * (t : F v) := by
    change (∀ v : V, (↑(scale⁻¹) : A).2 v * (x.2 v - center.2 v) ∈ O v) ↔ _
    simp only [hu, hc]
    constructor
    · intro hx v
      refine ⟨⟨_, hx v⟩, ?_⟩
      change x.2 v = a v + (u v : F v) * ((↑((u v)⁻¹) : F v) * (x.2 v - a v))
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, add_sub_cancel]
    · intro hx v
      obtain ⟨t, ht⟩ := hx v
      rw [ht, add_sub_cancel_left, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]
      exact t.property
  change rationalAdeleUnramified b z = _
  by_cases hz : z ∈ rationalIntegralAdeles
  · rw [rationalAdeleUnramified, indicator_of_mem hz, indicator_of_mem (hfin.mp hz), hreal]
  · rw [rationalAdeleUnramified, indicator_of_notMem hz, indicator_of_notMem (mt hfin.mpr hz)]

end Masullo
