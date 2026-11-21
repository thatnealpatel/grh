module

public import Lemmas.RationalIdeleReal
public import Mathlib.Topology.Algebra.Group.Units

/-! # The finite-unit window for rational ideles -/

open NumberField IsDedekindDomain
open scoped RestrictedProduct

namespace Masullo

private abbrev Ideles := IdeleGroup (𝓞 ℚ) ℚ

private def integralStage : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  {b | ∀ v, b v ∈ v.adicCompletionIntegers ℚ}

private theorem isOpen_integralStage : IsOpen integralStage :=
  RestrictedProduct.isOpen_forall_mem (fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion ℚ))

/-- The window with positive real coordinate and integral finite coordinates for
both the idele and its inverse. -/
@[expose]
public def rationalIdeleUnitWindow : Set (IdeleGroup (𝓞 ℚ) ℚ) :=
  {a | 0 < rationalIdeleReal a ∧
    (∀ v, (a : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ) ∧
    (∀ v, (↑(a⁻¹) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ)}

public theorem isOpen_rationalIdeleUnitWindow : IsOpen rationalIdeleUnitWindow := by
  have hfin : Continuous (fun a : IdeleGroup (𝓞 ℚ) ℚ ↦ (a : AdeleRing (𝓞 ℚ) ℚ).2) :=
    continuous_snd.comp Units.continuous_val
  have hreal : Continuous rationalIdeleReal :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      ((continuous_apply Rat.infinitePlace).comp (continuous_fst.comp Units.continuous_val))
  exact (isOpen_lt continuous_const hreal).inter
    ((isOpen_integralStage.preimage hfin).inter (isOpen_integralStage.preimage (hfin.comp continuous_inv)))

public theorem rationalIdeleReal_one : rationalIdeleReal (1 : IdeleGroup (𝓞 ℚ) ℚ) = 1 := by
  unfold rationalIdeleReal
  exact map_one _

private theorem real_mul (a b : Ideles) :
    rationalIdeleReal (a * b) = rationalIdeleReal a * rationalIdeleReal b :=
  map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _

public theorem mul_mem_rationalIdeleUnitWindow {a b : IdeleGroup (𝓞 ℚ) ℚ}
    (ha : a ∈ rationalIdeleUnitWindow) (hb : b ∈ rationalIdeleUnitWindow) : a * b ∈ rationalIdeleUnitWindow := by
  refine ⟨?_, ?_, ?_⟩
  · rw [real_mul]
    exact mul_pos ha.1 hb.1
  · intro v
    exact (v.adicCompletionIntegers ℚ).mul_mem _ _ (ha.2.1 v) (hb.2.1 v)
  · intro v
    rw [mul_inv_rev]
    exact (v.adicCompletionIntegers ℚ).mul_mem _ _ (hb.2.2 v) (ha.2.2 v)

public theorem inv_mem_rationalIdeleUnitWindow {a : IdeleGroup (𝓞 ℚ) ℚ}
    (ha : a ∈ rationalIdeleUnitWindow) : a⁻¹ ∈ rationalIdeleUnitWindow := by
  refine ⟨?_, ha.2.2, inv_inv a ▸ ha.2.1⟩
  have h := (real_mul a a⁻¹).symm
  rw [mul_inv_cancel, rationalIdeleReal_one] at h
  exact pos_of_mul_pos_right (h.symm ▸ (zero_lt_one : (0 : ℝ) < 1)) ha.1.le

public theorem mem_rationalIdeleUnitWindow_of_finiteValuation_eq_one {a : IdeleGroup (𝓞 ℚ) ℚ}
    (hreal : 0 < rationalIdeleReal a) (hfin : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1) : a ∈ rationalIdeleUnitWindow := by
  refine ⟨hreal, fun v ↦ (hfin v).le, fun v ↦ ?_⟩
  have h := congrArg (fun b : AdeleRing (𝓞 ℚ) ℚ ↦ Valued.v (b.2 v)) (Units.val_inv a)
  change Valued.v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v * (↑a⁻¹ : AdeleRing (𝓞 ℚ) ℚ).2 v) =
    Valued.v (1 : v.adicCompletion ℚ) at h
  rw [map_mul, hfin, one_mul, map_one] at h
  exact h.le

public theorem one_mem_rationalIdeleUnitWindow :
    (1 : IdeleGroup (𝓞 ℚ) ℚ) ∈ rationalIdeleUnitWindow := by
  refine ⟨rationalIdeleReal_one.symm ▸ zero_lt_one, ?_, ?_⟩
  · intro v
    exact (v.adicCompletionIntegers ℚ).one_mem
  · rw [inv_one]
    intro v
    exact (v.adicCompletionIntegers ℚ).one_mem

public theorem finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow {a : IdeleGroup (𝓞 ℚ) ℚ}
    (ha : a ∈ rationalIdeleUnitWindow) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1 := by
  let x := (a : AdeleRing (𝓞 ℚ) ℚ).2 v
  let y := (↑(a⁻¹) : AdeleRing (𝓞 ℚ) ℚ).2 v
  have hx : Valued.v x ≤ 1 := ha.2.1 v
  have hy : Valued.v y ≤ 1 := ha.2.2 v
  have hxy : x * y = 1 := congrArg (fun b : AdeleRing (𝓞 ℚ) ℚ ↦ b.2 v) (Units.val_inv a)
  refine le_antisymm hx ?_
  calc
    1 = Valued.v x * Valued.v y := by rw [← map_mul, hxy, map_one]
    _ ≤ Valued.v x * 1 := mul_le_mul_of_nonneg_left hy zero_le
    _ = Valued.v x := mul_one _

/-- A principal idele in the positive finite-unit window is the identity. -/
public theorem eq_one_of_mem_rationalIdeleUnitWindow_of_principal {a : IdeleGroup (𝓞 ℚ) ℚ}
    (ha : a ∈ rationalIdeleUnitWindow) (hp : a ∈ IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) :
    a = 1 := by
  obtain ⟨r, rfl⟩ := hp
  have hnorm : ideleNorm (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r) = 1 := by
    rw [ideleNorm_apply]
    exact AdeleRing.norm_algebraMap_eq_one_of_ne_zero r.ne_zero
  have hfin := finiteValuation_eq_one_of_mem_rationalIdeleUnitWindow ha
  have habs := (ideleNorm_eq_abs_rationalIdeleReal _ hfin).symm.trans hnorm
  have hpos : 0 < rationalIdeleReal (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r) := ha.1
  rw [abs_of_pos hpos] at habs
  have hreal : ((r : ℚ) : ℝ) = 1 := by
    rw [← mul_one (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ r), rationalIdeleReal_principal_mul]
      at habs
    rwa [rationalIdeleReal_one, mul_one] at habs
  have hr : r = 1 := Units.ext (Rat.cast_injective (by
    simpa only [Units.val_one, Rat.cast_one] using hreal))
  simp [hr]

/-- The rational ideles are Hausdorff in the units topology. The adele ring is
Hausdorff as a product of the infinite and finite adele rings. -/
public theorem t2Space_rationalIdeleGroup : T2Space (IdeleGroup (𝓞 ℚ) ℚ) := by
  let : T2Space (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    show T2Space (Πʳ v : HeightOneSpectrum (𝓞 ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ])
      from inferInstance
  let : T2Space (InfiniteAdeleRing ℚ) :=
    show T2Space ((v : InfinitePlace ℚ) → v.Completion) from inferInstance
  let : T2Space (AdeleRing (𝓞 ℚ) ℚ) :=
    show T2Space (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) from inferInstance
  infer_instance

end Masullo
