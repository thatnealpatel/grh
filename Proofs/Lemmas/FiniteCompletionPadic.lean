module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # The base p-adic field of a finite number-field completion

The discriminant in (A.3.2.2), p. 560, uses the integer ring of the
actual completion at the place and the base `ℤ_[p]`. We construct the
compatible field and integer maps by extending the rational embedding.
This supplies their algebraic and topological interface, not the local
discriminant calculation. -/

open IsDedekindDomain HeightOneSpectrum NumberField UniformSpace
open scoped WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The rational prime below `v`. -/
public noncomputable def finiteCompletionBasePrime : Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv (v.under ℤ)

omit [NumberField K] in
/-- The base prime is the natural generator of the contracted prime in `ℤ`. -/
public theorem finiteCompletionBasePrime_val :
    (finiteCompletionBasePrime v : ℕ) = Rat.HeightOneSpectrum.natGenerator (v.under ℤ) := by
  unfold finiteCompletionBasePrime
  rfl

local notation "u" => v.under ℤ
local notation "Kv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K
local notation "p" => finiteCompletionBasePrime v
public scoped instance finiteCompletionBasePrime_isPrime : Fact (p : ℕ).Prime := ⟨(p).property⟩

omit [NumberField K] in
private theorem liesOver_under : v.asIdeal.LiesOver (v.under ℤ).asIdeal :=
  Ideal.over_under _

private theorem withValMap_uniformContinuous :
    UniformContinuous (algebraMap (WithVal ((u).valuation ℚ)) (WithVal (v.valuation K))) := by
  let _ := liesOver_under v
  exact HeightOneSpectrum.uniformContinuous_algebraMap_liesOver ℚ K u v

private noncomputable def adicBaseMap : (u).adicCompletion ℚ →+* Kv :=
  ((adicCompletion.equiv K v).symm.toRingHom.comp
    (Completion.mapRingHom _ (withValMap_uniformContinuous v).continuous)).comp
    (adicCompletion.equiv ℚ u).toRingHom

private theorem continuous_adicBaseMap : Continuous (adicBaseMap v) :=
  (adicCompletion.continuous_ofCompletion K v).comp <|
    Completion.continuous_map.comp
      (adicCompletion.continuous_toCompletion ℚ u)

private theorem adicBaseMap_algebraMap (x : ℚ) :
    adicBaseMap v (algebraMap ℚ ((u).adicCompletion ℚ) x) = algebraMap ℚ Kv x := by
  apply adicCompletion.ext
  refine (Completion.mapRingHom_coe (withValMap_uniformContinuous v).continuous
    ((WithVal.equiv ((u).valuation ℚ)).symm x)).trans ?_
  rw [algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def]
  rfl

private theorem adicBaseMap_mem_integers_iff (x : (u).adicCompletion ℚ) :
    adicBaseMap v x ∈ Ov ↔ x ∈ (u).adicCompletionIntegers ℚ := by
  have hK : IsClopen (Ov : Set Kv) := Valued.isClopen_valuationSubring Kv
  have hQ : IsClopen ((u).adicCompletionIntegers ℚ : Set ((u).adicCompletion ℚ)) :=
    Valued.isClopen_valuationSubring ((u).adicCompletion ℚ)
  let A := (adicBaseMap v) ⁻¹' (Ov : Set Kv)
  let B := ((u).adicCompletionIntegers ℚ : Set ((u).adicCompletion ℚ))
  have hA : IsClopen A := hK.preimage (continuous_adicBaseMap v)
  refine ((u).denseRange_algebraMap ℚ).induction_on x ?_ ?_
  · change IsClosed {x | x ∈ A ↔ x ∈ B}
    have heq : {x | x ∈ A ↔ x ∈ B} = A ∩ B ∪ (Aᶜ ∩ Bᶜ) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    rw [heq]
    exact (hA.isClosed.inter hQ.isClosed).union (hA.isOpen.isClosed_compl.inter
      hQ.isOpen.isClosed_compl)
  · intro y
    rw [adicBaseMap_algebraMap]
    change Valued.v (algebraMap ℚ Kv y) ≤ 1 ↔
      Valued.v (algebraMap ℚ ((u).adicCompletion ℚ) y) ≤ 1
    simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    change Valued.v (↑(algebraMap ℚ K y) : Kv) ≤ 1 ↔
      Valued.v (↑((WithVal.equiv ((u).valuation ℚ)).symm y) : (u).adicCompletion ℚ) ≤ 1
    rw [adicCompletion.valued_coe]
    have h := adicCompletion.valued_coe ℚ u y
    change Valued.v (↑((WithVal.equiv ((u).valuation ℚ)).symm y) : (u).adicCompletion ℚ) = _ at h
    rw [h]
    let _ := liesOver_under v
    rw [← (u).valuation_liesOver K v]
    exact (pow_le_one_iff_of_nonneg zero_le (ne_of_gt
      (Ideal.ramificationIdx_pos_of_isDedekindDomain' v.asIdeal (u).ne_bot)))

/-- The embedding of the base `ℚ_[p]` into the actual completion at `v`. -/
public noncomputable def finiteCompletionPadicMap : ℚ_[p] →+* Kv :=
  (adicBaseMap v).comp (Rat.HeightOneSpectrum.adicCompletion.padicEquiv u).symm.toRingHom

public theorem continuous_finiteCompletionPadicMap : Continuous (finiteCompletionPadicMap v) :=
  (continuous_adicBaseMap v).comp (Rat.HeightOneSpectrum.adicCompletion.padicEquiv u).symm.continuous

@[simp]
public theorem finiteCompletionPadicMap_algebraMap (x : ℚ) :
    finiteCompletionPadicMap v (algebraMap ℚ ℚ_[p] x) = algebraMap ℚ Kv x := by
  change adicBaseMap v ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv u).symm
    (algebraMap ℚ ℚ_[p] x)) = _
  exact (congrArg (adicBaseMap v)
    ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv u).symm.toAlgEquiv.commutes x)).trans
      (adicBaseMap_algebraMap v x)

/-- The base embedding preserves and reflects integrality. -/
public theorem finiteCompletionPadicMap_mem_integers_iff (x : ℚ_[p]) :
    finiteCompletionPadicMap v x ∈ Ov ↔ ‖x‖ ≤ 1 := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv u
  change adicBaseMap v (e.symm x) ∈ Ov ↔ ‖x‖ ≤ 1
  rw [adicBaseMap_mem_integers_iff]
  change e.symm x ∈ (u).adicCompletionIntegers ℚ ↔ x ∈ PadicInt.subring p
  constructor
  · intro hx
    have h : e (e.symm x) ∈ PadicInt.subring p :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn u).mapsTo hx
    exact e.apply_symm_apply x ▸ h
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn u).surjOn hx
    exact e.symm_apply_eq.mpr hyx.symm ▸ hy

/-- The restriction of the base field embedding to the respective integer rings. -/
@[expose] public noncomputable def finiteCompletionPadicIntMap : ℤ_[p] →+* Ov :=
  ((finiteCompletionPadicMap v).comp (PadicInt.subring p).subtype).codRestrict (Ov).toSubring
    fun x ↦ (finiteCompletionPadicMap_mem_integers_iff v x).2 (PadicInt.norm_le_one x)

@[simp]
public theorem coe_finiteCompletionPadicIntMap (x : ℤ_[p]) :
    (finiteCompletionPadicIntMap v x : Kv) = finiteCompletionPadicMap v (x : ℚ_[p]) := rfl

public theorem continuous_finiteCompletionPadicIntMap :
    Continuous (finiteCompletionPadicIntMap v) :=
  ((continuous_finiteCompletionPadicMap v).comp continuous_subtype_val).subtype_mk _

/-- The local field as an algebra over its actual base `ℚ_[p]`. -/
public noncomputable scoped instance finiteCompletionPadicAlgebra : Algebra ℚ_[p] Kv :=
  (finiteCompletionPadicMap v).toAlgebra

public scoped instance finiteCompletionRatPadicTower : IsScalarTower ℚ ℚ_[p] Kv :=
  .of_algebraMap_eq fun x ↦ (finiteCompletionPadicMap_algebraMap v x).symm

/-- The integer ring as an algebra over the base integers `ℤ_[p]`. -/
public noncomputable scoped instance finiteCompletionPadicIntAlgebra : Algebra ℤ_[p] Ov :=
  (finiteCompletionPadicIntMap v).toAlgebra

public noncomputable scoped instance finiteCompletionPadicIntFieldAlgebra : Algebra ℤ_[p] Kv :=
  ((finiteCompletionPadicMap v).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

public scoped instance finiteCompletionPadicIntPadicTower : IsScalarTower ℤ_[p] ℚ_[p] Kv :=
  .of_algebraMap_eq fun _ ↦ rfl

public scoped instance finiteCompletionPadicIntIntegersTower : IsScalarTower ℤ_[p] Ov Kv :=
  .of_algebraMap_eq fun x ↦ (coe_finiteCompletionPadicIntMap v x).symm

public scoped instance finiteCompletionPadicContinuousSMul : ContinuousSMul ℚ_[p] Kv :=
  ⟨by
    simp only [Algebra.smul_def]
    exact ((continuous_finiteCompletionPadicMap v).comp continuous_fst).mul continuous_snd⟩

open scoped TensorProduct in
/-- The `p`-adic span of the image of `K` is finite-dimensional and closed.
Since it contains a dense set, it is the whole completion. -/
public theorem finiteCompletion_moduleFinite : Module.Finite ℚ_[p] Kv := by
  let Φ : ℚ_[p] ⊗[ℚ] K →ₗ[ℚ_[p]] Kv := Algebra.TensorProduct.lift
    (Algebra.algHom ℚ_[p] ℚ_[p] Kv) (Algebra.algHom ℚ K Kv) (fun _ _ ↦ mul_comm ..) |>.toLinearMap
  have hdense : DenseRange Φ := by
    apply (v.denseRange_algebraMap K).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [Φ, Algebra.algHom]⟩
  apply Module.Finite.of_surjective Φ
  rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.isClosed_of_finiteDimensional.closure_eq]
  exact hdense.closure_range

end Masullo
