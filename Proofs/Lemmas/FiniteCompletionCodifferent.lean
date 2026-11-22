module

public import Lemmas.FiniteCompletionFractionBaseChange
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.BaseChange

/-! # The global codifferent in a finite completion

Masullo uses the local inverse different in Example A.3.1.10, (A.3.1.8),
PDF p. 558, and the local discriminant in (A.3.2.2), PDF p. 560. The comparison
with the global codifferent below is a separate argument. The source reading
is provisional (Markdown and numbered layout, not the rendered pages).
-/

open IsDedekindDomain NumberField Module
open scoped BigOperators nonZeroDivisors TensorProduct

namespace Masullo

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

local notation "V[" p "]" => {v : HeightOneSpectrum (𝓞 K) //
  HeightOneSpectrum.asIdeal v ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))}
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K (Subtype.val v)
local notation "F[" v "]" => HeightOneSpectrum.adicCompletion K (Subtype.val v)
local notation "IntTensor" => ℤ_[p] ⊗[ℤ] 𝓞 K
local notation "FracTensor" => ℚ_[p] ⊗[ℤ_[p]] IntTensor
local notation "RatTensor" => ℚ_[p] ⊗[ℚ] K
local notation "Codiff" => Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)

attribute [local instance] finiteCompletionOverPrimeAlgebra finiteCompletionOverPrimeFieldAlgebra

private noncomputable instance globalIntegerPushout : Algebra.IsPushout ℤ ℚ (𝓞 K) K :=
  (Algebra.isPushout_of_isLocalization (A := ℚ) ℤ⁰ (𝓞 K) K).symm

-- Cancel the intermediate base changes, then localize the global integers.
private noncomputable def fractionComparison : FracTensor ≃ₐ[ℚ_[p]] RatTensor :=
  (Algebra.TensorProduct.cancelBaseChange ℤ ℤ_[p] ℚ_[p] ℚ_[p] (𝓞 K)).trans
    ((Algebra.TensorProduct.cancelBaseChange ℤ ℚ ℚ_[p] ℚ_[p] (𝓞 K)).symm.trans
      (Algebra.TensorProduct.congr (.refl : ℚ_[p] ≃ₐ[ℚ_[p]] ℚ_[p])
        (Algebra.IsPushout.equiv ℤ ℚ (𝓞 K) K)))

private theorem fractionComparison_one_tmul (a : 𝓞 K) :
    fractionComparison p ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] ((1 : ℤ_[p]) ⊗ₜ[ℤ] a)) =
      (1 : ℚ_[p]) ⊗ₜ[ℚ] algebraMap (𝓞 K) K a := by
  simp [fractionComparison, Algebra.IsPushout.equiv_tmul]

private noncomputable def globalInFraction : K →+* FracTensor :=
  (fractionComparison p).symm.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[p])).toRingHom

private theorem globalInFraction_integer (a : 𝓞 K) :
    globalInFraction p (algebraMap (𝓞 K) K a) =
      (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
  apply (fractionComparison p).injective
  rw [fractionComparison_one_tmul]
  exact AlgEquiv.apply_symm_apply (fractionComparison p) _

-- The two maps agree on global integers, hence on their localization `K`.
private theorem fractionBaseChange_global (v : V[p]) (x : K) :
    finiteCompletionFractionBaseChange p (globalInFraction p x) v = algebraMap K F[v] x := by
  let f : K →+* F[v] := (Pi.evalRingHom (fun w : V[p] ↦ F[w]) v).comp
    ((finiteCompletionFractionBaseChange p).toRingHom.comp (globalInFraction p))
  suffices f = algebraMap K F[v] from DFunLike.congr_fun this x
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰)
  apply RingHom.ext
  intro a
  change finiteCompletionFractionBaseChange p (globalInFraction p (algebraMap (𝓞 K) K a)) v =
    algebraMap K F[v] (algebraMap (𝓞 K) K a)
  rw [globalInFraction_integer, finiteCompletionFractionBaseChange_tmul,
    finiteCompletionIntegralBaseChange_tmul, one_smul, one_smul]
  change (↑(algebraMap (𝓞 K) O[v] a) : F[v]) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rfl

section DualBasis

local notation "Idx" => Free.ChooseBasisIndex ℤ (𝓞 K)

private theorem fractionTrace_global (x : K) :
    Algebra.trace ℚ_[p] FracTensor (globalInFraction p x) =
      algebraMap ℚ ℚ_[p] (Algebra.trace ℚ K x) := by
  rw [← Algebra.trace_eq_of_algEquiv (fractionComparison p)]
  change Algebra.trace ℚ_[p] RatTensor ((fractionComparison p) ((fractionComparison p).symm
    ((1 : ℚ_[p]) ⊗ₜ[ℚ] x))) = _
  rw [AlgEquiv.apply_symm_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, ← Algebra.trace_apply]

private noncomputable def fractionDualBasis : Basis Idx ℚ_[p] FracTensor :=
  ((integralBasis K).traceDual.baseChange ℚ_[p]).map
    (fractionComparison p).symm.toLinearEquiv

private theorem fractionDualBasis_apply (i : Idx) :
    fractionDualBasis p i = globalInFraction p ((integralBasis K).traceDual i) := by
  simp only [fractionDualBasis, Basis.map_apply, Basis.baseChange_apply]
  rfl

-- The global trace-dual basis remains dual to the extended integral basis.
private theorem fractionDualBasis_repr (x : FracTensor) (i : Idx) :
    (fractionDualBasis p).repr x i = Algebra.trace ℚ_[p] FracTensor
      (x * globalInFraction p (integralBasis K i)) := by
  classical
  let f : FracTensor →ₗ[ℚ_[p]] ℚ_[p] :=
    (Finsupp.lapply i).comp (fractionDualBasis p).repr.toLinearMap
  let g : FracTensor →ₗ[ℚ_[p]] ℚ_[p] :=
    (Algebra.traceForm ℚ_[p] FracTensor).flip (globalInFraction p (integralBasis K i))
  suffices f = g from LinearMap.congr_fun this x
  apply (fractionDualBasis p).ext
  intro j
  change (fractionDualBasis p).repr (fractionDualBasis p j) i =
    Algebra.trace ℚ_[p] FracTensor (fractionDualBasis p j * globalInFraction p (integralBasis K i))
  rw [Basis.repr_self, fractionDualBasis_apply, ← map_mul, fractionTrace_global,
    Basis.trace_traceDual_mul]
  by_cases h : i = j <;> simp [h]

private theorem fractionTraceDual_iff_basis (x : FracTensor) :
    (∀ t : IntTensor, Algebra.trace ℚ_[p] FracTensor (x * ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t)) ∈
      (algebraMap ℤ_[p] ℚ_[p]).range) ↔
    (∀ i : Idx, (fractionDualBasis p).repr x i ∈ (algebraMap ℤ_[p] ℚ_[p]).range) := by
  let b := (RingOfIntegers.basis K).baseChange ℤ_[p]
  let f : IntTensor →ₗ[ℤ_[p]] ℚ_[p] :=
    (((Algebra.traceForm ℚ_[p] FracTensor) x).restrictScalars ℤ_[p]).comp
      (TensorProduct.mk ℤ_[p] ℚ_[p] IntTensor 1)
  have hb (i : Idx) : f (b i) = (fractionDualBasis p).repr x i := by
    rw [fractionDualBasis_repr, integralBasis_apply, globalInFraction_integer]
    simp only [f, b, Basis.baseChange_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      TensorProduct.mk_apply, Algebra.traceForm_apply]
  change (∀ t : IntTensor, f t ∈ (algebraMap ℤ_[p] ℚ_[p]).range) ↔ _
  constructor
  · intro h i
    simpa only [hb] using h (b i)
  · intro h t
    have hle : (⊤ : Submodule ℤ_[p] IntTensor) ≤ (1 : Submodule ℤ_[p] ℚ_[p]).comap f := by
      rw [← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.mem_one.mpr (hb i ▸ h i)
    exact Submodule.mem_one.mp (hle (Submodule.mem_top : t ∈ ⊤))

private theorem globalInFraction_traceDual {x : K} (hx : x ∈ Codiff) :
    ∀ t : IntTensor, Algebra.trace ℚ_[p] FracTensor
      (globalInFraction p x * ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t)) ∈ (algebraMap ℤ_[p] ℚ_[p]).range := by
  apply (fractionTraceDual_iff_basis p _).mpr
  intro i
  rw [fractionDualBasis_repr, ← map_mul, fractionTrace_global]
  have hi : integralBasis K i ∈ (1 : Submodule (𝓞 K) K) :=
    Submodule.mem_one.mpr ⟨RingOfIntegers.basis K i, (integralBasis_apply _ _).symm⟩
  obtain ⟨n, hn⟩ := Submodule.mem_traceDual.mp hx _ hi
  rw [← Algebra.traceForm_apply, ← hn, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ ℤ_[p] ℚ_[p]]
  exact ⟨_, rfl⟩

private theorem traceDualBasis_mem_globalCodiff (i : Idx) : (integralBasis K).traceDual i ∈ Codiff := by
  classical
  have hb : (1 : Submodule (𝓞 K) K).restrictScalars ℤ =
      Submodule.span ℤ (Set.range (integralBasis K)) := by
    ext x
    rw [Submodule.restrictScalars_mem, Submodule.mem_one]
    exact (mem_span_integralBasis (K := K)).symm
  change (integralBasis K).traceDual i ∈ (Codiff).restrictScalars ℤ
  rw [Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 K) K) (integralBasis K) hb]
  exact Submodule.subset_span ⟨i, rfl⟩

end DualBasis

section Projection

private noncomputable instance localIntegerAlgebra (v : V[p]) : Algebra ℤ_[p] F[v] :=
  Algebra.compHom F[v] (algebraMap ℤ_[p] ℚ_[p])

private instance localFieldScalarTower (v : V[p]) : IsScalarTower ℤ_[p] ℚ_[p] F[v] :=
  .of_algebraMap_eq fun _ ↦ rfl

private instance localIntegerScalarTower (v : V[p]) : IsScalarTower ℤ_[p] O[v] F[v] :=
  .of_algebraMap_eq fun r ↦ (finiteCompletionOverPrime_algebraMap_int p v r).symm

private theorem localDual_mem (v : V[p]) (x : F[v]) :
    x ∈ Submodule.traceDual ℤ_[p] ℚ_[p] (1 : Submodule O[v] F[v]) ↔
    ∀ y : O[v], Algebra.trace ℚ_[p] F[v] (x * algebraMap O[v] F[v] y) ∈
      (algebraMap ℤ_[p] ℚ_[p]).range := by
  rw [Submodule.mem_traceDual]
  constructor
  · intro h y
    exact h _ (Submodule.mem_one.mpr ⟨y, rfl⟩)
  · intro h z hz
    obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hz
    exact h y

private noncomputable def fractionCoordinate (v : V[p]) : FracTensor →ₗ[ℤ_[p]] F[v] :=
  (((Pi.evalAlgHom ℚ_[p] (fun w : V[p] ↦ F[w]) v).comp
    (finiteCompletionFractionBaseChange p).toAlgHom).toLinearMap).restrictScalars ℤ_[p]

/-- In the actual completion at a place over `p`, the `ℤ_[p]`-trace dual
of the local integer ring is the local-integer span of the image of the
number field's codifferent under the canonical completion map. -/
public theorem finiteCompletion_traceDual_iff_mem_span_globalCodifferent (v : V[p]) (x : F[v]) :
    (∀ y : O[v], Algebra.trace ℚ_[p] F[v] (x * algebraMap O[v] F[v] y) ∈
      (algebraMap ℤ_[p] ℚ_[p]).range) ↔
    x ∈ Submodule.span O[v] ((algebraMap K F[v]) '' (Codiff : Set K)) := by
  constructor
  · intro hx
    classical
    -- Lift just this place to the product trace dual; the other tests see zero.
    let t : (w : V[p]) → F[w] := Function.update 0 v x
    let z := (finiteCompletionFractionBaseChange p).symm t
    have hz (w : V[p]) : finiteCompletionFractionBaseChange p z w = t w :=
      congrFun ((finiteCompletionFractionBaseChange p).apply_symm_apply t) w
    have htest := (finiteCompletionFractionBaseChange_traceDual_iff p z).mpr (by
      intro w y
      rw [hz]
      by_cases hw : w = v
      · subst w
        simpa [t] using hx y
      · simp [t, Function.update_of_ne hw])
    let b := fractionDualBasis (K := K) p
    obtain ⟨c, hc⟩ := Classical.skolem.mp ((fractionTraceDual_iff_basis p z).mp htest)
    have hsum : (∑ i, c i • b i) = z := by
      rw [← b.sum_repr z]
      congr 1
      funext i
      rw [← hc i, algebraMap_smul]
    have hxz : fractionCoordinate p v z = x := by
      change finiteCompletionFractionBaseChange p z v = x
      simp [hz, t]
    rw [← hxz, ← hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul]
    change c i • finiteCompletionFractionBaseChange p (fractionDualBasis p i) v ∈ _
    -- Each projected basis vector is a canonical image of a global dual vector.
    rw [fractionDualBasis_apply, fractionBaseChange_global]
    let S := Submodule.span O[v] ((algebraMap K F[v]) '' (Codiff : Set K))
    exact (S.restrictScalars ℤ_[p]).smul_mem (c i) (Submodule.subset_span
      ⟨_, traceDualBasis_mem_globalCodiff i, rfl⟩)
  · intro hx
    -- The local dual is an `O[v]`-submodule, so test the generators of the span.
    apply (localDual_mem p v x).mp
    refine (Submodule.span_le.mpr ?_) hx
    rintro _ ⟨d, hd, rfl⟩
    apply (localDual_mem p v _).mpr
    have h := (finiteCompletionFractionBaseChange_traceDual_iff p _).mp
      (globalInFraction_traceDual p hd) v
    simpa only [fractionBaseChange_global] using h

end Projection

end Masullo
