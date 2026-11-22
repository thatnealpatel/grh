module

public import Theorems.IdeleFiniteStage
import Lemmas.FiniteLocalNormShell
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! # Coordinates and norm calculations for finite idele stages -/

open IsDedekindDomain NumberField
open scoped Classical RestrictedProduct

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "D" => AdeleRing (𝓞 K) K
local notation "F" v => HeightOneSpectrum.adicCompletion K v

/-- Evaluate the finite coordinate of an actual idele as a local unit. -/
@[expose] public noncomputable def ideleFiniteCoordinate (a : I) (v : V) : (F v)ˣ :=
  Units.map (M := D) { toFun := fun b ↦ b.2 v, map_one' := rfl, map_mul' := fun _ _ ↦ rfl } a

public theorem ideleFiniteCoordinate_val (a : I) (v : V) :
    (ideleFiniteCoordinate K a v : F v) = (a : D).2 v := rfl

public theorem ideleFiniteCoordinate_stage_mem (S : Finset V) (x : IdeleFiniteStage K S)
    (v : V) (hv : v ∈ S) : ideleFiniteCoordinate K (ideleFiniteStageEmbedding K S x) v = x.2.1 ⟨v, hv⟩ :=
  Units.ext (ideleFiniteStageEmbedding_finite_mem K S x v hv)

/-- Evaluate the tuple of Archimedean units of an actual idele. -/
public noncomputable def ideleInfiniteCoordinates (a : I) (v : InfinitePlace K) : v.Completionˣ :=
  Units.map (M := D) { toFun := fun b ↦ b.1 v, map_one' := rfl, map_mul' := fun _ _ ↦ rfl } a

public theorem ideleInfiniteCoordinates_stage (S : Finset V) (x : IdeleFiniteStage K S) :
    ideleInfiniteCoordinates K (ideleFiniteStageEmbedding K S x) = x.1 :=
  funext fun v ↦ Units.ext (ideleFiniteStageEmbedding_infinite K S x v)

public theorem ideleFiniteStage_norm_finite_notMem (S : Finset V) (x : IdeleFiniteStage K S)
    (v : V) (hv : v ∉ S) : ‖(ideleFiniteStageEmbedding K S x : AdeleRing (𝓞 K) K).2 v‖ = 1 := by
  rw [ideleFiniteStageEmbedding_finite_notMem K S x v hv]
  let u := x.2.2 ⟨v, hv⟩
  have hu : Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u ∈ finiteLocalUnitSet v := by
    rw [finiteLocalUnitSet_eq_range]
    exact ⟨u, rfl⟩
  exact hu

public theorem prod_norm_cpow {ι : Type*} (S : Finset ι) (n : ι → ℝ)
    (hn : ∀ v, 0 ≤ n v) (s : ℂ) :
    ((∏ v ∈ S, n v : ℝ) : ℂ) ^ s = ∏ v ∈ S, ((n v : ℂ) ^ s) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert v T hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hn v) (Finset.prod_nonneg fun w _ ↦ hn w), ih]

end Masullo
