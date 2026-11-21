module

public import Theorems.RationalAdeleStageFourier
public import Theorems.RationalAdeleLFDilationDeriv
public import Lemmas.SchwartzWeightedDilation

/-! # Forward Fourier and weighted inverse dilation on the rational LF space

A pointwise formula on the assembled functions makes each operator
independent of the containing stage. Continuity then follows stagewise.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

noncomputable section

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "L" => rationalAdeleFactorialLevel
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)
local notation "assemble" => rationalAdeleLFAssembly
local notation:max "val[" f "]" => Subtype.val (RationalAdeleSchwartzLF.toUnion f)

private def stageNumber (f : E) : ℕ :=
  (mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property).choose

private theorem stageNumber_assembly (f : E) :
    assemble (stageNumber f) (rationalAdeleLFRead (stageNumber f) f) = f :=
  rationalAdeleLFAssembly_read _ f (mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property).choose_spec

variable (T : ∀ (n : ℕ), (Profiles n) →L[ℂ] (Profiles n)) (H : (A → ℂ) → (A → ℂ))
  (h : ∀ n b, val[assemble n (T n b)] = H (val[assemble n b]))

private def stageOperatorValue (f : E) : E :=
  let n := stageNumber f
  assemble n (T n (rationalAdeleLFRead n f))

include h in
private theorem stageOperatorValue_eq (f : E) : val[stageOperatorValue T f] = H (val[f]) := by
  change val[assemble (stageNumber f) (T _ (rationalAdeleLFRead _ f))] = _
  rw [h, stageNumber_assembly]

include h in
private theorem stageOperatorValue_assembly (n : ℕ) (b : Profiles n) :
    stageOperatorValue T (assemble n b) = assemble n (T n b) :=
  RationalAdeleSchwartzLF.ext ((stageOperatorValue_eq T H h _).trans (h n b).symm)

private def stageOperatorLinear : E →ₗ[ℂ] E where
  toFun := stageOperatorValue T
  map_add' f g := by
    obtain ⟨m, hm⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
    obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp g.toUnion.property
    let k := max m n
    have hf := rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_left m n)) hm
    have hg := rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_right m n)) hn
    change stageOperatorValue T (f + g) = stageOperatorValue T f + stageOperatorValue T g
    let b := rationalAdeleLFRead k f
    let c := rationalAdeleLFRead k g
    calc
      stageOperatorValue T (f + g) = stageOperatorValue T (assemble k (b + c)) := by
        rw [map_add, rationalAdeleLFAssembly_read k f hf, rationalAdeleLFAssembly_read k g hg]
      _ = stageOperatorValue T f + stageOperatorValue T g := by
        have hb : assemble k b = f := rationalAdeleLFAssembly_read k f hf
        have hc : assemble k c = g := rationalAdeleLFAssembly_read k g hg
        rw [stageOperatorValue_assembly T H h k (b + c), ← hb, ← hc,
          stageOperatorValue_assembly T H h k b, stageOperatorValue_assembly T H h k c,
          map_add, map_add]
  map_smul' c f := by
    change stageOperatorValue T (c • f) = c • stageOperatorValue T f
    let n := stageNumber f
    let b := rationalAdeleLFRead n f
    have hb : assemble n b = f := stageNumber_assembly f
    calc
      stageOperatorValue T (c • f) = stageOperatorValue T (assemble n (c • b)) := by
        rw [map_smul, hb]
      _ = c • stageOperatorValue T f := by
        rw [stageOperatorValue_assembly T H h n (c • b), ← hb,
          stageOperatorValue_assembly T H h n b, map_smul, map_smul]

private def stageOperator : E →L[ℂ] E where
  toLinearMap := stageOperatorLinear T H h
  cont := (rationalAdeleLF_continuous_iff _).mpr fun n ↦ by
    have he : (stageOperatorLinear T H h).comp (rationalAdeleLFAssemblyLinear n) =
        ((assemble n).comp (T n)).toLinearMap := by
      apply LinearMap.ext
      intro b
      change stageOperatorValue T (rationalAdeleLFAssemblyLinear n b) = assemble n (T n b)
      have hb : rationalAdeleLFAssemblyLinear n b = assemble n b :=
        RationalAdeleSchwartzLF.ext (congrArg Subtype.val
          ((rationalAdeleLFAssemblyLinear_toUnion n b).trans (rationalAdeleLFAssembly_toUnion n b).symm))
      rw [hb, stageOperatorValue_assembly T H h]
    rw [he]
    exact ((assemble n).comp (T n)).continuous

private theorem stageOperator_assembly (n : ℕ) (b : Profiles n) :
    stageOperator T H h (assemble n b) = assemble n (T n b) :=
  stageOperatorValue_assembly T H h n b

private theorem stageOperator_eq (f : E) : val[stageOperator T H h f] = H (val[f]) :=
  stageOperatorValue_eq T H h f

set_option linter.concreteInstances false

section Fourier

variable [MeasurableSpace A] [BorelSpace A]

/-- The normalized forward adelic Fourier transform on the rational LF space. -/
public def rationalAdeleLFFourier : E →L[ℂ] E :=
  stageOperator (fun n ↦ rationalAdeleStageFourier (L n)) rationalAdeleFourier
    rationalAdeleLFAssembly_fourier

public theorem rationalAdeleLFFourier_eq (f : E) :
    val[rationalAdeleLFFourier f] = rationalAdeleFourier (val[f]) :=
  stageOperator_eq _ _ _ f

public theorem rationalAdeleLFFourier_assembly (n : ℕ) (b : Profiles n) :
    rationalAdeleLFFourier (assemble n b) = assemble n (rationalAdeleStageFourier (L n) b) :=
  stageOperator_assembly _ _ _ n b

end Fourier

local notation "U" => schwartzWeightedInverseDilation

private def stageDilation (s : ℝ) (n : ℕ) : (Profiles n) →L[ℂ] (Profiles n) :=
  ContinuousLinearMap.pi fun j ↦ (U s).comp (ContinuousLinearMap.proj j)

private theorem assembly_stageDilation (s : ℝ) (n : ℕ) (b : Profiles n) :
    val[assemble n (stageDilation s n b)] = fun y ↦ Real.exp (-s) •
      (val[assemble n b]) ((rationalIdeleLogSection (Multiplicative.ofAdd (-s)) : A) * y) := by
  let hL := rationalAdeleFactorialLevel_pos n
  have hval (c : Profiles n) : val[assemble n c] =
      ((rationalAdeleStageCoordinates hL).symm c).val := by
    rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val]
  funext y
  simp only [hval, rationalIdeleLogSection_mul_adele]
  by_cases hy : y ∈ rationalAdeleStageSupport (L n)
  · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hL y).mp hy
    have hcell : rationalAdeleAt (Real.exp (-s) * rationalAdeleReal y) y.2 ∈
        rationalAdeleStageCell (L n) j := by
      rw [mem_rationalAdeleStageCell_iff hL, rationalAdeleAt_finite]
      exact (mem_rationalAdeleStageCell_iff hL j y).mp hj
    rw [← rationalAdeleStageCoordinates_eq_on_cell hL _ hj, LinearEquiv.apply_symm_apply,
      ← rationalAdeleStageCoordinates_eq_on_cell hL _ hcell, LinearEquiv.apply_symm_apply,
      rationalAdeleReal_at]
    exact schwartzWeightedInverseDilation_apply s (b j) (rationalAdeleReal y)
  · have hout : rationalAdeleAt (Real.exp (-s) * rationalAdeleReal y) y.2 ∉
        rationalAdeleStageSupport (L n) := by
      change ((L n : FiniteAdeleRing (𝓞 ℚ) ℚ) * (rationalAdeleAt _ y.2).2) ∉
        rationalFiniteIntegralAdeles
      rw [rationalAdeleAt_finite]
      exact hy
    rw [((rationalAdeleStageCoordinates hL).symm _).property.1 _ hy,
      ((rationalAdeleStageCoordinates hL).symm b).property.1 _ hout, smul_zero]

/-- Weighted inverse dilation in the real log parameter, continuous and
complex-linear at each fixed parameter. -/
public def rationalAdeleLFWeightedInverseDilation (s : ℝ) : E →L[ℂ] E :=
  stageOperator (stageDilation s) (fun f y ↦ Real.exp (-s) •
    f ((rationalIdeleLogSection (Multiplicative.ofAdd (-s)) : A) * y)) (assembly_stageDilation s)

public theorem rationalAdeleLFWeightedInverseDilation_apply (s : ℝ) (f : E) (y : A) :
    val[rationalAdeleLFWeightedInverseDilation s f] y = Real.exp (-s) •
      (val[f]) ((rationalIdeleLogSection (Multiplicative.ofAdd (-s)) : A) * y) :=
  congrFun (stageOperator_eq _ _ _ f) y

public theorem rationalAdeleLFWeightedInverseDilation_assembly (s : ℝ) (n : ℕ) (b : Profiles n) :
    rationalAdeleLFWeightedInverseDilation s (assemble n b) = assemble n (fun j ↦ U s (b j)) :=
  stageOperator_assembly _ _ _ n b

end
end Masullo
