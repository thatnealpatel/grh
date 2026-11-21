module

public import Props.RationalAdeleSchwartzLF
public import Theorems.RationalIdeleLogSection
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Stagewise real dilation on rational adelic Schwartz functions

The real dilation derivative changes only the profile on each finite cell.
Its pointwise characterization makes the assembled linear map independent
of the containing stage.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "L" => rationalAdeleFactorialLevel
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)

/-- The real Euler operator on each profile of a factorial stage. -/
public noncomputable def rationalAdeleStageEuler (n : ℕ) : (Profiles n) →L[ℂ] (Profiles n) :=
  ContinuousLinearMap.pi fun j ↦
    ((SchwartzMap.smulLeftCLM ℂ Complex.ofReal).comp (SchwartzMap.derivCLM ℂ ℂ)).comp
      (ContinuousLinearMap.proj j)

public theorem rationalAdeleStageEuler_apply (n : ℕ) (b : Profiles n) (j : Fin ((L n) ^ 2))
    (u : ℝ) : rationalAdeleStageEuler n b j u = (u : ℂ) * deriv (b j) u := by
  change SchwartzMap.smulLeftCLM ℂ Complex.ofReal (SchwartzMap.derivCLM ℂ ℂ (b j)) u = _
  rw [SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal,
    SchwartzMap.derivCLM_apply, smul_eq_mul]

private noncomputable def orbit (f : E) (x : A) (t : ℝ) : ℂ :=
  f.toUnion.val (rationalAdeleAt (t * rationalAdeleReal x) x.2)

private theorem hasDerivAt_orbit (f : E) (x : A) :
    HasDerivAt (orbit f x)
      ((rationalAdeleReal x : ℂ) *
        deriv (fun u ↦ f.toUnion.val (rationalAdeleAt u x.2)) (rationalAdeleReal x)) 1 := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
  obtain ⟨b, hb⟩ := hn.2.2 x.2
  have he : (fun u ↦ f.toUnion.val (rationalAdeleAt u x.2)) = (b : ℝ → ℂ) :=
    funext fun u ↦ (hb u).symm
  have h := (b.hasDerivAt (rationalAdeleReal x)).scomp_of_eq 1
    ((hasDerivAt_id' 1).mul_const (rationalAdeleReal x)) (one_mul _).symm
  have hfun : orbit f x = fun t ↦ b (t * rationalAdeleReal x) := by
    funext t
    exact congrFun he _
  simpa only [hfun, he, Function.comp_def, one_mul, Complex.real_smul] using h

private theorem assembly_hasDerivAt (n : ℕ) (b : Profiles n) (x : A) :
    HasDerivAt (orbit (rationalAdeleLFAssembly n b) x)
      ((rationalAdeleLFAssembly n (rationalAdeleStageEuler n b)).toUnion.val x) 1 := by
  let hL := rationalAdeleFactorialLevel_pos n
  have hval (c : Profiles n) : (rationalAdeleLFAssembly n c).toUnion.val =
      ((rationalAdeleStageCoordinates hL).symm c).val := by
    rw [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val]
  rw [hval]
  by_cases hx : x ∈ rationalAdeleStageSupport (L n)
  · obtain ⟨j, hj, _⟩ := (mem_rationalAdeleStageSupport_iff_existsUnique_cell hL x).mp hx
    have hcell (t : ℝ) : rationalAdeleAt (t * rationalAdeleReal x) x.2 ∈
        rationalAdeleStageCell (L n) j := by
      rw [mem_rationalAdeleStageCell_iff hL, rationalAdeleAt_finite]
      exact (mem_rationalAdeleStageCell_iff hL j x).mp hj
    have he : orbit (rationalAdeleLFAssembly n b) x = fun t ↦ b j (t * rationalAdeleReal x) := by
      funext t
      rw [orbit, hval, ← rationalAdeleStageCoordinates_eq_on_cell hL _ (hcell t),
        LinearEquiv.apply_symm_apply, rationalAdeleReal_at]
    rw [he, ← rationalAdeleStageCoordinates_eq_on_cell hL _ hj,
      LinearEquiv.apply_symm_apply, rationalAdeleStageEuler_apply]
    have h := ((b j).hasDerivAt (rationalAdeleReal x)).scomp_of_eq 1
      ((hasDerivAt_id' 1).mul_const (rationalAdeleReal x)) (one_mul _).symm
    simpa [Function.comp_def] using h
  · have hout (t : ℝ) : rationalAdeleAt (t * rationalAdeleReal x) x.2 ∉
        rationalAdeleStageSupport (L n) := by
      change ((L n : FiniteAdeleRing (𝓞 ℚ) ℚ) * (rationalAdeleAt _ x.2).2) ∉
        rationalFiniteIntegralAdeles
      rw [rationalAdeleAt_finite]
      exact hx
    have he : orbit (rationalAdeleLFAssembly n b) x = fun _ ↦ 0 := by
      funext t
      rw [orbit, hval]
      exact ((rationalAdeleStageCoordinates hL).symm b).property.1 _ (hout t)
    rw [he, ((rationalAdeleStageCoordinates hL).symm (rationalAdeleStageEuler n b)).property.1 x hx]
    exact hasDerivAt_const 1 0

private noncomputable def stageIndex (f : E) : ℕ :=
  (mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property).choose

private theorem stageIndex_assembly (f : E) :
    rationalAdeleLFAssembly (stageIndex f) (rationalAdeleLFRead (stageIndex f) f) = f :=
  rationalAdeleLFAssembly_read _ f
    (mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property).choose_spec

private noncomputable def generatorValue (f : E) : E :=
  let n := stageIndex f
  rationalAdeleLFAssembly n (rationalAdeleStageEuler n (rationalAdeleLFRead n f))

private theorem generatorValue_apply (f : E) (x : A) :
    (generatorValue f).toUnion.val x = deriv (orbit f x) 1 := by
  have h := (assembly_hasDerivAt (stageIndex f) (rationalAdeleLFRead (stageIndex f) f) x).deriv
  rw [stageIndex_assembly] at h
  exact h.symm

/-- The stagewise Euler operator on the algebraic union. -/
public noncomputable def rationalAdeleLFDilationLinear : E →ₗ[ℂ] E where
  toFun := generatorValue
  map_add' f g := by
    apply RationalAdeleSchwartzLF.ext
    funext x
    rw [map_add, Submodule.coe_add, Pi.add_apply]
    have he : orbit (f + g) x = orbit f x + orbit g x := by
      funext t
      simp only [orbit, map_add, Submodule.coe_add, Pi.add_apply]
    rw [generatorValue_apply, generatorValue_apply, generatorValue_apply, he]
    exact deriv_add (hasDerivAt_orbit f x).differentiableAt (hasDerivAt_orbit g x).differentiableAt
  map_smul' c f := by
    apply RationalAdeleSchwartzLF.ext
    funext x
    change (generatorValue (c • f)).toUnion.val x = (c • generatorValue f).toUnion.val x
    rw [map_smul, Submodule.coe_smul, Pi.smul_apply]
    have he : orbit (c • f) x = c • orbit f x := by
      funext t
      simp only [orbit, map_smul, Submodule.coe_smul, Pi.smul_apply]
    rw [generatorValue_apply, generatorValue_apply, he]
    exact deriv_const_smul c (hasDerivAt_orbit f x).differentiableAt

public theorem rationalAdeleLFDilationLinear_assembly (n : ℕ) (b : Profiles n) :
    rationalAdeleLFDilationLinear (rationalAdeleLFAssembly n b) =
      rationalAdeleLFAssembly n (rationalAdeleStageEuler n b) := by
  apply RationalAdeleSchwartzLF.ext
  funext x
  change (generatorValue (rationalAdeleLFAssembly n b)).toUnion.val x = _
  rw [generatorValue_apply, (assembly_hasDerivAt n b x).deriv]

/-- Pointwise Euler formula for the algebraic dilation operator. -/
public theorem rationalAdeleLFDilationLinear_apply (f : E) (x : A) :
    (rationalAdeleLFDilationLinear f).toUnion.val x =
      (rationalAdeleReal x : ℂ) *
        deriv (fun u ↦ f.toUnion.val (rationalAdeleAt u x.2)) (rationalAdeleReal x) := by
  change (generatorValue f).toUnion.val x = _
  exact (generatorValue_apply f x).trans (hasDerivAt_orbit f x).deriv

public theorem hasDerivAt_rationalAdeleLFDilationLinear (f : E) (x : A) :
    HasDerivAt (fun t : ℝ ↦ f.toUnion.val (rationalAdeleAt (t * rationalAdeleReal x) x.2))
      ((rationalAdeleLFDilationLinear f).toUnion.val x) 1 := by
  rw [rationalAdeleLFDilationLinear_apply]
  exact hasDerivAt_orbit f x

/-- Multiplication by the log-norm section scales the real coordinate only. -/
public theorem rationalIdeleLogSection_mul_adele (s : ℝ) (x : A) :
    (rationalIdeleLogSection (Multiplicative.ofAdd s) : A) * x =
      rationalAdeleAt (Real.exp s * rationalAdeleReal x) x.2 := by
  let g := rationalIdeleLogSection (Multiplicative.ofAdd s)
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  refine Prod.ext (funext fun v ↦ ?_) (FiniteAdeleRing.ext _ fun v ↦ ?_)
  · have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
    subst v
    apply e.injective
    dsimp only [e]
    rw [← rationalAdeleReal_apply, ← rationalAdeleReal_apply, rationalAdeleReal_at]
    have hreal : rationalAdeleReal ((g : A) * x) =
        rationalAdeleReal (g : A) * rationalAdeleReal x := by
      simp only [rationalAdeleReal_apply]
      exact map_mul e _ _
    have hg : rationalAdeleReal (g : A) = Real.exp s := by
      rw [rationalAdeleReal_apply]
      exact rationalIdeleReal_logSection (Multiplicative.ofAdd s)
    rw [hreal, hg]
  · rw [rationalAdeleAt_finite]
    change (g : A).2 v * x.2 v = x.2 v
    rw [rationalIdeleLogSection_finite, one_mul]

end Masullo
