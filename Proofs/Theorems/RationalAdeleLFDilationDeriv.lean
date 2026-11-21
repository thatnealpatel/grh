module

public import Lemmas.RationalAdeleDilationDeriv

/-! # The real dilation generator on the rational Schwartz LF space

This is the positive real section case of Lemma 2.2.4.2, pp. 87–88.
The derivative is pointwise in the adele; the resulting operator is
continuous in the rational LF topology. No differentiability of the
orbit in that topology is asserted, nor is this topology identified with
the manuscript tensor topology.
-/

open NumberField IsDedekindDomain
open scoped SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "L" => rationalAdeleFactorialLevel
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)

/-- The complex continuous linear generator of positive real dilation. -/
public noncomputable def rationalAdeleLFDilationDeriv : E →L[ℂ] E where
  toLinearMap := rationalAdeleLFDilationLinear
  cont := (rationalAdeleLF_continuous_iff rationalAdeleLFDilationLinear).mpr fun n ↦ by
    have he (b : Profiles n) : rationalAdeleLFAssemblyLinear n b = rationalAdeleLFAssembly n b :=
      RationalAdeleSchwartzLF.ext <| congrArg Subtype.val <|
        (rationalAdeleLFAssemblyLinear_toUnion n b).trans (rationalAdeleLFAssembly_toUnion n b).symm
    simpa only [LinearMap.coe_comp, Function.comp_def, he, rationalAdeleLFDilationLinear_assembly,
      ContinuousLinearMap.coe_comp] using
      ((rationalAdeleLFAssembly n).comp (rationalAdeleStageEuler n)).continuous

/-- The LF generator preserves each factorial stage and applies the Euler
operator to its profile tuple. -/
public theorem rationalAdeleLFDilationDeriv_assembly (n : ℕ) (b : Profiles n) :
    rationalAdeleLFDilationDeriv (rationalAdeleLFAssembly n b) =
      rationalAdeleLFAssembly n (rationalAdeleStageEuler n b) :=
  rationalAdeleLFDilationLinear_assembly n b

/-- Only the real coordinate is differentiated. The Euler factor makes
the value zero when the real coordinate is zero. -/
public theorem rationalAdeleLFDilationDeriv_apply (f : E) (x : A) :
    (rationalAdeleLFDilationDeriv f).toUnion.val x =
      (rationalAdeleReal x : ℂ) *
        deriv (fun u ↦ f.toUnion.val (rationalAdeleAt u x.2)) (rationalAdeleReal x) :=
  rationalAdeleLFDilationLinear_apply f x

/-- The pointwise derivative at unit scale, corresponding to the denominator
`t - 1` in (2.2.4.2). The all-real formula extends the positive-scale
field action near `1`. -/
public theorem hasDerivAt_rationalAdeleLF_dilate (f : E) (x : A) :
    HasDerivAt (fun t : ℝ ↦ f.toUnion.val (rationalAdeleAt (t * rationalAdeleReal x) x.2))
      ((rationalAdeleLFDilationDeriv f).toUnion.val x) 1 := by
  exact hasDerivAt_rationalAdeleLFDilationLinear f x

/-- The same derivative along the canonical log-norm section, at log scale
zero, corresponding to (2.2.4.3)–(2.2.4.5). -/
public theorem hasDerivAt_rationalAdeleLF_logDilation (f : E) (x : A) :
    HasDerivAt (fun s : ℝ ↦ f.toUnion.val
      ((rationalIdeleLogSection (Multiplicative.ofAdd s) : A) * x))
      ((rationalAdeleLFDilationDeriv f).toUnion.val x) 0 := by
  have h := (hasDerivAt_rationalAdeleLF_dilate f x).scomp_of_eq 0
    (Real.hasDerivAt_exp 0) Real.exp_zero.symm
  simpa only [Function.comp_def, rationalIdeleLogSection_mul_adele, Real.exp_zero, one_smul]
    using h

end Masullo
