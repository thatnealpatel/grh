module

public import Lemmas.RationalAdeleCyclicFourier
public import Lemmas.RationalAdeleLFStageOperators

/-! # Fourier inversion on the rational adelic Schwartz LF space

This is the rational LF version of the topological isomorphism in
Lemma D.1.6.19(2), pp. 773–775. At each level the inverse is the product
of real Schwartz inversion and the inverse of the normalized finite matrix.
Continuity in both directions uses the rational inductive-limit topology.
-/

open NumberField
open scoped SchwartzMap

namespace Masullo

noncomputable section

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "L" => rationalAdeleFactorialLevel
local notation "Profiles" n => Fin ((L n) ^ 2) → 𝓢(ℝ, ℂ)
local notation "assemble" => rationalAdeleLFAssembly
local notation "stageFourier" =>
  (fun n : ℕ ↦ rationalAdeleStageFourierEquiv (rationalAdeleFactorialLevel_pos n))

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

private theorem forward_assembly (n : ℕ) (b : Profiles n) :
    rationalAdeleLFFourier (assemble n b) = assemble n (stageFourier n b) := by
  rw [rationalAdeleLFFourier_assembly, rationalAdeleStageFourierEquiv_apply]

private theorem forward_bijective : Function.Bijective (rationalAdeleLFFourier : E → E) := by
  constructor
  · intro f g h
    obtain ⟨m, hm⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
    obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp g.toUnion.property
    let k := max m n
    have hf := rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_left m n)) hm
    have hg := rationalAdeleSchwartzStage_mono (rationalAdeleFactorialLevel_dvd (le_max_right m n)) hn
    rw [← rationalAdeleLFAssembly_read k f hf, ← rationalAdeleLFAssembly_read k g hg]
    rw [← rationalAdeleLFAssembly_read k f hf, ← rationalAdeleLFAssembly_read k g hg,
      forward_assembly, forward_assembly] at h
    have hi := (rationalAdeleLFRead_leftInverse k).injective
    exact congrArg (assemble k) ((stageFourier k).injective (hi h))
  · intro f
    obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp f.toUnion.property
    refine ⟨assemble n ((stageFourier n).symm (rationalAdeleLFRead n f)), ?_⟩
    rw [forward_assembly, (stageFourier n).apply_symm_apply,
      rationalAdeleLFAssembly_read n f hn]

private def fourierLinearEquiv : E ≃ₗ[ℂ] E :=
  LinearEquiv.ofBijective rationalAdeleLFFourier.toLinearMap forward_bijective

private theorem linearInverse_assembly (n : ℕ) (b : Profiles n) :
    fourierLinearEquiv.symm (assemble n b) = assemble n ((stageFourier n).symm b) := by
  apply fourierLinearEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change assemble n b = rationalAdeleLFFourier (assemble n ((stageFourier n).symm b))
  rw [forward_assembly, (stageFourier n).apply_symm_apply]

/-- The normalized adelic Fourier integral defines a continuous complex-linear
self-equivalence of the rational Schwartz LF space. -/
public def rationalAdeleLFFourierEquiv : E ≃L[ℂ] E where
  toLinearEquiv := fourierLinearEquiv
  continuous_toFun := rationalAdeleLFFourier.continuous
  continuous_invFun := (rationalAdeleLF_continuous_iff fourierLinearEquiv.symm.toLinearMap).mpr fun n ↦ by
    have he : fourierLinearEquiv.symm.toLinearMap.comp (rationalAdeleLFAssemblyLinear n) =
        ((assemble n).comp (stageFourier n).symm.toContinuousLinearMap).toLinearMap := by
      apply LinearMap.ext
      intro b
      change fourierLinearEquiv.symm (rationalAdeleLFAssemblyLinear n b) =
        assemble n ((stageFourier n).symm b)
      have hb : rationalAdeleLFAssemblyLinear n b = assemble n b :=
        RationalAdeleSchwartzLF.ext (congrArg Subtype.val
          ((rationalAdeleLFAssemblyLinear_toUnion n b).trans
            (rationalAdeleLFAssembly_toUnion n b).symm))
      rw [hb, linearInverse_assembly]
    rw [he]
    exact ((assemble n).comp (stageFourier n).symm.toContinuousLinearMap).continuous

/-- The equivalence extends the existing forward Fourier operator. -/
public theorem rationalAdeleLFFourierEquiv_toContinuousLinearMap :
    rationalAdeleLFFourierEquiv.toContinuousLinearMap = rationalAdeleLFFourier :=
  ContinuousLinearMap.ext fun _ ↦ rfl

/-- Forward evaluation agrees with the normalized adelic Fourier integral at
all rational adelic frequencies. -/
public theorem rationalAdeleLFFourierEquiv_apply (f : E) (y : A) :
    (rationalAdeleLFFourierEquiv f).toUnion.val y = rationalAdeleFourier f.toUnion.val y :=
  congrFun (rationalAdeleLFFourier_eq f) y

/-- Inversion commutes with assembly from each factorial stage. The inverse
there is the inverse of the explicit real and cyclic Fourier matrix. -/
public theorem rationalAdeleLFFourierEquiv_symm_assembly (n : ℕ) (b : Profiles n) :
    rationalAdeleLFFourierEquiv.symm (assemble n b) = assemble n ((stageFourier n).symm b) :=
  linearInverse_assembly n b

/-- Pointwise Schwartz inversion, in the rational adelic pairing coordinates.

Lemma D.1.6.19(2), pp. 773–775, reduces to elementary stages and invokes
(D.1.1.11) for pointwise inversion. Here the finite stage has the exact
Haar coefficient `1/M`, so the inverse is the normalized forward integral
at `-x`. Unlike the literal statement of (D.1.1.11) for arbitrary `L¹`
representatives, this equality uses the actual Schwartz functions. -/
public theorem rationalAdeleLFFourierEquiv_symm_apply (g : E) (x : A) :
    (rationalAdeleLFFourierEquiv.symm g).toUnion.val x = rationalAdeleFourier g.toUnion.val (-x) := by
  obtain ⟨n, hn⟩ := mem_rationalAdeleSchwartzStageUnion.mp g.toUnion.property
  rw [← rationalAdeleLFFourierEquiv_apply, ← rationalAdeleLFAssembly_read n g hn,
    rationalAdeleLFFourierEquiv_symm_assembly]
  change (assemble n ((stageFourier n).symm _)).toUnion.val x =
    (rationalAdeleLFFourier (assemble n _)).toUnion.val (-x)
  rw [forward_assembly]
  simp only [rationalAdeleLFAssembly_toUnion, rationalAdeleFactorialStageAssembly_val]
  exact rationalAdeleStageFourierEquiv_symm_coordinates (rationalAdeleFactorialLevel_pos n) _ x

end
end Masullo
