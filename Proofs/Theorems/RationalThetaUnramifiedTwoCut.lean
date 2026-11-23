module

public import Theorems.RationalAdeleLiteralTwoCut
public import Theorems.RationalThetaUnramifiedPrimeCut

/-!
# Theta of the disjoint prime-two unit cut

Specialization of the all-prime identity to `2`.
-/

open NumberField
open scoped SchwartzMap

namespace Masullo

local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "p₂" => (Subtype.mk 2 Nat.prime_two : Nat.Primes)
local notation "v₂" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) p₂
local notation "Θ[" f "]" => rationalAdeleClassTheta (Subtype.val (RationalAdeleSchwartzLF.toUnion f))

/-- The literal prime-two cut of an unramified LF tensor has an LF witness
whose class theta is the inverse-uniformizer difference at `2`. -/
public theorem exists_rationalAdeleUnramifiedTwoCut (b : 𝓢(ℝ, ℂ)) (f : E)
    (hf : f.toUnion.val = rationalAdeleUnramified b) :
    ∃ g : E, g.toUnion.val = Set.indicator (rationalAdelePrimeUnits p₂) f.toUnion.val ∧
      ∀ d : C, Θ[g] d = Θ[f] d -
        Θ[f] ((QuotientGroup.mk (rationalThetaRadialUniformizer v₂) : C)⁻¹ * d) :=
  exists_rationalAdeleUnramifiedPrimeCut p₂ b f hf

end Masullo
