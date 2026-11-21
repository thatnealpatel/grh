module

public import Theorems.RationalDiagonalDual
import Lemmas.RationalAdeleClassDual
import Lemmas.RationalAdeleAdditiveModulus
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Topological self-duality of the rational adeles

This proves the self-duality of Example A.3.1.8, p. 558, with the
compact-open topology of Theorem D.1.1.1, p. 746. The pairing uses the
project's positive real and conjugated finite phases so the character
is trivial on the rational diagonal. This statement does not compare
Haar measures.
-/

open NumberField Function Topology

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "D" => rationalDiagonal
local notation "Cq" => A ⧸ D
local notation "Â" => PontryaginDual (Multiplicative A)
local notation "ι" => algebraMap ℚ A

private theorem pairing_injective : Injective rationalAdelePairing := by
  apply (injective_iff_map_eq_zero rationalAdelePairing).mpr
  intro a ha
  have hrestrict : rationalAdeleRestrictChar a = 0 := by
    rw [rationalAdeleRestrictChar, AddMonoidHom.comp_apply, ha, map_zero]
  have haD : a ∈ D := by
    rw [← ker_rationalAdeleRestrictChar]
    exact hrestrict
  obtain ⟨r, rfl⟩ := haD
  change rationalAdelePairing (ι r) = 0 at ha
  change ι r = 0
  by_contra hr
  have hr' : r ≠ 0 := fun h ↦ hr (by rw [h, map_zero])
  obtain ⟨c, hc⟩ := exists_rationalAdeleClassChar_eq_neg_one hr'
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
  have he := congrArg (fun χ : Additive Â ↦ (χ.toMul (Multiplicative.ofAdd x) : ℂ)) ha
  change ((rationalAdelePairing (ι r)).toMul (Multiplicative.ofAdd x) : ℂ) = 1 at he
  rw [rationalAdelePairing_apply, mul_comm, ← rationalAdeleClassChar_mk, hc] at he
  norm_num at he

private theorem pairing_surjective : Surjective rationalAdelePairing := by
  intro χ
  -- Match the restriction to the rational diagonal, then remove that character.
  let restriction := PontryaginDual.map rationalDiagonalInclusion
  obtain ⟨c, hc⟩ := bijective_rationalAdeleClassToDiagonalDual.surjective
    (Additive.ofMul (restriction χ.toMul))
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [rationalAdeleClassToDiagonalDual_mk] at hc
  let δ : Â := χ.toMul / (rationalAdelePairing a).toMul
  let δ₀ : A →+ Additive Circle :=
    (show Multiplicative A →ₜ* Circle from δ).toMonoidHom.toAdditiveRight
  have hker : D ≤ δ₀.ker := by
    intro x hx
    let r := Multiplicative.ofAdd (⟨x, hx⟩ : D)
    have he := congrArg (fun φ : Additive (PontryaginDual (Multiplicative D)) ↦ φ.toMul r) hc
    change (rationalAdelePairing a).toMul (Multiplicative.ofAdd x) =
      χ.toMul (Multiplicative.ofAdd x) at he
    change χ.toMul (Multiplicative.ofAdd x) / (rationalAdelePairing a).toMul
      (Multiplicative.ofAdd x) = (1 : Circle)
    rw [he, div_self']
  -- The ratio factors through the compact quotient and hence is itself a
  -- pairing character at a rational frequency.
  let θ : Cq →+ Additive Circle := QuotientAddGroup.lift D δ₀ hker
  have hθ : Continuous θ := (QuotientAddGroup.isQuotientMap_mk D).continuous_iff.mpr
    (show Continuous δ₀ from map_continuous δ)
  obtain ⟨r, hr⟩ := exists_rationalAdeleClassChar_eq θ hθ
  have hδ (x : A) : (rationalAdelePairing (ι r)).toMul (Multiplicative.ofAdd x) =
      δ (Multiplicative.ofAdd x) := by
    apply Circle.coe_injective
    rw [rationalAdelePairing_apply, mul_comm, ← rationalAdeleClassChar_mk, hr]
    change (↑((QuotientAddGroup.lift D δ₀ hker) (x : Cq)).toMul : ℂ) = _
    rw [QuotientAddGroup.lift_mk]
    rfl
  refine ⟨a + ι r, ?_⟩
  change (rationalAdelePairing (a + ι r)).toMul = χ.toMul
  apply PontryaginDual.ext
  intro x
  rw [map_add]
  change ((rationalAdelePairing a).toMul x) * ((rationalAdelePairing (ι r)).toMul x) = _
  have hx : (rationalAdelePairing (ι r)).toMul x = δ x := hδ x.toAdd
  rw [hx]
  change _ * (χ.toMul x / (rationalAdelePairing a).toMul x) = _
  rw [mul_comm, div_mul_cancel]

/-- Pairing with the standard character identifies the additive rational adeles
with their full compact-open dual. The multiplicative tags express addition
upstairs and pointwise multiplication of circle characters on the dual. -/
public noncomputable def rationalAdelePontryaginDualEquiv : A ≃ₜ+ Additive Â := by
  letI : LocallyCompactSpace A := rationalAdeleClosedUnitStrip.locallyCompactSpace_of_addGroup
  letI : SecondCountableTopology A := secondCountableTopology_rationalAdeles
  letI : LocallyCompactSpace (Multiplicative A) := ‹LocallyCompactSpace A›
  letI : LocallyCompactSpace (Additive Â) := inferInstanceAs (LocallyCompactSpace Â)
  letI : T2Space (Additive Â) := inferInstanceAs (T2Space Â)
  have hopen := rationalAdelePairing.isOpenMap_of_sigmaCompact pairing_surjective
    continuous_rationalAdelePairing
  apply (AddEquiv.ofBijective rationalAdelePairing ⟨pairing_injective, pairing_surjective⟩)
    |>.toContinuousAddEquiv
  intro s
  change IsOpen (rationalAdelePairing ⁻¹' s) ↔ IsOpen s
  refine ⟨fun hs ↦ ?_, fun hs ↦ hs.preimage continuous_rationalAdelePairing⟩
  simpa only [Set.image_preimage_eq s pairing_surjective] using
    hopen (rationalAdelePairing ⁻¹' s) hs

/-- The topological equivalence has the prescribed pointwise pairing. -/
public theorem rationalAdelePontryaginDualEquiv_apply (a x : A) :
    ((rationalAdelePontryaginDualEquiv a).toMul (Multiplicative.ofAdd x) : ℂ) =
      rationalAdeleAddChar (a * x) := by
  rw [rationalAdelePontryaginDualEquiv]
  exact rationalAdelePairing_apply a x

end Masullo
