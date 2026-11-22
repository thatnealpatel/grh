module

public import Mathlib.NumberTheory.NumberField.HeckeLFunction
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Continuity of the local restriction at a finite place -/

open Filter IsDedekindDomain NumberField HeightOneSpectrum Set
open scoped RestrictedProduct

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)

/-- The single-place insertion factors through the stage integral off `v`.
Passing to the units and then to idele classes gives continuity of the
restricted character on the completion units. -/
public theorem continuous_finiteHeckeRestriction (χ : HeckeCharacter (𝓞 K) K) (v : Places) :
    Continuous (fun x : (adicCompletion K v)ˣ ↦ χ.restrict v (x : v.adicCompletion K)) := by
  classical
  have hv : cofinite ≤ 𝓟 ({v} : Set Places)ᶜ := by
    rw [le_principal_iff, mem_cofinite, compl_compl]
    exact finite_singleton v
  let i (a : v.adicCompletion K) :
      Πʳ w : Places, [w.adicCompletion K, w.adicCompletionIntegers K]_[𝓟 ({v} : Set Places)ᶜ] :=
    ⟨Pi.mulSingle v a, by
      rw [eventually_principal]
      intro w hw
      rw [Pi.mulSingle_eq_of_ne (show w ≠ v from hw)]
      exact Subring.one_mem _⟩
  have hi : Continuous i := RestrictedProduct.continuous_rng_of_principal.mpr <| continuous_pi fun w ↦ by
    change Continuous fun a : v.adicCompletion K ↦ Pi.mulSingle (M := fun u : Places ↦
      u.adicCompletion K) v a w
    by_cases hw : w = v
    · subst w
      rw [show (fun a : v.adicCompletion K ↦ Pi.mulSingle (M := fun u : Places ↦
        u.adicCompletion K) v a v) = id from funext (Pi.mulSingle_eq_same v)]
      exact continuous_id
    · simpa only [Pi.mulSingle_eq_of_ne hw] using
        (continuous_const : Continuous fun _ : v.adicCompletion K ↦ (1 : w.adicCompletion K))
  have hfin : Continuous (FiniteAdeleRing.ofAdicCompletion K v) :=
    (RestrictedProduct.continuous_inclusion hv).comp hi
  have hadele : Continuous (AdeleRing.ofAdicCompletion (𝓞 K) K v) := continuous_const.prodMk hfin
  have hidele : Continuous (IdeleGroup.ofAdicCompletion (𝓞 K) K v) := Units.continuous_map hadele
  have hclass : Continuous (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v) :=
    QuotientGroup.continuous_mk.comp hidele
  convert χ.continuous.comp hclass using 1
  funext x
  exact MulChar.ofUnitHom_coe _ _

end Masullo
