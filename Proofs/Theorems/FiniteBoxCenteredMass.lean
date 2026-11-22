module

public import Lemmas.FiniteCompletionNormalizedHaar
public import Lemmas.FiniteIdeleIdealNorm
public import Theorems.ArchimedeanIdealDual
import Theorems.FiniteCompletionMultiplicativeHaar
import Mathlib.Algebra.FiniteSupport.Basic

/-! # Finite mass and lattice covolume for a centered adelic box

Masullo, PDF p. 556, Definition A.3.1.2(3), (A.3.1.2), calibrates the
integer-ring masses. Lemma A.3.1.3, (A.3.1.3), uses their product at the
unit box; Lemma A.3.1.4, (A.3.1.4), cites the global dilation formula.
Here we use the proved local dilation on each box factor and match the
result to the trace-measure covolume of the associated fractional ideal.
This is a repair for the lattice Poisson argument, not a construction of
an additive restricted-product measure. Source reading: Provisional,
from the pinned Markdown and numbered PDF layout.
-/

open Function IsDedekindDomain MeasureTheory NumberField
open scoped BigOperators Classical InnerProductSpace nonZeroDivisors Pointwise

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => IsDedekindDomain.FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "D" => differentIdeal ℤ (𝓞 K)
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v

-- Use the canonical Borel σ-algebra; no measurable-space choice enters the endpoint.
local notation "mass[" v "," B "]" =>
  (@Measure.real K[v] (borel K[v])
    (@finiteCompletionNormalizedHaar K _ _ v (borel K[v])
      (@BorelSpace.mk K[v] _ (borel K[v]) rfl)) (B : Set K[v]))

local notation "unitMass" => (fun v : V ↦ mass[v, O[v]])
local notation "boxMass[" g "]" => (fun v : V ↦ mass[v, Units.val g v • (O[v] : Set K[v])])

local instance (v : V) : MeasurableSpace K[v]ˣ := borel _
local instance (v : V) : BorelSpace K[v]ˣ := ⟨rfl⟩

-- Compare the numerical calibrations on the two local groups, not the measures.
private theorem unitBox_mass :
    (unitMass).HasFiniteMulSupport ∧
      (∏ᶠ v : V, unitMass v) = (Real.sqrt ((discr K).natAbs : ℝ))⁻¹ := by
  classical
  let S := (finite_differentIdeal_multiplicity_support (K := K)).toFinset
  have hS (v : V) (hv : v ∉ S) : multiplicity v.asIdeal D = 0 := by
    by_contra hn
    exact hv (Set.Finite.mem_toFinset _ |>.mpr hn)
  have hmass (v : V) : unitMass v =
      (finiteCompletionUnitMass K (fun w ↦ finiteCompletionMultiplicativeHaar w) v).toReal := by
    borelize K[v]
    change (finiteCompletionNormalizedHaar v).real (O[v] : Set K[v]) = _
    rw [finiteCompletionNormalizedHaar_real, finiteCompletionDifferentExponent_eq_global_multiplicity,
      finiteCompletionUnitMass, finiteCompletionMultiplicativeHaar_unitMass, ENNReal.toReal_ofReal]
    positivity
  have hsupp : mulSupport unitMass ⊆ S := by
    intro v hv
    by_contra hvS
    apply hv
    rw [hmass, finiteCompletionMultiplicativeHaar_unitMass_eq_one v (hS v hvS), ENNReal.toReal_one]
  refine ⟨S.finite_toSet.subset hsupp, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  simp_rw [hmass]
  exact prod_finiteCompletionMultiplicativeHaar_unitMass S hS

/-- For the box with local factors `g_v O_v`, all but finitely many real masses
are one. Their product is the reciprocal of the associated ideal lattice's
covolume in the Archimedean trace normalization. -/
public theorem finiteBox_centeredMass_finprod (g : Fˣ) :
    boxMass[g].HasFiniteMulSupport ∧
      (∏ᶠ v : V, boxMass[g] v) =
        (ZLattice.covolume (archimedeanIdealLattice K (finiteIdeleIdeal K g))
          (archimedeanTraceMeasure K))⁻¹ := by
  have hfactor (v : V) : boxMass[g] v = ‖g.val v‖ * unitMass v := by
    borelize K[v]
    exact finiteCompletionNormalizedHaar_real_smul_integers v (g.val v)
      ((IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp g.isUnit).1 v)
  rw [show boxMass[g] = (fun v : V ↦ ‖g.val v‖ * unitMass v) from funext hfactor]
  -- Both the finite idele and the different can contribute nontrivial factors.
  have hg := NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm g
  obtain ⟨hu, hprod⟩ := unitBox_mass (K := K)
  refine ⟨hg.mul hu, ?_⟩
  rw [finprod_mul_distrib hg hu, ← NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit g, hprod,
    ← absNorm_inv_finiteIdeleIdeal g, map_inv₀, Rat.cast_inv, ← mul_inv,
    covolume_archimedeanIdealLattice_traceMeasure, Nat.cast_natAbs, Int.cast_abs]

/-- In arithmetic terms the centered box contributes `(N(I) √|D_K|)⁻¹`. -/
public theorem finiteBox_centeredMass_finprod_eq_absNorm (g : Fˣ) :
    (∏ᶠ v : V, boxMass[g] v) =
      ((FractionalIdeal.absNorm (finiteIdeleIdeal K g : J) : ℝ) * √|(discr K : ℝ)|)⁻¹ := by
  rw [(finiteBox_centeredMass_finprod g).2, covolume_archimedeanIdealLattice_traceMeasure]

end

end Masullo
