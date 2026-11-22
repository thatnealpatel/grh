module

public import Theorems.ArchimedeanTorsionMass
public import Theorems.RegulatorBox

import Theorems.ArchimedeanHaarCoordinates

/-!
# The Archimedean unit fundamental domain

Masullo defines `E₀` by the half-open regulator box and the sector at one
infinite place in (A.2.3.13), PDF p. 549. Lemma A.2.3.8(2), (A.2.3.17),
p. 550, asserts the covering and disjointness; the proof on p. 551 uses the
log-lattice reduction and then the torsion reduction. We follow these two
steps pointwise. Instead of choosing a splitting of the unit group as on
p. 551, we lift the unique lattice translation arbitrarily and use the
log kernel to show that any two lifts differ by torsion.

For the Archimedean factors in (A.3.2.1), pp. 559–560, Lean supplies the
mass of the coordinate rectangle using the checked regulator and angular
masses. The coordinates come from the product split in
`Theorems.ArchimedeanHaarCoordinates`. This calculation is not the mass of
a norm-one slice in full Haar measure, nor does it compare quotient Haar
with the product of the local measures.

Source reading: Pinned Markdown and numbered PDF text, not rendered pages.
-/

open MeasureTheory NumberField Set
open NumberField.Units (logEmbedding regulator torsion torsionOrder unitLattice)
open NumberField.Units.dirichletUnitTheorem (logSpace logEmbedding_eq_zero_iff)
open scoped Classical ENNReal

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "U∞" => (InfiniteAdeleRing K)ˣ
local notation "G∞" => archimedeanNormOne (K := K)

/-- Masullo's half-open set `E₀` in the actual norm-one Archimedean unit group. -/
@[expose] public noncomputable def archimedeanUnitDomain (v : InfinitePlace K) : Set G∞ :=
  {g | archimedeanDroppedLog g ∈ regulatorBox K ∧ archimedeanInTorsionSector v g}

private theorem droppedLog_mul (a b : G∞) :
    archimedeanDroppedLog (a * b) = archimedeanDroppedLog a + archimedeanDroppedLog b := by
  have h := archimedeanDroppedLog_inv_mul (K := K) a (a * b)
  rw [inv_mul_cancel_left] at h
  exact (add_comm _ _).trans (eq_sub_iff_add_eq.mp h) |>.symm

private noncomputable def unitLog (u : (𝓞 K)ˣ) : unitLattice K :=
  ⟨logEmbedding K (Additive.ofMul u), Submodule.mem_map.mpr ⟨_, Submodule.mem_top, rfl⟩⟩

/-- Every norm-one unit is sent into `E₀` by exactly one diagonal integral unit. -/
public theorem existsUnique_archimedeanUnit_translate (v : InfinitePlace K) (g : G∞) :
    ∃! u : (𝓞 K)ˣ, archimedeanDiagonalUnit u * g ∈ archimedeanUnitDomain v := by
  -- Reduce the logarithm and lift the unique lattice translation to an integral unit.
  obtain ⟨l, hl, huniq⟩ := existsUnique_unitLattice_vadd_mem_regulatorBox K (archimedeanDroppedLog g)
  obtain ⟨a, -, ha⟩ := Submodule.mem_map.mp l.property
  let z : G∞ := archimedeanDiagonalUnit a.toMul * g
  have hz : archimedeanDroppedLog z ∈ regulatorBox K := by
    have ha' : logEmbedding K (Additive.ofMul a.toMul) = (l : logSpace K) := ha
    rw [droppedLog_mul, archimedeanDroppedLog_diagonalUnit, ha']
    exact hl
  -- A torsion translate preserves the reduced log and reduces the chosen angle.
  obtain ⟨ζ, hζ, hζuniq⟩ := existsUnique_archimedeanTorsion_translate v z
  refine ⟨ζ.val * a.toMul, ⟨?_, ?_⟩, ?_⟩
  · rw [map_mul, mul_assoc, droppedLog_mul, archimedeanDroppedLog_diagonalUnit,
      logEmbedding_eq_zero_iff.mpr ζ.property, zero_add]
    exact hz
  · simpa only [map_mul, mul_assoc] using hζ
  -- Any other reducing unit has the same lattice log, so it differs from `a` by torsion.
  intro u hu
  have hul : unitLog u = l := huniq _ (by
    change logEmbedding K (Additive.ofMul u) + archimedeanDroppedLog g ∈ regulatorBox K
    simpa only [droppedLog_mul, archimedeanDroppedLog_diagonalUnit] using hu.1)
  have hlog : logEmbedding K (Additive.ofMul u) = logEmbedding K a :=
    (congrArg Subtype.val hul).trans ha.symm
  have ht : u * a.toMul⁻¹ ∈ torsion K := (logEmbedding_eq_zero_iff (K := K)).mp (by
    change logEmbedding K (Additive.ofMul u + -a) = 0
    rw [map_add, map_neg, hlog, add_neg_cancel])
  let t : torsion K := ⟨u * a.toMul⁻¹, ht⟩
  have htζ : t = ζ := hζuniq t (by
    have ht_eq : t.val * a.toMul = u := inv_mul_cancel_right _ _
    change archimedeanInTorsionSector v (archimedeanDiagonalUnit t.val * z)
    rw [show archimedeanDiagonalUnit t.val * z = archimedeanDiagonalUnit u * g from by
      rw [show z = archimedeanDiagonalUnit a.toMul * g from rfl, ← mul_assoc, ← map_mul, ht_eq]]
    exact hu.2)
  calc
    u = t.val * a.toMul := (inv_mul_cancel_right _ _).symm
    _ = ζ.val * a.toMul := by rw [htζ]

/-- The retained-log and angular rectangle describing `E₀`. -/
@[expose] public noncomputable def archimedeanUnitDomainCoordinates (v : InfinitePlace K) :
    Set (logSpace K × ((w : InfinitePlace K) → ArchimedeanAngle w)) :=
  regulatorBox K ×ˢ archimedeanAngularTorsionSlice v

/-- The norm-one group membership test agrees pointwise with the coordinate rectangle. -/
public theorem mem_archimedeanUnitDomain_iff_coordinates (v : InfinitePlace K) (g : G∞) :
    g ∈ archimedeanUnitDomain v ↔
      (archimedeanDroppedLog g, fun w ↦ archimedeanAngle w (ContinuousMulEquiv.piUnits (g : U∞) w)) ∈
        archimedeanUnitDomainCoordinates v := by
  exact and_congr_right fun _ ↦ archimedeanInTorsionSector_iff_angularTorsionSlice v g

/-- The Borel structure on the ambient units induces a measurable norm-one domain. -/
public theorem measurableSet_archimedeanUnitDomain [MeasurableSpace U∞] [BorelSpace U∞]
    (v : InfinitePlace K) : MeasurableSet (archimedeanUnitDomain v) := by
  let (w : InfinitePlace K) : MeasurableSpace w.Completionˣ := borel _
  let (w : InfinitePlace K) : BorelSpace w.Completionˣ := ⟨rfl⟩
  have h := ((measurePreserving_infiniteAdeleHaarCoordinates K).measurable.snd).comp
    (measurable_subtype_coe (p := fun g : U∞ ↦ g ∈ archimedeanNormOne))
  have hm : Measurable (fun g : G∞ ↦ (archimedeanDroppedLog g,
      fun w ↦ archimedeanAngle w (ContinuousMulEquiv.piUnits (g : U∞) w))) := by
    convert h using 1
    funext g
    congr 1
    funext w
    rw [archimedeanDroppedLog_apply]
    rfl
  have hrect : MeasurableSet (archimedeanUnitDomainCoordinates v) :=
    (measurableSet_regulatorBox K).prod (measurableSet_archimedeanAngularTorsionSlice v)
  refine (hrect.preimage hm).congr (Set.ext fun g ↦ ?_)
  exact (mem_archimedeanUnitDomain_iff_coordinates v g).symm

/-- The product-coordinate mass of `E₀` is the regulator times the selected angular share. -/
public theorem measure_archimedeanUnitDomainCoordinates (v : InfinitePlace K) :
    let ω := Measure.pi fun w : InfinitePlace K ↦ archimedeanAngularMeasure w
    ((volume : Measure (logSpace K)).prod ω) (archimedeanUnitDomainCoordinates v) =
      ENNReal.ofReal (regulator K) * (ω univ / (torsionOrder K : ℝ≥0∞)) := by
  intro ω
  rw [archimedeanUnitDomainCoordinates, Measure.prod_prod, volume_regulatorBox,
    measure_archimedeanAngularTorsionSlice]

end Masullo
