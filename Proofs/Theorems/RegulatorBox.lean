module

public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# The half-open regulator box

Masullo, (A.2.3.9)–(11) and Lemma A.2.3.5(2), PDF p. 549, takes the
half-open parallelotope of the logarithms of a basis of global units modulo
torsion. We use the weighted logs with Mathlib's distinguished coordinate
omitted, as in `Theorems.ArchimedeanLogMeasure`. Mathlib's basis of the unit
lattice gives precisely the logarithms of a fundamental system of units.

The pointwise translation lemma gives existence and disjointness, including
on the faces of the box. For the regulator in (A.3.2.1), PDF pp. 559–560,
we also identify the box's product-Lebesgue mass with the lattice covolume,
which Mathlib identifies with the absolute determinant in these coordinates.
This is the logarithmic factor only; the angular torsion slice and the
idelic quotient measure are not asserted here.

Source reading: Pinned Markdown and numbered PDF text, not rendered pages.
-/

open MeasureTheory NumberField Set
open NumberField.Units (basisUnitLattice regulator unitLattice)
open NumberField.Units.dirichletUnitTheorem (logSpace)
open scoped Classical

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

/-- The half-open `[0, 1)` parallelotope of the basis of unit logarithms in the
retained weighted log coordinates. -/
@[expose] public noncomputable def regulatorBox : Set (logSpace K) :=
  ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))

public theorem measurableSet_regulatorBox : MeasurableSet (regulatorBox K) :=
  ZSpan.fundamentalDomain_measurableSet _

/-- Every point has a unique translation by a unit logarithm into the box. -/
public theorem existsUnique_unitLattice_vadd_mem_regulatorBox (x : logSpace K) :
    ∃! l : unitLattice K, (l : logSpace K) + x ∈ regulatorBox K := by
  let b := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  -- The span in the pointwise lattice theorem is the full lattice of unit logs.
  have hspan : Submodule.span ℤ (Set.range b) = unitLattice K :=
    (basisUnitLattice K).ofZLatticeBasis_span ℝ
  let P : Submodule ℤ (logSpace K) → Prop :=
    fun L ↦ ∃! l : L, (l : logSpace K) + x ∈ regulatorBox K
  exact hspan ▸ (show P (Submodule.span ℤ (Set.range b)) from
    ZSpan.exist_unique_vadd_mem_fundamentalDomain b x)

/-- The box has product-Lebesgue mass exactly the regulator, with no scalar
from the sum-zero hyperplane. -/
public theorem volume_regulatorBox : volume (regulatorBox K) = ENNReal.ofReal (regulator K) := by
  let b := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  -- Compute the covolume with this particular half-open fundamental domain.
  have hfd : IsAddFundamentalDomain (unitLattice K) (regulatorBox K) volume :=
    ZLattice.isAddFundamentalDomain (basisUnitLattice K) volume
  have hmass : regulator K = volume.real (regulatorBox K) :=
    ZLattice.covolume_eq_measure_fundamentalDomain (unitLattice K) volume hfd
  rw [hmass, measureReal_def, ENNReal.ofReal_toReal]
  exact (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne

end Masullo
