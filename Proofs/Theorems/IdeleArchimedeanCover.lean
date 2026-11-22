module

public import Lemmas.IdeleArchimedeanCover

/-!
# Compact cover of the norm-one Archimedean adele units

This is the cover and compactness consequence of Masullo, Lemma A.2.3.8(1)–(2),
PDF pp. 550–551. We keep the whole logarithmic fiber and use a closed window;
neither an angular section nor disjointness, interior, or volume is asserted.
The correspondence is based on the pinned Markdown and numbered PDF layout
extraction (provisional; no rendered-page inspection).

* The homomorphism (A.2.3.3)–(A.2.3.4), p. 548, uses the real place norm or
  the square of the complex place norm. Deleting Mathlib's distinguished place
  gives coordinates on (A.2.3.5): The missing weighted logarithm is minus the
  sum of the retained coordinates. `archimedeanDroppedLog_diagonalUnit`
  identifies the regulator (A.2.3.6) with Mathlib's `Units.logEmbedding` in
  these coordinates.
* Lemma A.2.3.5 and (A.2.3.9)–(A.2.3.10), p. 549, supply the lattice-window
  argument. We use Mathlib's full lattice of unit logarithms, floor the real
  basis coordinates, and enlarge the half-open window to the closed one.
* On p. 551, compactness is deduced from properness in Lemma A.2.3.2(3).
  In place of an appeal to that assertion we prove the needed compact-preimage
  result, `isCompact_preimage_archimedeanDroppedLog`: Restore the omitted
  coordinate, bound each place value and inverse, and apply the closed
  value–inverse embedding of the actual unit group. To lift the window cover
  we translate by an actual integral unit with the chosen lattice logarithm,
  not by a representative chosen modulo torsion.
-/

open NumberField Set
open NumberField.Units.dirichletUnitTheorem (logSpace)

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "G∞" => archimedeanNormOne (K := K)

/-- A compact set whose left translates by the diagonally embedded integral units cover
Masullo's norm-one Archimedean group. -/
public theorem archimedean_compact_cover :
    ∃ C : Set G∞, IsCompact C ∧ ∀ g : G∞,
      ∃ (u : (𝓞 K)ˣ) (c : G∞), c ∈ C ∧ g = archimedeanDiagonalUnit u * c := by
  classical
  let L := NumberField.Units.unitLattice K
  let : Module.Free ℤ L := ZLattice.module_free ℝ L
  let : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  -- The closure of the lattice box, pulled back to the norm-one units.
  let W : Set (logSpace K) := b.parallelepiped
  refine ⟨archimedeanDroppedLog ⁻¹' W,
    isCompact_preimage_archimedeanDroppedLog b.parallelepiped.isCompact, ?_⟩
  intro g
  let x := archimedeanDroppedLog g
  -- Floor in the lattice basis, then choose a genuine integral unit representing that log.
  let y : logSpace K := ZSpan.floor b x
  have hy : y ∈ Submodule.span ℤ (Set.range b) := (ZSpan.floor b x).property
  have hspan : Submodule.span ℤ (Set.range b) = L :=
    (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ
  have hl : y ∈ L := (congrArg (fun S : Submodule ℤ (logSpace K) ↦ y ∈ S) hspan).mp hy
  change y ∈ Submodule.map (NumberField.Units.logEmbedding K).toIntLinearMap ⊤ at hl
  obtain ⟨u, -, hu⟩ := Submodule.mem_map.mp hl
  let a := archimedeanDiagonalUnit u.toMul
  have ha : archimedeanDroppedLog a = (ZSpan.floor b x : logSpace K) :=
    (archimedeanDroppedLog_diagonalUnit u.toMul).trans hu
  -- Subtract the lattice log by multiplying by the inverse of the chosen unit on the left.
  refine ⟨u.toMul, a⁻¹ * g, ?_, (mul_inv_cancel_left a g).symm⟩
  change archimedeanDroppedLog (a⁻¹ * g) ∈ W
  rw [archimedeanDroppedLog_inv_mul, ha]
  exact ZSpan.fundamentalDomain_subset_parallelepiped b (ZSpan.fract_mem_fundamentalDomain b x)

end Masullo
