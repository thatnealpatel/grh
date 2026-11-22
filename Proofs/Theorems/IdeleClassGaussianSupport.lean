module

public import Lemmas.IdeleCompactDenominators
public import Theorems.IdeleClassCompactHausdorff
public import Theorems.IdeleClassQuotientNormOne
public import Theorems.IdeleHeckeGaussian

/-! # A uniform finite-support lattice on norm-one representatives

Masullo constructs a relatively compact fundamental set of norm-one ideles
in (A.2.3.14), PDF p. 549, and proves relative compactness and coverage in
Proposition A.2.3.10(1)–(2), p. 552. We only need a compact cover, not a
section with unique representatives. We recover it from the checked compact
quotient (proved using that same Archimedean reduction) by lifting a finite
open cover to compact neighborhoods in the actual norm-one subgroup.

Lemma 2.2.2.1(3), (2.2.2.3), pp. 77–78, reduces a special tensor test to a
single fractional-ideal lattice, an input to Theorem 2.2.3.4(1), p. 83.
For the finite-support part of this reduction, the uniformizer prescription
on p. 79 cannot bound a radius greater than one with nonnegative powers.
`exists_uniform_denominator_of_isCompact` instead uses the inverse finite
ideals and constructs one positive rational integer clearing all of them.
This gives a containing lattice for the actual fixed Gaussian with ramified
unit support. No Archimedean majorant or large-norm estimate is proved here.
The manuscript reading is provisional (Markdown and numbered PDF layout).
-/

open IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "q₁" => ideleClassQuotientNormOne (K := K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

/-- A compact set of actual norm-one ideles covers all norm-one classes. -/
public theorem exists_compact_cover_ideleClassNormOne :
    ∃ C : Set I₁, IsCompact C ∧ q₁ '' C = univ := by
  classical
  let _ : CompactSpace C₁ := (compactHausdorff_ideleClassNormOne (K := K)).1
  have hq := isOpenQuotientMap_ideleClassQuotientNormOne (K := K)
  choose B hBc hBn using fun x : I₁ ↦ exists_compact_mem_nhds x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ q₁ '' interior (B x))
    (fun _ ↦ hq.isOpenMap _ isOpen_interior) (by
      intro y _
      obtain ⟨x, rfl⟩ := hq.surjective y
      exact mem_iUnion.mpr ⟨x, mem_image_of_mem q₁ (mem_interior_iff_mem_nhds.mpr (hBn x))⟩)
  refine ⟨⋃ x ∈ s, B x, s.isCompact_biUnion (fun x _ ↦ hBc x), subset_antisymm (subset_univ _) ?_⟩
  intro y hy
  obtain ⟨x, hx, z, hz, rfl⟩ := mem_iUnion₂.mp (hs hy)
  exact mem_image_of_mem q₁ (mem_iUnion₂.mpr ⟨x, hx, interior_subset hz⟩)

/-- The norm-one compact representatives and a denominator uniform in both
    the representative `b` and the diagonal index `a`. -/
public theorem exists_compact_cover_ideleClassNormOne_uniform_denominator :
    ∃ C : Set I₁, IsCompact C ∧ q₁ '' C = univ ∧
      ∃ m : ℕ, 0 < m ∧ ∀ b ∈ C, ∀ a : Kˣ,
        (∀ v : V, ‖(d a * (b : I)).val.2 v‖ ≤ 1) →
        (m : K) * (a : K) ∈ range (algebraMap (𝓞 K) K) := by
  obtain ⟨C, hC, hq⟩ := exists_compact_cover_ideleClassNormOne (K := K)
  obtain ⟨m, hm, hc⟩ := exists_uniform_denominator_of_isCompact _ (hC.image continuous_subtype_val)
  exact ⟨C, hC, hq, m, hm, fun b hb ↦ hc (b : I) (mem_image_of_mem _ hb)⟩

variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- Nonvanishing of the fixed Gaussian implies integrality at every finite
    coordinate. At an active ramified place the factor is supported on
    integral units, whose local norm is exactly one. -/
public theorem norm_finite_le_one_of_ideleHeckeGaussian_ne_zero
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (T : Finset V) {g : I} (hg : ideleHeckeGaussian χ hχ T g ≠ 0) (v : V) :
    ‖g.val.2 v‖ ≤ 1 := by
  classical
  unfold ideleHeckeGaussian ideleZetaTest at hg
  split at hg
  next h =>
    by_cases hv : v ∈ T
    · have hn : finiteHeckeGaussian χ v (ideleFiniteCoordinate K g v) ≠ 0 := by
        intro hz
        rw [Finset.prod_eq_zero hv hz, mul_zero] at hg
        exact hg rfl
      rw [← ideleFiniteCoordinate_val]
      unfold finiteHeckeGaussian at hn
      split at hn
      · split at hn
        · assumption
        · exact (hn rfl).elim
      · by_contra! hgt
        have hnot : ideleFiniteCoordinate K g v ∉ finiteLocalUnitSet v := fun hmem ↦
          (not_le_of_gt hgt) (le_of_eq hmem)
        rw [indicator_of_notMem hnot] at hn
        exact hn rfl
    · exact h v hv
  next => exact (hg rfl).elim

/-- The uniform support lattice for the fixed Gaussian: Only diagonal
    indices in `(1/m) 𝓞 K` contribute on the compact norm-one cover. -/
public theorem exists_compact_cover_ideleClassNormOne_gaussian_denominator
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (T : Finset V) :
    ∃ C : Set I₁, IsCompact C ∧ q₁ '' C = univ ∧
      ∃ m : ℕ, 0 < m ∧ ∀ b ∈ C, ∀ a : Kˣ,
        ideleHeckeGaussian χ hχ T (d a * (b : I)) ≠ 0 →
        (m : K) * (a : K) ∈ range (algebraMap (𝓞 K) K) := by
  obtain ⟨C, hC, hq, m, hm, hc⟩ := exists_compact_cover_ideleClassNormOne_uniform_denominator (K := K)
  exact ⟨C, hC, hq, m, hm, fun b hb a hg ↦
    hc b hb a (norm_finite_le_one_of_ideleHeckeGaussian_ne_zero χ hχ T hg)⟩

end Masullo
