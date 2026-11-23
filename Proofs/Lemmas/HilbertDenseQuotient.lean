module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Separated Hilbert completion of a quotient of a dense subspace

For a linear image of `E` dense in a Hilbert space `H`, project to the
orthogonal complement of the image of `T ≤ E`. The resulting map from `E / T`
has dense range and computes the distance seminorm. No separation of `E / T`
or continuity in a pre-existing topology on `E` is assumed.
-/

open Function Set

namespace Masullo

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The Hilbert quotient by `closure T`, realized in the orthogonal complement. -/
@[expose] public noncomputable def hilbertQuotientProjection (T : Submodule 𝕜 H) : H →L[𝕜] Tᗮ :=
  Tᗮ.orthogonalProjectionOnto

/-- The projection annihilates the closure, not just the original subspace. -/
public theorem ker_hilbertQuotientProjection (T : Submodule 𝕜 H) :
    (hilbertQuotientProjection T).ker = T.topologicalClosure := by
  rw [hilbertQuotientProjection, Submodule.ker_orthogonalProjectionOnto,
    Submodule.orthogonal_orthogonal_eq_closure]

/-- Every vector in the complementary closed subspace is its own lift. -/
public theorem surjective_hilbertQuotientProjection (T : Submodule 𝕜 H) :
    Surjective (hilbertQuotientProjection T) :=
  fun y ↦ ⟨y, Tᗮ.orthogonalProjectionOnto_mem_subspace_eq_self y⟩

/-- Distance to the original subspace, without requiring a nearest vector there. -/
public theorem norm_hilbertQuotientProjection (T : Submodule 𝕜 H) (y : H) :
    ‖hilbertQuotientProjection T y‖ = Metric.infDist y (T : Set H) := by
  change ‖Tᗮ.starProjection y‖ = _
  rw [Tᗮ.norm_starProjection_eq_infDist, Submodule.orthogonal_orthogonal_eq_closure]
  exact Metric.infDist_closure

variable [AddCommGroup E] [Module 𝕜 E]

omit [CompleteSpace H] in
/-- Any left-hand source with the same kernel as its Hilbert realization
embeds, modulo that kernel, densely into the closure of its image. -/
public theorem exists_denseEmbedding_quotient_rangeClosure
    (i : E →ₗ[𝕜] H) (P : Submodule 𝕜 E) (hP : P = i.ker) :
    ∃ L : (E ⧸ P) →ₗ[𝕜] i.range.topologicalClosure,
      Injective L ∧ DenseRange L ∧ ∀ f : E, (L (P.mkQ f)).val = i f := by
  let j : E →ₗ[𝕜] i.range.topologicalClosure :=
    i.codRestrict _ (fun f ↦ i.range.le_topologicalClosure (i.mem_range_self f))
  have hker : P = j.ker := by
    rw [hP]
    ext f
    simp only [LinearMap.mem_ker, Subtype.ext_iff]
    rfl
  let L : (E ⧸ P) →ₗ[𝕜] i.range.topologicalClosure := P.liftQ j hker.le
  refine ⟨L, LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' P j hker), ?_, fun _ ↦ rfl⟩
  intro y
  rw [closure_subtype, ← Set.range_comp]
  have heq : range (Subtype.val ∘ L) = range i := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨f, rfl⟩ := P.mkQ_surjective q
      exact ⟨f, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨P.mkQ f, rfl⟩
  rw [heq, ← LinearMap.coe_range]
  exact y.property

private theorem le_ker_hilbertQuotientProjection_comp (e : E →ₗ[𝕜] H) (T : Submodule 𝕜 E) :
    T ≤ LinearMap.ker ((hilbertQuotientProjection (T.map e)).toLinearMap.comp e) := by
  intro x hx
  rw [LinearMap.ker_comp, ker_hilbertQuotientProjection]
  exact (T.map e).le_topologicalClosure ⟨x, hx, rfl⟩

/-- Descend the Hilbert quotient projection to the original algebraic quotient. -/
public noncomputable def hilbertDenseQuotientMap (e : E →ₗ[𝕜] H) (T : Submodule 𝕜 E) :
    (E ⧸ T) →ₗ[𝕜] (T.map e)ᗮ :=
  T.liftQ ((hilbertQuotientProjection (T.map e)).toLinearMap.comp e)
    (le_ker_hilbertQuotientProjection_comp e T)

/-- The descended map sends a representative to its orthogonal projection. -/
@[simp] public theorem hilbertDenseQuotientMap_mk (e : E →ₗ[𝕜] H) (T : Submodule 𝕜 E) (x : E) :
    hilbertDenseQuotientMap e T (T.mkQ x) = hilbertQuotientProjection (T.map e) (e x) := by
  rw [hilbertDenseQuotientMap]
  rfl

/-- The original quotient seminorm is preserved. Applying this to the
difference of two representatives also gives their seminorm distance. -/
public theorem norm_hilbertDenseQuotientMap_mk (e : E →ₗ[𝕜] H) (T : Submodule 𝕜 E) (x : E) :
    ‖hilbertDenseQuotientMap e T (T.mkQ x)‖ = Metric.infDist (e x) (T.map e : Set H) := by
  rw [hilbertDenseQuotientMap_mk, norm_hilbertQuotientProjection]

/-- On original classes the kernel is the preimage of the ambient closure
modulo `T`. For the inclusion of a subspace this is `(E ∩ closure T) / T`. -/
public theorem ker_hilbertDenseQuotientMap (e : E →ₗ[𝕜] H) (T : Submodule 𝕜 E) :
    LinearMap.ker (hilbertDenseQuotientMap e T) =
      ((T.map e).topologicalClosure.comap e).map T.mkQ := by
  rw [hilbertDenseQuotientMap, Submodule.ker_liftQ, LinearMap.ker_comp,
    ker_hilbertQuotientProjection]

/-- A continuous surjective projection takes the dense test image to a dense
image of original quotient classes. The target is a closed subspace of `H`,
hence complete for its induced inner-product norm. -/
public theorem denseRange_hilbertDenseQuotientMap (e : E →ₗ[𝕜] H) (T : Submodule 𝕜 E)
    (he : DenseRange e) : DenseRange (hilbertDenseQuotientMap e T) := by
  have h := (surjective_hilbertQuotientProjection (T.map e)).denseRange.comp he
    (hilbertQuotientProjection (T.map e)).continuous
  apply h.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨T.mkQ x, rfl⟩

end Masullo
