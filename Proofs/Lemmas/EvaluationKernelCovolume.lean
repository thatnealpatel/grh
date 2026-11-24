module

public import Lemmas.TernarySubstitutionDet
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Euclidean coarea for an evaluation lattice

Source: `710dec242ab2:.godel/alice/cheap-filter-occupancy.md:17–29` (selected at scan
`76d66112`), “A small equation if there are many actual points.”
Scope: the covolume identity with the actual integral image (not its saturation) and the
resulting degree-nine kernel bound in ordinary scaled-box monomial coordinates. No
point-counting or Minkowski assertion.
Owner check session: `01a20db3-6987-747d-9d8d-903a502adedd`.
-/

@[expose] public section

noncomputable section

open Module Submodule MeasureTheory
open scoped InnerProductSpace

namespace EvaluationKernelCovolume

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The intersection with the real kernel, regarded as a lattice in that kernel. -/
def kernelLattice (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) : Submodule ℤ (LinearMap.ker J) :=
  ZLattice.comap ℝ L (LinearMap.ker J).subtype

/-- The actual image of the coefficient lattice, with no saturation. -/
def imageLattice (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) : Submodule ℤ F :=
  L.map (J.restrictScalars ℤ)

instance (L : Submodule ℤ E) [DiscreteTopology L] (J : E →ₗ[ℝ] F) :
    DiscreteTopology (kernelLattice L J) :=
  ZLattice.comap_discreteTopology ℝ L continuous_subtype_val Subtype.val_injective

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The actual discrete image spans the target, by surjectivity. -/
theorem imageLattice_full (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (J : E →ₗ[ℝ] F)
    [DiscreteTopology (imageLattice L J)] (hJ : Function.Surjective J) :
    IsZLattice ℝ (imageLattice L J) := by
  constructor
  change Submodule.span ℝ (J '' (L : Set E)) = ⊤
  rw [← Submodule.map_span, IsZLattice.span_top (L := L), Submodule.map_top,
    LinearMap.range_eq_top.mpr hJ]

private def imageMap (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) : L →ₗ[ℤ] imageLattice L J :=
  (J.restrictScalars ℤ).restrict fun _ hx ↦ Submodule.mem_map_of_mem hx

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem imageMap_surjective (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) :
    Function.Surjective (imageMap L J) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

private def kernelInclusion (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) : kernelLattice L J →ₗ[ℤ] L where
  toFun x := ⟨x.1.1, x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def imageSection (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) {ι : Type*}
    (bI : Basis ι ℤ (imageLattice L J)) : imageLattice L J →ₗ[ℤ] L :=
  bI.constr ℤ fun i ↦ (imageMap_surjective L J (bI i)).choose

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem imageMap_imageSection (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) {ι : Type*}
    (bI : Basis ι ℤ (imageLattice L J)) (y : imageLattice L J) :
    imageMap L J (imageSection L J bI y) = y := by
  have h : (imageMap L J).comp (imageSection L J bI) = LinearMap.id := by
    apply bI.ext
    intro i
    simpa [imageSection] using (imageMap_surjective L J (bI i)).choose_spec
  exact DFunLike.congr_fun h y

/-- The integral splitting, constructed by lifting an actual image basis. -/
private def adaptedEquiv (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) {ι : Type*}
    (bI : Basis ι ℤ (imageLattice L J)) : (kernelLattice L J × imageLattice L J) ≃ₗ[ℤ] L := by
  classical
  let g := imageMap L J
  let s := imageSection L J bI
  have hs (y : imageLattice L J) : g (s y) = y := imageMap_imageSection L J bI y
  let k := kernelInclusion L J
  have hk (x : kernelLattice L J) : g (k x) = 0 :=
    Subtype.ext (LinearMap.mem_ker.mp x.1.property)
  refine LinearEquiv.ofBijective (k.coprod s) ⟨?_, ?_⟩
  · intro x y h
    have he : x.2 = y.2 := by
      simpa only [LinearMap.coprod_apply, map_add, hk, hs, zero_add] using congrArg g h
    change k x.1 + s x.2 = k y.1 + s y.2 at h
    rw [he] at h
    have hxy := congrArg (fun a : L ↦ (a : E)) (add_right_cancel h)
    exact Prod.ext (Subtype.ext (Subtype.ext hxy)) he
  · intro x
    let z := x - s (g x)
    have hz : J (z : E) = 0 := by
      have hz' : g z = 0 := by simp [z, hs]
      exact congrArg Subtype.val hz'
    refine ⟨(⟨⟨z, LinearMap.mem_ker.mpr hz⟩, z.property⟩, g x), ?_⟩
    change x - s (g x) + s (g x) = x
    exact sub_add_cancel _ _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem adaptedEquiv_inl (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) {ι : Type*}
    (bI : Basis ι ℤ (imageLattice L J)) (x : kernelLattice L J) :
    adaptedEquiv L J bI (x, 0) = kernelInclusion L J x := by
  change kernelInclusion L J x + imageSection L J bI 0 = kernelInclusion L J x
  rw [map_zero, add_zero]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem adaptedEquiv_image (L : Submodule ℤ E) (J : E →ₗ[ℝ] F) {ι : Type*}
    (bI : Basis ι ℤ (imageLattice L J)) (y : imageLattice L J) :
    J (adaptedEquiv L J bI (0, y) : E) = y := by
  have h : adaptedEquiv L J bI (0, y) = imageSection L J bI y := by
    change kernelInclusion L J 0 + imageSection L J bI y = _
    rw [map_zero, zero_add]
  rw [h]
  exact congrArg (fun a : imageLattice L J ↦ (a : F)) (imageMap_imageSection L J bI y)

/-- Surjectivity and discreteness of the actual image force the intersection to span the real
kernel. -/
theorem kernelLattice_full (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (J : E →ₗ[ℝ] F) [DiscreteTopology (imageLattice L J)] (hJ : Function.Surjective J) :
    IsZLattice ℝ (kernelLattice L J) := by
  let : IsZLattice ℝ (imageLattice L J) := imageLattice_full L J hJ
  let K := kernelLattice L J
  let I := imageLattice L J
  let e := adaptedEquiv L J (Free.chooseBasis ℤ I)
  have hd : finrank ℤ K + finrank ℤ I = finrank ℤ L := by
    rw [← Module.finrank_prod]
    exact e.finrank_eq
  rw [ZLattice.rank ℝ I, ZLattice.rank ℝ L] at hd
  have hr := J.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hJ, finrank_top] at hr
  have hk : finrank ℤ K = finrank ℝ (LinearMap.ker J) := by omega
  have hdisc : DiscreteTopology (Submodule.span ℤ (K : Set (LinearMap.ker J))) := by
    rw [Submodule.span_eq]
    infer_instance
  have hs := Real.finrank_eq_int_finrank_of_discrete hdisc
  rw [Set.finrank, Set.finrank, Submodule.span_eq] at hs
  exact ⟨Submodule.eq_top_of_finrank_eq (hs.trans hk)⟩

section Euclidean

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Restriction of a surjective map to the orthogonal complement of its kernel. -/
def orthogonalKerEquiv (J : E →ₗ[ℝ] F) (hJ : Function.Surjective J) :
    (LinearMap.ker J)ᗮ ≃ₗ[ℝ] F := by
  let K := LinearMap.ker J
  let e := K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  refine LinearEquiv.ofBijective (J.domRestrict Kᗮ) ⟨?_, ?_⟩
  · apply (LinearMap.ker_eq_bot (f := J.domRestrict Kᗮ)).mp
    apply eq_bot_iff.mpr
    intro x hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp K.isCompl_orthogonal.disjoint) _
      (LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hx)) x.property
  · intro y
    obtain ⟨x, rfl⟩ := hJ y
    refine ⟨(e.symm x).2, ?_⟩
    have hx : ((e.symm x).1 : E) + (e.symm x).2 = x := e.apply_symm_apply x
    change J ((e.symm x).2 : E) = J x
    conv_rhs => rw [← hx]
    rw [map_add, LinearMap.mem_ker.mp (e.symm x).1.property, zero_add]

/-- An orthonormal basis of the normal space indexed by the target basis. -/
def orthogonalKerBasis {ι : Type*} [Fintype ι] (J : E →ₗ[ℝ] F) (hJ : Function.Surjective J)
    (bF : OrthonormalBasis ι ℝ F) : OrthonormalBasis ι ℝ (LinearMap.ker J)ᗮ :=
  (stdOrthonormalBasis ℝ (LinearMap.ker J)ᗮ).reindex (Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, (orthogonalKerEquiv J hJ).finrank_eq, finrank_eq_card_basis bF.toBasis]))

/-- The absolute determinant of `J` on the normal space in orthonormal coordinates. -/
def normalJacobian {ι : Type*} [Fintype ι] [DecidableEq ι] (J : E →ₗ[ℝ] F)
    (bP : OrthonormalBasis ι ℝ (LinearMap.ker J)ᗮ) (bF : OrthonormalBasis ι ℝ F) : ℝ :=
  |(LinearMap.toMatrix bP.toBasis bF.toBasis (J.domRestrict (LinearMap.ker J)ᗮ)).det|

private theorem covolume_orthonormal_det {V ι : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Fintype ι] [DecidableEq ι] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (o : OrthonormalBasis ι ℝ V) :
    ZLattice.covolume L volume = |(o.toBasis.toMatrix (fun i ↦ (b i : V))).det| := by
  have hvol : (volume : Measure V).real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    simp only [measureReal_def, OrthonormalBasis.coe_toBasis, o.volume_parallelepiped,
      ENNReal.toReal_one]
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis, hvol, mul_one, Basis.det_apply]
  rfl

/-- Euclidean coarea for a full lattice and a surjective linear map with discrete image.
The two covolumes on the left are measured in the real kernel and the full target respectively.
The result holds for any two orthonormal bases used for the normal determinant, including
empty bases when the target is zero-dimensional. -/
theorem coarea (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (J : E →ₗ[ℝ] F) [DiscreteTopology (imageLattice L J)] (hJ : Function.Surjective J)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bP : OrthonormalBasis ι ℝ (LinearMap.ker J)ᗮ)
    (bF : OrthonormalBasis ι ℝ F) :
    ZLattice.covolume (kernelLattice L J) volume * ZLattice.covolume (imageLattice L J) volume =
      ZLattice.covolume L volume * normalJacobian J bP bF := by
  classical
  let : IsZLattice ℝ (imageLattice L J) := imageLattice_full L J hJ
  let : IsZLattice ℝ (kernelLattice L J) := kernelLattice_full L J hJ
  let K := LinearMap.ker J
  let LK := kernelLattice L J
  let I := imageLattice L J
  let κ := Free.ChooseBasisIndex ℤ LK
  let bK : Basis κ ℤ LK := Free.chooseBasis ℤ LK
  let bI : Basis ι ℤ I := (Free.chooseBasis ℤ I).reindex (Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ I,
      finrank_eq_card_basis bF.toBasis]))
  let bL := (bK.prod bI).map (adaptedEquiv L J bI)
  let oK : OrthonormalBasis κ ℝ K := (stdOrthonormalBasis ℝ K).reindex
    (Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ LK]))
  let e := K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  let B := (oK.toBasis.prod bP.toBasis).map e
  have hleft (j : κ) : B (Sum.inl j) = (oK j : E) := by simp [B, e]
  have hright (j : ι) : B (Sum.inr j) = (bP j : E) := by simp [B, e]
  have horth : Orthonormal ℝ B := by
    rw [orthonormal_iff_ite]
    rintro (i | i) (j | j)
    · rw [hleft i, hleft j]
      simp only [Sum.inl.injEq]
      exact orthonormal_iff_ite.mp oK.orthonormal i j
    · simpa only [hleft, hright, reduceCtorEq, ite_false] using
        (K.mem_orthogonal _).mp (bP j).property _ (oK i).property
    · simpa only [hleft, hright, reduceCtorEq, ite_false] using
        (K.mem_orthogonal' _).mp (bP i).property _ (oK j).property
    · rw [hright i, hright j]
      simp only [Sum.inr.injEq]
      exact orthonormal_iff_ite.mp bP.orthonormal i j
  let oE := B.toOrthonormalBasis horth
  have hOE : oE.toBasis = B := Basis.toBasis_toOrthonormalBasis _ _
  have hl (i : κ) : (bL (Sum.inl i) : E) = (bK i : K).val := by
    calc
      (bL (Sum.inl i) : E) = (adaptedEquiv L J bI (bK i, 0) : E) := by simp [bL]
      _ = (bK i : K).val := by rw [adaptedEquiv_inl]; rfl
  have hi (i : ι) : J (bL (Sum.inr i) : E) = bI i := by
    simpa [bL] using adaptedEquiv_image L J bI (bI i)
  let w (j : ι) : Kᗮ := (e.symm (bL (Sum.inr j) : E)).2
  have hw (j : ι) : J (w j : E) = bI j := by
    have h : ((e.symm (bL (Sum.inr j) : E)).1 : E) + w j = (bL (Sum.inr j) : E) :=
      e.apply_symm_apply _
    have hj := hi j
    rw [← h, map_add, LinearMap.mem_ker.mp (e.symm (bL (Sum.inr j) : E)).1.property,
      zero_add] at hj
    exact hj
  let A := oK.toBasis.toMatrix (fun i ↦ (bK i : K))
  let D := bP.toBasis.toMatrix w
  let C := bF.toBasis.toMatrix (fun i ↦ (bI i : F))
  let R := LinearMap.toMatrix bP.toBasis bF.toBasis (J.domRestrict Kᗮ)
  let U : Matrix κ ι ℝ := fun i j ↦ B.repr (bL (Sum.inr j) : E) (Sum.inl i)
  have hblock : B.toMatrix (fun i ↦ (bL i : E)) = Matrix.fromBlocks A U 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [Basis.toMatrix_apply, Matrix.fromBlocks_apply₁₁, hl]
      simp [B, A, e, Basis.map_repr, Basis.toMatrix_apply]
    · rfl
    · rw [Basis.toMatrix_apply, Matrix.fromBlocks_apply₂₁, hl]
      simp [B, e, Basis.map_repr]
    · simp [B, D, w, Basis.toMatrix_apply, Basis.map_repr]
  have hmul : C = R * D := by
    let v := bF.toBasis.constr ℝ w
    have hv : LinearMap.toMatrix bF.toBasis bP.toBasis v = D := by
      ext i j
      simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, D, v]
    rw [← hv, ← LinearMap.toMatrix_comp]
    ext i j
    simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, C, v, hw, LinearMap.domRestrict_apply]
  rw [covolume_orthonormal_det LK bK oK, covolume_orthonormal_det I bI bF,
    covolume_orthonormal_det L bL oE, hOE, hblock, Matrix.det_fromBlocks_zero₂₁]
  change |A.det| * |C.det| = |A.det * D.det| * |R.det|
  simp only [hmul, Matrix.det_mul, abs_mul]
  ring

/-- The Euclidean coarea identity, using the basis-independent normal determinant. -/
theorem coarea_normDet (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (J : E →ₗ[ℝ] F) [DiscreteTopology (imageLattice L J)] (hJ : Function.Surjective J) :
    ZLattice.covolume (kernelLattice L J) volume * ZLattice.covolume (imageLattice L J) volume =
      ZLattice.covolume L volume * (J.domRestrict (LinearMap.ker J)ᗮ).normDet := by
  classical
  let bF := stdOrthonormalBasis ℝ F
  let bP := orthogonalKerBasis J hJ bF
  rw [coarea L J hJ bP bF, (J.domRestrict (LinearMap.ker J)ᗮ).normDet_eq_norm_det_toMatrix bP bF,
    Real.norm_eq_abs, normalJacobian]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- In rank zero the normal determinant is the determinant of the empty matrix, i.e. `1`. -/
theorem normalJacobian_rank_zero {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (J : E →ₗ[ℝ] F) (bP : OrthonormalBasis ι ℝ (LinearMap.ker J)ᗮ)
    (bF : OrthonormalBasis ι ℝ F) : normalJacobian J bP bF = 1 := by
  rw [normalJacobian, Matrix.det_isEmpty, abs_one]

end Euclidean

section IntegralImage

variable {ι : Type*} [Fintype ι]

/-- The coordinatewise integer lattice in the Euclidean evaluation target. -/
abbrev coordinateLattice (ι : Type*) [Fintype ι] : Submodule ℤ (EuclideanSpace ℝ ι) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)

@[simp]
theorem mem_coordinateLattice_iff (x : EuclideanSpace ℝ ι) :
    x ∈ coordinateLattice ι ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = x i := by
  rw [coordinateLattice, Basis.mem_span_iff_repr_mem]
  rfl

@[simp]
theorem covolume_coordinateLattice : ZLattice.covolume (coordinateLattice ι) volume = 1 := by
  classical
  let o := EuclideanSpace.basisFun ι ℝ
  rw [covolume_orthonormal_det (coordinateLattice ι) (o.toBasis.restrictScalars ℤ) o]
  simp only [Basis.restrictScalars_apply, Basis.toMatrix_self, Matrix.det_one, abs_one]

private theorem discrete_of_le_coordinateLattice {I : Submodule ℤ (EuclideanSpace ℝ ι)}
    (hI : I ≤ coordinateLattice ι) : DiscreteTopology I :=
  DiscreteTopology.of_continuous_injective
    (f := fun x : I ↦ (⟨x.val, hI x.property⟩ : coordinateLattice ι))
    (continuous_subtype_val.subtype_mk _)
    (fun _ _ h ↦ Subtype.ext (congrArg (fun y : coordinateLattice ι ↦ y.val) h))

omit [FiniteDimensional ℝ E] in
/-- The actual full image, contained in the coordinatewise integer lattice, has covolume at
least one. It need not be all of the integer lattice. -/
theorem image_covolume_ge_one (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (J : E →ₗ[ℝ] EuclideanSpace ℝ ι) (hJ : Function.Surjective J)
    (hI : imageLattice L J ≤ coordinateLattice ι) :
    1 ≤ ZLattice.covolume (imageLattice L J) volume := by
  let : DiscreteTopology (imageLattice L J) := discrete_of_le_coordinateLattice hI
  let : IsZLattice ℝ (imageLattice L J) := imageLattice_full L J hJ
  have hi := ZLattice.covolume_div_covolume_eq_relIndex' _ _ hI
  rw [covolume_coordinateLattice, div_one] at hi
  have hp := ZLattice.covolume_pos (imageLattice L J) volume
  rw [hi] at hp ⊢
  exact_mod_cast (Nat.succ_le_of_lt (Nat.cast_pos.mp hp))

variable [MeasurableSpace E] [BorelSpace E]

/-- Euclidean lattice coarea for a surjective family of independent evaluation rows with
integral values on the coefficient lattice. No discreteness or saturation assumption on the
actual image is required: it is discrete by containment in the coordinate lattice. -/
theorem coarea_of_integral (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (J : E →ₗ[ℝ] EuclideanSpace ℝ ι) (hJ : Function.Surjective J)
    (hInt : ∀ x ∈ L, ∀ i, ∃ z : ℤ, (z : ℝ) = J x i) :
    ZLattice.covolume (kernelLattice L J) volume * ZLattice.covolume (imageLattice L J) volume =
      ZLattice.covolume L volume * (J.domRestrict (LinearMap.ker J)ᗮ).normDet := by
  have hI : imageLattice L J ≤ coordinateLattice ι := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_coordinateLattice_iff _).mpr (hInt x hx)
  let : DiscreteTopology (imageLattice L J) := discrete_of_le_coordinateLattice hI
  exact coarea_normDet L J hJ

end IntegralImage

section DegreeNine

open TernarySubstitution

/-- Euclidean coefficient space in the ordinary degree-nine monomials. -/
abbrev Coeff9 := EuclideanSpace ℝ (MonomialIndex 9)

/-- The standard coefficient basis of the Euclidean degree-nine monomial space. -/
abbrev coeffBasis9 := (EuclideanSpace.basisFun (MonomialIndex 9) ℝ).toBasis

/-- The degree-nine substitution acting on ordinary Euclidean coefficient vectors. -/
def substitutionEquiv9 (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) :
    Coeff9 ≃ₗ[ℝ] Coeff9 :=
  LinearEquiv.ofIsUnitDet (f := Matrix.toLin coeffBasis9 coeffBasis9 (substitutionMatrix 9 T))
    (v := coeffBasis9) (v' := coeffBasis9) (by
      rw [LinearMap.toMatrix_toLin, det_substitutionMatrix_nine]
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hT))

/-- Degree-nine forms with integer coefficients in the `z` coordinates, recorded in the
Euclidean `ξ` monomial coordinates, with `z = T ξ`. -/
abbrev coefficientLattice9 (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) :
    Submodule ℤ Coeff9 :=
  Submodule.span ℤ (Set.range (coeffBasis9.map (substitutionEquiv9 T hT)))

/-- Euclidean covolume of `P9` when `T` changes the scaled box coordinates to lattice
coordinates. -/
theorem covolume_coefficientLattice9 (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) :
    ZLattice.covolume (coefficientLattice9 T hT) volume = |T.det| ^ 165 := by
  let b := coeffBasis9.map (substitutionEquiv9 T hT)
  rw [covolume_orthonormal_det (coefficientLattice9 T hT) (b.restrictScalars ℤ)
    (EuclideanSpace.basisFun (MonomialIndex 9) ℝ)]
  have hm : coeffBasis9.toMatrix (fun i ↦ ((b.restrictScalars ℤ i) : Coeff9)) =
      substitutionMatrix 9 T := by
    rw [show (fun i ↦ ((b.restrictScalars ℤ i) : Coeff9)) = ⇑b from
      funext (b.restrictScalars_apply ℤ)]
    change coeffBasis9.toMatrix (fun i ↦ substitutionEquiv9 T hT (coeffBasis9 i)) = _
    rw [← show LinearMap.toMatrix coeffBasis9 coeffBasis9
        (substitutionEquiv9 T hT).toLinearMap =
        coeffBasis9.toMatrix (fun i ↦ substitutionEquiv9 T hT (coeffBasis9 i)) by
      ext i j
      simp only [LinearMap.toMatrix_apply, Basis.toMatrix_apply, LinearEquiv.coe_coe]]
    simp [substitutionEquiv9, LinearEquiv.coe_ofIsUnitDet]
  change |(coeffBasis9.toMatrix (fun i ↦ ((b.restrictScalars ℤ i) : Coeff9))).det| = _
  rw [hm, det_substitutionMatrix_nine, abs_pow]

variable {ι : Type*} [Fintype ι]

/-- Evaluation in the `ξ` coordinates, with one row per representative and no monomial
normalization. -/
def evaluation9 (p : ι → Fin 3 → ℝ) : Coeff9 →ₗ[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toLin coeffBasis9 (EuclideanSpace.basisFun ι ℝ).toBasis
    (fun i (a : MonomialIndex 9) ↦ ∏ j, p i j ^ a.val j)

/-- Coordinate formula for evaluation of a coefficient vector. -/
theorem evaluation9_apply (p : ι → Fin 3 → ℝ) (v : Coeff9) (i : ι) :
    evaluation9 p v i = ∑ a : MonomialIndex 9, (∏ j, p i j ^ a.val j) * v a := by
  classical
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let M : Matrix ι (MonomialIndex 9) ℝ := fun i a ↦ ∏ j, p i j ^ a.val j
  change (b.repr (Matrix.toLin coeffBasis9 b M v)) i = _
  rw [Matrix.toLin_apply]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

open MvPolynomial in
private theorem evaluate_substituted_generator (T : Matrix (Fin 3) (Fin 3) ℝ)
    (hT : T.det ≠ 0) (p : ι → Fin 3 → ℝ) (a : MonomialIndex 9) (i : ι) :
    evaluation9 p (substitutionEquiv9 T hT (coeffBasis9 a)) i =
      ∏ j, (T.mulVec (p i)) j ^ a.val j := by
  classical
  let f := monomial (exponent a) (1 : ℝ)
  have hf : (substitution T f).IsHomogeneous 9 := by
    have ha : (exponent a).degree = 9 := by
      rw [Finsupp.degree_eq_sum]
      simpa only [exponent_apply] using Finset.Nat.mem_antidiagonalTuple.mp a.property
    simpa only [substitution, one_mul] using (isHomogeneous_monomial (1 : ℝ) ha).aeval
      (fun j ↦ ∑ k, C (T j k) * X k) (n := 1)
      (fun j ↦ IsHomogeneous.sum _ _ _ fun k _ ↦ (isHomogeneous_X ℝ k).C_mul _)
  have hmap (b : MonomialIndex 9) : (substitutionEquiv9 T hT (coeffBasis9 a)) b =
      (substitution T f).coeff (exponent b) := by
    change (coeffBasis9.repr ((substitutionEquiv9 T hT).toLinearMap (coeffBasis9 a))) b = _
    rw [show (substitutionEquiv9 T hT).toLinearMap =
        Matrix.toLin coeffBasis9 coeffBasis9 (substitutionMatrix 9 T) from
      LinearEquiv.coe_ofIsUnitDet _]
    rw [← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]
    rfl
  have hcomp : (aeval (p i)).comp (substitution T) =
      aeval (R := ℝ) (T.mulVec (p i)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [Matrix.mulVec, dotProduct]
  calc
    _ = (aeval (p i)) (substitution T f) := by
      rw [evaluation9_apply, ← sum_monomial_coeff hf, map_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [hmap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
      simp only [exponent_apply, Algebra.algebraMap_self_apply, mul_comm]
    _ = (aeval (T.mulVec (p i))) f := DFunLike.congr_fun hcomp f
    _ = _ := by
      change aeval (T.mulVec (p i)) (monomial (exponent a) (1 : ℝ)) = _
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
      simp only [exponent_apply, map_one, one_mul]

private theorem evaluation9_integral (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0)
    (p : ι → Fin 3 → ℝ) (hInt : ∀ i j, ∃ z : ℤ, (z : ℝ) = (T.mulVec (p i)) j) :
    imageLattice (coefficientLattice9 T hT) (evaluation9 p) ≤ coordinateLattice ι := by
  rw [imageLattice, Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  apply (mem_coordinateLattice_iff _).2
  intro i
  choose z hz using hInt i
  refine ⟨∏ j, z j ^ a.val j, ?_⟩
  change ((∏ j, z j ^ a.val j : ℤ) : ℝ) =
    evaluation9 p (((coeffBasis9.map (substitutionEquiv9 T hT)) a) : Coeff9) i
  rw [Int.cast_prod, Basis.map_apply, evaluate_substituted_generator]
  simp only [Int.cast_pow, hz]

private theorem normalDet_le_of_bounded (p : ι → Fin 3 → ℝ)
    (hsurj : Function.Surjective (evaluation9 p)) (B : ℝ) (hB : 0 ≤ B)
    (hp : ∀ i j, |p i j| ≤ B) :
    ((evaluation9 p).domRestrict (evaluation9 p).kerᗮ).normDet ≤
      (Fintype.card ι).factorial * ((Fintype.card (MonomialIndex 9) : ℝ) * B ^ 9) ^ Fintype.card ι := by
  classical
  let bF := EuclideanSpace.basisFun ι ℝ
  let bP := orthogonalKerBasis (evaluation9 p) hsurj bF
  rw [LinearMap.normDet_eq_norm_det_toMatrix _ bP bF, Real.norm_eq_abs]
  refine (Matrix.det_le (abv := AbsoluteValue.abs)
    (x := (Fintype.card (MonomialIndex 9) : ℝ) * B ^ 9) ?_).trans_eq ?_
  · intro i j
    have hn : ‖((bP j : (evaluation9 p).kerᗮ) : Coeff9)‖ = 1 := bP.orthonormal.norm_eq_one j
    change |evaluation9 p (bP j : Coeff9) i| ≤ _
    rw [evaluation9_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _a : MonomialIndex 9, B ^ 9 := by
        apply Finset.sum_le_sum
        intro a _
        rw [abs_mul, Finset.abs_prod]
        have ha : (∑ j : Fin 3, a.val j) = 9 := Finset.Nat.mem_antidiagonalTuple.mp a.property
        have hm : (∏ j : Fin 3, |p i j ^ a.val j|) ≤ B ^ 9 := by
          calc
            _ ≤ ∏ j, B ^ a.val j := by
              refine Finset.prod_le_prod₀ (f := fun j : Fin 3 ↦ |p i j ^ a.val j|)
                (g := fun j : Fin 3 ↦ B ^ a.val j) (fun _ _ ↦ abs_nonneg _) ?_
              intro j _
              rw [abs_pow]
              exact pow_le_pow_left₀ (abs_nonneg _) (hp i j) _
            _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ha]
        have hc : |(bP j : Coeff9) a| ≤ 1 := by
          rw [← hn, ← Real.norm_eq_abs]
          exact PiLp.norm_apply_le (bP j : Coeff9) a
        calc
          _ ≤ B ^ 9 * |(bP j : Coeff9) a| := mul_le_mul_of_nonneg_right hm (abs_nonneg _)
          _ ≤ B ^ 9 := mul_le_of_le_one_right (pow_nonneg hB _) hc
      _ = _ := by simp [nsmul_eq_mul]
  · rw [nsmul_eq_mul]

/-- Coarea for ordinary degree-nine evaluation on lattice points `zᵢ = T ξᵢ`. The image
covolume is that of the actual integral evaluation image. -/
theorem evaluation9_coarea (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0)
    (p : ι → Fin 3 → ℝ) (hsurj : Function.Surjective (evaluation9 p))
    (hInt : ∀ i j, ∃ z : ℤ, (z : ℝ) = (T.mulVec (p i)) j) :
    ZLattice.covolume (kernelLattice (coefficientLattice9 T hT) (evaluation9 p)) volume *
      ZLattice.covolume (imageLattice (coefficientLattice9 T hT) (evaluation9 p)) volume =
      |T.det| ^ 165 * ((evaluation9 p).domRestrict (evaluation9 p).kerᗮ).normDet := by
  have hI := evaluation9_integral T hT p hInt
  let : DiscreteTopology (imageLattice (coefficientLattice9 T hT) (evaluation9 p)) :=
    discrete_of_le_coordinateLattice hI
  rw [coarea_normDet _ _ hsurj, covolume_coefficientLattice9]

/-- The degree-nine kernel covolume bound for bounded representatives and independent rows.
Here `δ` is the scaled lattice covolume, so that `|det T| = δ⁻¹` for the map to lattice
coordinates. The rank-dependent factor is explicit and also applies to an empty row set. -/
theorem evaluation9_kernel_covolume_le (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0)
    (p : ι → Fin 3 → ℝ) (hsurj : Function.Surjective (evaluation9 p))
    (hInt : ∀ i j, ∃ z : ℤ, (z : ℝ) = (T.mulVec (p i)) j)
    (B : ℝ) (hB : 0 ≤ B) (hp : ∀ i j, |p i j| ≤ B) (δ : ℝ) (hδ : |T.det| = δ⁻¹) :
    ZLattice.covolume (kernelLattice (coefficientLattice9 T hT) (evaluation9 p)) volume ≤
      (δ⁻¹) ^ 165 *
        ((Fintype.card ι).factorial *
          ((Fintype.card (MonomialIndex 9) : ℝ) * B ^ 9) ^ Fintype.card ι) := by
  let L := coefficientLattice9 T hT
  let J := evaluation9 p
  have hI := evaluation9_integral T hT p hInt
  let : DiscreteTopology (imageLattice L J) := discrete_of_le_coordinateLattice hI
  let : IsZLattice ℝ (kernelLattice L J) := kernelLattice_full L J hsurj
  calc
    _ ≤ ZLattice.covolume (kernelLattice L J) volume *
        ZLattice.covolume (imageLattice L J) volume :=
      le_mul_of_one_le_right (ZLattice.covolume_pos (kernelLattice L J) volume).le
        (image_covolume_ge_one L J hsurj hI)
    _ = (δ⁻¹) ^ 165 * (J.domRestrict J.kerᗮ).normDet := by
      rw [evaluation9_coarea T hT p hsurj hInt, hδ]
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalDet_le_of_bounded p hsurj B hB hp)
      (by rw [← hδ]; exact pow_nonneg (abs_nonneg _) _)

/-- The rank of a surjective evaluation family is at most the degree-nine coefficient dimension. -/
theorem evaluation9_rank_le (p : ι → Fin 3 → ℝ)
    (hsurj : Function.Surjective (evaluation9 p)) :
    Fintype.card ι ≤ Fintype.card (MonomialIndex 9) := by
  have h := LinearMap.finrank_le_finrank_of_surjective hsurj
  simpa only [Coeff9, finrank_euclideanSpace] using h

/-- The change from scaled-box point coordinates `ξ` to coordinates in a lattice basis `b`. -/
def latticeCoordinates (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  b.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

private theorem coord_det_mul (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    (latticeCoordinates b).det *
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix b).det = 1 := by
  rw [← Matrix.det_mul, latticeCoordinates, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]

/-- The change to coordinates in a lattice basis is nonsingular. -/
theorem latticeCoordinates_det_ne_zero (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    (latticeCoordinates b).det ≠ 0 := by
  intro h
  have hh := coord_det_mul b
  rw [h, zero_mul] at hh
  exact zero_ne_one hh

/-- The determinant of the change to lattice coordinates is the reciprocal of the Euclidean
covolume of that lattice, taken in scaled-box coordinates. -/
theorem abs_det_latticeCoordinates (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    |(latticeCoordinates b).det| = (ZLattice.covolume (span ℤ (Set.range b)) volume)⁻¹ := by
  let o := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [covolume_orthonormal_det _ (b.restrictScalars ℤ) o]
  simp only [Basis.restrictScalars_apply]
  have h := congrArg abs (coord_det_mul b)
  rw [abs_mul, abs_one] at h
  have hn : |(o.toBasis.toMatrix b).det| ≠ 0 := by
    intro hz
    rw [show |((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix b).det| = 0 from hz,
      mul_zero] at h
    exact zero_ne_one h
  calc
    _ = (|(latticeCoordinates b).det| * |(o.toBasis.toMatrix b).det|) *
        |(o.toBasis.toMatrix b).det|⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
    _ = _ := by rw [h, one_mul]

/-- The degree-nine bound starting from a lattice basis in scaled-box space and bounded actual
lattice points. The reciprocal covolume factor is derived from that basis. -/
theorem evaluation9_kernel_covolume_le_of_latticeBasis
    (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (p : ι → EuclideanSpace ℝ (Fin 3))
    (hsurj : Function.Surjective (evaluation9 (fun i j ↦ p i j)))
    (hMem : ∀ i, p i ∈ span ℤ (Set.range b))
    (B : ℝ) (hB : 0 ≤ B) (hp : ∀ i j, |p i j| ≤ B) :
    ZLattice.covolume (kernelLattice
        (coefficientLattice9 (latticeCoordinates b) (latticeCoordinates_det_ne_zero b))
        (evaluation9 (fun i j ↦ p i j))) volume ≤
      (ZLattice.covolume (span ℤ (Set.range b)) volume)⁻¹ ^ 165 *
        ((Fintype.card ι).factorial *
          ((Fintype.card (MonomialIndex 9) : ℝ) * B ^ 9) ^ Fintype.card ι) := by
  apply evaluation9_kernel_covolume_le _ (latticeCoordinates_det_ne_zero b) _ hsurj _ B hB hp _
    (abs_det_latticeCoordinates b)
  intro i j
  have hcoord : ((latticeCoordinates b).mulVec (fun k ↦ p i k)) j = b.repr (p i) j := by
    exact congrFun ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix_mulVec_repr b (p i)) j
  rw [hcoord]
  exact ((b.mem_span_iff_repr_mem ℤ (p i)).mp (hMem i)) j

/-- The degree-nine kernel covolume is at most `C(B) · δ⁻¹⁶⁵`, uniformly over the
size of the independent family, where `B` bounds the scaled-box coordinates and `δ`
is the Euclidean covolume of the point lattice. -/
theorem evaluation9_kernel_covolume_le_uniform
    (b : Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (p : ι → EuclideanSpace ℝ (Fin 3))
    (hsurj : Function.Surjective (evaluation9 (fun i j ↦ p i j)))
    (hMem : ∀ i, p i ∈ span ℤ (Set.range b))
    (B : ℝ) (hB : 0 ≤ B) (hp : ∀ i j, |p i j| ≤ B) :
    ZLattice.covolume (kernelLattice
        (coefficientLattice9 (latticeCoordinates b) (latticeCoordinates_det_ne_zero b))
        (evaluation9 (fun i j ↦ p i j))) volume ≤
      (ZLattice.covolume (span ℤ (Set.range b)) volume)⁻¹ ^ 165 *
        ((Fintype.card (MonomialIndex 9)).factorial *
          (max 1 ((Fintype.card (MonomialIndex 9) : ℝ) * B ^ 9)) ^
            Fintype.card (MonomialIndex 9)) := by
  let N := Fintype.card (MonomialIndex 9)
  let k := Fintype.card ι
  let M : ℝ := N * B ^ 9
  have hk : k ≤ N := evaluation9_rank_le _ hsurj
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB _)
  apply (evaluation9_kernel_covolume_le_of_latticeBasis b p hsurj hMem B hB hp).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg _ _)
  · exact mul_le_mul (Nat.cast_le.mpr (Nat.factorial_le hk))
      ((pow_le_pow_left₀ hM (le_max_right 1 M) k).trans (pow_le_pow_right₀ (le_max_left 1 M) hk))
      (pow_nonneg hM _) (Nat.cast_nonneg _)
  · rw [← abs_det_latticeCoordinates]
    exact abs_nonneg _

end DegreeNine

end EvaluationKernelCovolume
