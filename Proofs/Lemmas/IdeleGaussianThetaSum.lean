module

public import Lemmas.IdeleGaussianFiniteSupport
public import Lemmas.IdeleMixedScale
public import Lemmas.MixedLatticeGaussianPoisson
public import Lemmas.IdeleGaussianIdeal
import Lemmas.IdeleGaussianSummable
import Lemmas.IdeleGaussianTrivialArch
import all Lemmas.IdeleStageNormCoordinates

/-! # The lattice theta sum of the trivial idelic Gaussian

The finite factors restrict the principal sum to the inverse finite idele
ideal. The Archimedean factors give the normalized mixed Gaussian on that
lattice; the only term missing from principal periodization is its origin.
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "χ₀" => (1 : HeckeCharacter (𝓞 K) K)
local notation "hχ₀" => (fun _ ↦ norm_one)

/-- The mixed Gaussian with the local complex prefactor at each complex place. -/
@[expose] public noncomputable def ideleThetaTest (x : mixedEmbedding.mixedSpace K) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ nrComplexPlaces K *
    mixedGaussian (fun _ ↦ 1) (fun _ ↦ 1) x

@[simp] public theorem ideleThetaTest_zero :
    ideleThetaTest K 0 = ((1 / (2 * Real.pi) : ℝ) : ℂ) ^ nrComplexPlaces K := by
  simp [ideleThetaTest, mixedGaussian]

variable {K}

private theorem real_coord (a : Kˣ) (g : I) (w : {v : InfinitePlace K // v.IsReal}) :
    extensionEmbeddingOfIsReal w.property (ideleInfiniteCoordinates K (d a * g) w.val).val =
      (ideleMixedScale g (mixedEmbedding K (a : K))).1 w := by
  rw [ideleMixedScale_apply]
  change extensionEmbeddingOfIsReal w.property
      (((↑(d a) : AdeleRing (𝓞 K) K).1 w.val) * g.val.1 w.val) =
    extensionEmbeddingOfIsReal w.property (g.val.1 w.val) * (mixedEmbedding K (a : K)).1 w
  rw [map_mul, mul_comm, mixedEmbedding_apply_isReal]
  congr 1
  change extensionEmbeddingOfIsReal w.property (algebraMap K w.val.Completion (a : K)) = _
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, extensionEmbeddingOfIsReal_coe, ← WithAbs.equiv_symm_apply,
    RingEquiv.apply_symm_apply]

private theorem complex_coord (a : Kˣ) (g : I) (w : {v : InfinitePlace K // v.IsComplex}) :
    extensionEmbedding w.val (ideleInfiniteCoordinates K (d a * g) w.val).val =
      (ideleMixedScale g (mixedEmbedding K (a : K))).2 w := by
  rw [ideleMixedScale_apply]
  change extensionEmbedding w.val
      (((↑(d a) : AdeleRing (𝓞 K) K).1 w.val) * g.val.1 w.val) =
    extensionEmbedding w.val (g.val.1 w.val) * (mixedEmbedding K (a : K)).2 w
  rw [map_mul, mul_comm, mixedEmbedding_apply_isComplex]
  congr 1
  change extensionEmbedding w.val (algebraMap K w.val.Completion (a : K)) = _
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, extensionEmbedding_coe, ← WithAbs.equiv_symm_apply,
    RingEquiv.apply_symm_apply]

variable [∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

private theorem arch_prod_eq_ideleThetaTest (a : Kˣ) (g : I) :
    (∏ v, archimedeanHeckeGaussian χ₀ hχ₀ v (ideleInfiniteCoordinates K (d a * g) v)) =
      ideleThetaTest K (ideleMixedScale g (mixedEmbedding K (a : K))) := by
  let x := ideleMixedScale g (mixedEmbedding K (a : K))
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hre (w : {v : InfinitePlace K // v.IsReal}) :
      archimedeanHeckeGaussian χ₀ hχ₀ w.val (ideleInfiniteCoordinates K (d a * g) w.val) =
        Complex.exp (↑(-Real.pi * (1 : ℝ) * (x.1 w) ^ 2 : ℝ) : ℂ) := by
    rw [archimedeanHeckeGaussian_trivial_apply, ite_eq_left w.property]
    have h := (isometry_extensionEmbeddingOfIsReal w.property).norm_map_of_map_zero
      (map_zero _) (ideleInfiniteCoordinates K (d a * g) w.val).val
    rw [real_coord] at h
    rw [← h, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_neg, mul_one, neg_mul]
  have hco (w : {v : InfinitePlace K // v.IsComplex}) :
      archimedeanHeckeGaussian χ₀ hχ₀ w.val (ideleInfiniteCoordinates K (d a * g) w.val) =
        c * Complex.exp (↑(-Real.pi * (2 * (1 : ℝ)) * ‖x.2 w‖ ^ 2 : ℝ) : ℂ) := by
    rw [archimedeanHeckeGaussian_trivial_apply,
      ite_eq_right (not_isReal_iff_isComplex.mpr w.property)]
    have h := (isometry_extensionEmbedding w.val).norm_map_of_map_zero
      (map_zero _) (ideleInfiniteCoordinates K (d a * g) w.val).val
    rw [complex_coord] at h
    change ‖x.2 w‖ = _ at h
    have harg : -(2 * Real.pi * ‖x.2 w‖ ^ 2) = -Real.pi * 2 * ‖x.2 w‖ ^ 2 := by ring
    rw [← h, ← Complex.ofReal_neg, mul_one, harg]
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  simp only [hre, hco, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  change _ = c ^ nrComplexPlaces K * mixedGaussian (fun _ ↦ 1) (fun _ ↦ 1) x
  unfold mixedGaussian
  ac_rfl

/-- On a principal translate, the finite indicator cuts out the Gaussian ideal. -/
private theorem ideleHeckeGaussian_one_diagonal_eq_ideleThetaTest (T : Finset V) (a : Kˣ) (g : I) :
    ideleHeckeGaussian χ₀ hχ₀ T (d a * g) =
      if (a : K) ∈ (ideleGaussianIdeal g : J) then
        ideleThetaTest K (ideleMixedScale g (mixedEmbedding K (a : K))) else 0 := by
  simpa only [ideleGaussianIdeal, Units.val_inv_eq_inv_val, arch_prod_eq_ideleThetaTest] using
    ideleHeckeGaussian_one_diagonal_eq T g a

/-- The convergent principal sum counts the nonzero elements of the inverse finite ideal
exactly once. Adding the origin gives the sum of the full lattice family. -/
private theorem hasSum_ideleThetaTest (T : Finset V) (g : I) :
    HasSum (fun x : (ideleGaussianIdeal g : J) ↦
      ideleThetaTest K (ideleMixedScale g (mixedEmbedding K (x : K))))
      ((∑' a : Kˣ, ideleHeckeGaussian χ₀ hχ₀ T (d a * g)) + ideleThetaTest K 0) := by
  classical
  let A := (ideleGaussianIdeal g : J)
  let z : A := ⟨0, A.zero_mem⟩
  let f (x : A) : ℂ := ideleThetaTest K (ideleMixedScale g (mixedEmbedding K (x : K)))
  let G (a : Kˣ) : ℂ := ideleHeckeGaussian χ₀ hχ₀ T (d a * g)
  let S : Set Kˣ := {a | (a : K) ∈ A}
  let e : S ≃ {x : A // x ∉ ({z} : Finset A)} := {
    toFun a := ⟨⟨(a.val : K), a.property⟩, by
      simpa [Finset.mem_singleton] using fun h : (⟨(a.val : K), a.property⟩ : A) = z ↦
        a.val.ne_zero (congrArg Subtype.val h)⟩
    invFun x := ⟨Units.mk0 (x.val : K) (by
      intro h
      exact x.property (Finset.mem_singleton.mpr (Subtype.ext h))), x.val.property⟩
    left_inv a := Subtype.ext (Units.ext rfl)
    right_inv x := Subtype.ext (Subtype.ext rfl) }
  have hsupport : Function.support G ⊆ S := by
    intro a ha
    by_contra hn
    apply ha
    exact (ideleHeckeGaussian_one_diagonal_eq_ideleThetaTest T a g).trans (ite_eq_right hn)
  have hG : Summable G := (summable_norm_ideleHeckeGaussian_diagonal χ₀ hχ₀ T g).of_norm
  have hS : HasSum (G ∘ (Subtype.val : S → Kˣ)) (∑' a, G a) :=
    (hasSum_subtype_iff_of_support_subset hsupport).mpr hG.hasSum
  have hfun : (fun x : {x : A // x ∉ ({z} : Finset A)} ↦ f x.val) ∘ e = G ∘ Subtype.val := by
    funext a
    exact ((ideleHeckeGaussian_one_diagonal_eq_ideleThetaTest T a.val g).trans
      (ite_eq_left a.property)).symm
  have hp := e.hasSum_iff.mp (hfun.symm ▸ hS)
  have hfull := (Finset.hasSum_compl_iff ({z} : Finset A)).mp hp
  rw [Finset.sum_singleton, show f z = ideleThetaTest K 0 by
    change ideleThetaTest K (ideleMixedScale g (mixedEmbedding K 0)) = _
    rw [map_zero, map_zero]] at hfull
  exact hfull

/-- The normalized Gaussian is summable on the full scaled ideal. -/
public theorem summable_ideleThetaTest (g : I) :
    Summable (fun x : (ideleGaussianIdeal g : J) ↦
      ideleThetaTest K (ideleMixedScale g (mixedEmbedding K (x : K)))) :=
  (hasSum_ideleThetaTest ∅ g).summable

/-- Adding the Gaussian's value at zero to principal periodization gives the full theta sum. -/
public theorem ideleHeckeGaussian_one_periodization_add_zero_eq_tsum (T : Finset V) (g : I) :
    (∑' a : Kˣ, ideleHeckeGaussian χ₀ hχ₀ T (d a * g)) + ideleThetaTest K 0 =
      ∑' x : (ideleGaussianIdeal g : J),
        ideleThetaTest K (ideleMixedScale g (mixedEmbedding K (x : K))) :=
  (hasSum_ideleThetaTest T g).tsum_eq.symm

end Masullo
