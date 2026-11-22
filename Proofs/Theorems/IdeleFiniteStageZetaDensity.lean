module

public import Theorems.IdeleFiniteStageCharacter
public import Lemmas.IdeleStageNormCoordinates

/-! # The raw zeta density on finite idele stages

The idelic norm is the product of normalized local norms in (A.1.3.2)–(3),
p. 541, using the squared norm at a complex place as in (3.1.2.3), p. 121.
The local character restrictions are from (3.1.2.4), p. 121.
The raw pairing (3.2.2.1), p. 124, is the integral of a test times the twisted
character. The proof of Theorem 3.4.1.1, pp. 143–144, asserts (3.4.1.6)
for `1 < s.re` without giving the restricted-product limit argument
(see footnote 3, p. 144).
Here we check the pointwise product on the actual open stages, with the
whole Archimedean test as one factor, as in (3.4.1.2), p. 143, and with
the test unchanged at the exceptional finite places. The later steps must
integrate and exhaust the stages; this theorem asserts neither admissible-set
independence nor an identity of global integrals. Passage readings are
provisional (Markdown and PDF layout).
-/

open IsDedekindDomain NumberField
open scoped Classical RestrictedProduct

namespace Masullo

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "I" => IdeleGroup (𝓞 K) K
local notation "F" v => HeightOneSpectrum.adicCompletion K v

/-- Inactive integer-unit coordinates contribute one to the idelic norm. -/
public theorem ideleFiniteStage_norm (S : Finset V) (x : IdeleFiniteStage K S) :
    ‖(ideleFiniteStageEmbedding K S x : AdeleRing (𝓞 K) K)‖ =
      (∏ v : InfinitePlace K, ‖(x.1 v : v.Completion)‖ ^ v.mult) *
      (∏ v : {v // v ∈ S}, ‖(x.2.1 v : F v.val)‖) := by
  rw [AdeleRing.norm_apply_of_isUnit (ideleFiniteStageEmbedding K S x).isUnit]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv ↦
    by_contra fun hn ↦ hv (ideleFiniteStage_norm_finite_notMem K S x v hn))]
  congr 1
  · exact Finset.prod_congr rfl fun v _ ↦ by rw [ideleFiniteStageEmbedding_infinite]
  · rw [← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun v _ ↦ by rw [ideleFiniteStageEmbedding_finite_mem K S x v v.property]

/-- The test at a finite place is the specified test on `E` and the integral-ring
indicator off `E`, both restricted to the completion units. -/
@[expose] public noncomputable def ideleFiniteTest (E : Finset V)
    (f : (v : V) → (F v)ˣ → ℂ) (v : V) (z : (F v)ˣ) : ℂ :=
  if v ∈ E then f v z else if ‖(z : F v)‖ ≤ 1 then 1 else 0

/-- The pure finite tensor with a grouped Archimedean test, evaluated upstairs.
Off `E`, the test imposes integrality at every finite place. -/
@[expose] public noncomputable def ideleZetaTest (E : Finset V)
    (arch : ((v : InfinitePlace K) → v.Completionˣ) → ℂ)
    (f : (v : V) → (F v)ˣ → ℂ) (a : I) : ℂ :=
  if ∀ v ∉ E, ‖(a : AdeleRing (𝓞 K) K).2 v‖ ≤ 1 then
    arch (ideleInfiniteCoordinates K a) *
      (∏ v ∈ E, f v (ideleFiniteCoordinate K a v))
  else 0

private theorem ideleZetaTest_stage (E S : Finset V) (hES : E ⊆ S)
    (arch : ((v : InfinitePlace K) → v.Completionˣ) → ℂ)
    (f : (v : V) → (F v)ˣ → ℂ) (x : IdeleFiniteStage K S) :
    ideleZetaTest K E arch f (ideleFiniteStageEmbedding K S x) =
      arch x.1 * ∏ v : {v // v ∈ S}, ideleFiniteTest K E f v (x.2.1 v) := by
  let a := ideleFiniteStageEmbedding K S x
  by_cases h : ∀ v ∉ E, ‖(a : AdeleRing (𝓞 K) K).2 v‖ ≤ 1
  · rw [ideleZetaTest, ite_eq_left h, ideleInfiniteCoordinates_stage]
    congr 1
    calc
      _ = ∏ v ∈ E, ideleFiniteTest K E f v (ideleFiniteCoordinate K a v) :=
        Finset.prod_congr rfl fun v hv ↦ by simp [ideleFiniteTest, hv, a]
      _ = ∏ v ∈ S, ideleFiniteTest K E f v (ideleFiniteCoordinate K a v) := by
        apply Finset.prod_subset hES
        intro v _ hv
        simp [ideleFiniteTest, hv, ideleFiniteCoordinate_val, h v hv]
      _ = _ := by
        rw [← Finset.prod_coe_sort]
        exact Finset.prod_congr rfl fun v _ ↦ by rw [ideleFiniteCoordinate_stage_mem K S x v v.property]
  · rw [ideleZetaTest, ite_eq_right h]
    obtain ⟨v, hv⟩ := not_forall.mp h
    obtain ⟨hvE, hv⟩ := not_imp.mp hv
    have hvS : v ∈ S := by
      by_contra hn
      exact hv (ideleFiniteStage_norm_finite_notMem K S x v hn).le
    have hv' : ¬ ‖(x.2.1 ⟨v, hvS⟩ : F v)‖ ≤ 1 := by
      rw [← ideleFiniteStageEmbedding_finite_mem K S x v hvS]
      exact hv
    rw [Finset.prod_eq_zero (Finset.mem_univ (⟨v, hvS⟩ : {v // v ∈ S}))
      (by simp [ideleFiniteTest, hvE, hv']), mul_zero]

/-- Pull the raw zeta density onto a stage containing the test exceptions and
all ramification. The infinite-place test need not split over the infinite places. -/
public theorem ideleFiniteStage_zetaDensity (E S : Finset V) (hES : E ⊆ S)
    (χ : HeckeCharacter (𝓞 K) K) (hu : ∀ v ∉ S, χ.IsUnramifiedAt v) (s : ℂ)
    (arch : ((v : InfinitePlace K) → v.Completionˣ) → ℂ)
    (f : (v : V) → (F v)ˣ → ℂ) (x : IdeleFiniteStage K S) :
    let a := ideleFiniteStageEmbedding K S x
    ideleZetaTest K E arch f a * χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) a) *
      (‖(a : AdeleRing (𝓞 K) K)‖ : ℂ) ^ s =
    (arch x.1 * (∏ v : InfinitePlace K, χ (IdeleClassGroup.ofCompletion (𝓞 K) K v (x.1 v))) *
      ((∏ v : InfinitePlace K, ‖(x.1 v : v.Completion)‖ ^ v.mult : ℝ) : ℂ) ^ s) *
    (∏ v : {v // v ∈ S}, ideleFiniteTest K E f v (x.2.1 v) *
      χ.restrict v (x.2.1 v : F v.val) * (‖(x.2.1 v : F v.val)‖ : ℂ) ^ s) := by
  dsimp only
  -- Pull back the test, character, and norm separately before multiplying.
  rw [ideleZetaTest_stage K E S hES, ideleFiniteStage_character_factor K χ S hu,
    ideleFiniteStage_norm K S, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun v _ ↦ pow_nonneg (norm_nonneg _) _)
      (Finset.prod_nonneg fun v _ ↦ norm_nonneg _),
    prod_norm_cpow _ _ (fun _ ↦ norm_nonneg _), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ac_rfl

end Masullo
