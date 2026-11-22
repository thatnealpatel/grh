module

public import Lemmas.AdeleBoxDilation
public import Theorems.FiniteAdditiveHeckeGaussian

import Lemmas.AdeleStageBalls
import Lemmas.FiniteCompletionAddHaar

/-! # The finite-stage additive Hecke test belongs to the box span

Masullo, Definition 3.4.3.2(3), PDF p. 152, gives the finite tests in
(3.4.3.7)–(8) and their tensor with an Archimedean Gaussian in (3.4.3.9).
To use the pointwise repair of Theorem 2.2.3.2, PDF p. 82, we need actual
membership in `adeleBoxSpan`. We expand the active finite factors by
`finiteAdditiveHeckeGaussian_eq_sum_principalBalls`. Each tuple of local
balls gives one box on the actual adeles, using integral-ring indicators
at *every* omitted place, not simply dropping those factors.

The Archimedean factor is any Schwartz map in the Euclidean mixed
coordinates here. Its identification with the corrected parity and
angular-weight Gaussian is a separate step. Source reading: Provisional
pinned Markdown and numbered PDF layout.
-/

open IsDedekindDomain NumberField Set
open scoped Classical SchwartzMap

namespace Masullo

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

local notation "A" => AdeleRing (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "E∞" => mixedEmbedding.euclidean.mixedSpace K
local notation "L[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v

/-- The additive finite-stage tensor with a grouped Archimedean Schwartz
factor. For the Hecke tensor (3.4.3.9), `S` contains all ramified places. -/
@[expose] public def adeleHeckeTest (χ : HeckeCharacter (𝓞 K) K) (S : Finset V)
    (φ : 𝓢(E∞, ℂ)) (z : A) : ℂ :=
  if ∀ v ∉ S, z.2 v ∈ O[v] then
    φ ((archimedeanEuclideanToAdele K).symm z.1) *
      ∏ v ∈ S, finiteAdditiveHeckeGaussian χ v (z.2 v)
  else 0

/-- The stage tensor is a finite sum of genuine box tensors with complex
weights. This holds for any stage, even before using unramifiedness off it. -/
public theorem adeleHeckeTest_mem_adeleBoxSpan (χ : HeckeCharacter (𝓞 K) K) (S : Finset V)
    (φ : 𝓢(E∞, ℂ)) : adeleHeckeTest χ S φ ∈ adeleBoxSpan K := by
  -- Choose one common scale, a finite index set, and centers at each active place.
  choose r s a ha using fun v : S ↦ finiteAdditiveHeckeGaussian_eq_sum_principalBalls χ v.val
  let J := (v : S) → s v
  let c (j : J) (v : S) := finiteAdditiveHeckeGaussian χ v.val (a v (j v) : L[v.val])
  let D (v : S) (i : s v) : Set L[v.val] :=
    {y | (↑(r v)⁻¹ : L[v.val]) * (y - (a v i : L[v.val])) ∈ O[v.val]}
  choose b g hbox using fun j : J ↦
    exists_adeleBoxTensor_eq_stageBalls φ S (fun v ↦ (a v (j v) : L[v.val])) r
  have hexpand : adeleHeckeTest χ S φ =
      ∑ j : J, (∏ v : S, c j v) • adeleBoxTensor φ (b j) (g j) := by
    funext z
    simp only [adeleHeckeTest, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hbox]
    by_cases hz : ∀ v ∉ S, z.2 v ∈ O[v]
    · simp only [ite_eq_left hz]
      rw [← Finset.prod_coe_sort]
      have heval : (∏ v : S, finiteAdditiveHeckeGaussian χ v.val (z.2 v.val)) =
          ∏ v : S, ∑ i : s v, (D v i).indicator
            (fun _ ↦ finiteAdditiveHeckeGaussian χ v.val (a v i : L[v.val])) (z.2 v.val) :=
        Finset.prod_congr rfl fun v _ ↦ ha v _
      rw [heval, Fintype.prod_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change φ _ * (∏ v : S, (D v (j v)).indicator (fun _ ↦ c j v) (z.2 v.val)) =
        (∏ v : S, c j v) * (φ _ * ∏ v : S, (D v (j v)).indicator (fun _ ↦ (1 : ℂ)) (z.2 v.val))
      have hlocal (v : S) : (D v (j v)).indicator (fun _ ↦ c j v) (z.2 v.val) =
          c j v * (D v (j v)).indicator (fun _ ↦ (1 : ℂ)) (z.2 v.val) := by
        simpa only [mul_one] using indicator_const_mul (D v (j v)) (fun _ ↦ (1 : ℂ))
          (c j v) (z.2 v.val)
      simp_rw [hlocal, Finset.prod_mul_distrib]
      ac_rfl
    · simp [hz]
  rw [hexpand]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
    (adeleBoxTensor_mem_adeleBoxSpan φ (b j) (g j))

/-- Adding places where the Hecke character is unramified leaves the
additive tensor unchanged at every adele, not just on the ideles. -/
public theorem adeleHeckeTest_eq_of_subset (χ : HeckeCharacter (𝓞 K) K) {S T : Finset V}
    (hST : S ⊆ T) (hχ : ∀ v ∈ T, v ∉ S → χ.IsUnramifiedAt v) (φ : 𝓢(E∞, ℂ)) :
    adeleHeckeTest χ S φ = adeleHeckeTest χ T φ := by
  funext z
  by_cases hS : ∀ v ∉ S, z.2 v ∈ O[v]
  · have hT : ∀ v ∉ T, z.2 v ∈ O[v] := fun v hv ↦ hS v (fun hs ↦ hv (hST hs))
    rw [adeleHeckeTest, adeleHeckeTest, ite_eq_left hS, ite_eq_left hT]
    congr 1
    exact Finset.prod_subset hST fun v hvT hvS ↦ by
      simp [finiteAdditiveHeckeGaussian, hχ v hvT hvS, hS v hvS]
  · rw [adeleHeckeTest, adeleHeckeTest, ite_eq_right hS]
    by_cases hT : ∀ v ∉ T, z.2 v ∈ O[v]
    · obtain ⟨v, hv⟩ := not_forall.mp hS
      obtain ⟨hvS, hv⟩ := not_imp.mp hv
      have hvT : v ∈ T := by by_contra hn; exact hv (hT v hn)
      rw [ite_eq_left hT, Finset.prod_eq_zero hvT, mul_zero]
      simp [finiteAdditiveHeckeGaussian, hχ v hvT hvS, hv]
    · rw [ite_eq_right hT]

/-- The additive tensor restricts to the idelic zeta test with the same
Schwartz factor evaluated in the Archimedean unit coordinates. -/
public theorem adeleHeckeTest_coe_idele (χ : HeckeCharacter (𝓞 K) K) (S : Finset V)
    (φ : 𝓢(E∞, ℂ)) (arch : ((v : InfinitePlace K) → v.Completionˣ) → ℂ)
    (harch : ∀ a : IdeleGroup (𝓞 K) K,
      φ ((archimedeanEuclideanToAdele K).symm (a : A).1) = arch (ideleInfiniteCoordinates K a))
    (a : IdeleGroup (𝓞 K) K) :
    adeleHeckeTest χ S φ (a : A) = ideleZetaTest K S arch (finiteHeckeGaussian χ) a := by
  have hguard : (∀ v ∉ S, (a : A).2 v ∈ O[v]) ↔ ∀ v ∉ S, ‖(a : A).2 v‖ ≤ 1 := by
    refine forall_congr' fun v ↦ imp_congr_right fun _ ↦ ?_
    change (a : A).2 v ∈ (O[v] : Set L[v]) ↔ _
    rw [finiteCompletionIntegers_eq_closedBall, Metric.mem_closedBall, dist_zero_right]
  simp only [adeleHeckeTest, ideleZetaTest, hguard, harch,
    ← finiteAdditiveHeckeGaussian_coe_unit, ideleFiniteCoordinate_val]

end

end Masullo
