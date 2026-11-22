module

public import Theorems.IdeleClassQuotientNormOne
public import Theorems.IdeleClassCompactHausdorff
public import Lemmas.FundamentalDomainQuotientMeasure

/-! # Borel periodization on norm-one idele classes

The Borel descent needed for Theorem D.1.2.1, PDF p. 747, uses continuous
local sections of the actual principal quotient and compactness of the target.
We also identify the index of the fundamental-domain API with `Kˣ`, so no
counting multiplicity is introduced.
-/

open NumberField MeasureTheory Set
open scoped Pointwise

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "d" => idelePrincipalNormOne (K := K)
local notation "q₁" => ideleClassQuotientNormOne (K := K)
local notation "Γ" => Subgroup.op (MonoidHom.range (idelePrincipalNormOne (K := K)))

/-- Index the opposite principal subgroup used by the fundamental-domain API
by actual field units; the diagonal has no repetitions. -/
@[expose] public noncomputable def idelePrincipalIndex : Kˣ ≃ Γ :=
  Equiv.ofBijective (fun a ↦ ⟨MulOpposite.op (d a), ⟨a, rfl⟩⟩) (by
    constructor
    · intro a b hab
      exact idelePrincipalNormOne_injective
        (MulOpposite.op_injective (congrArg (fun s : Γ ↦ s.val) hab))
    · rintro ⟨s, hs⟩
      obtain ⟨a, ha⟩ := hs
      exact ⟨a, Subtype.ext (MulOpposite.unop_injective ha)⟩)

public theorem idelePrincipalIndex_smul (a : Kˣ) (x : I₁) :
    idelePrincipalIndex a • x = d a * x := by
  change x * d a = d a * x
  exact mul_comm _ _

public theorem idelePrincipalIndex_tsum {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : I₁ → E) (x : I₁) : (∑' a : Kˣ, f (d a * x)) = ∑' s : Γ, f (s • x) := by
  simpa only [idelePrincipalIndex_smul] using (idelePrincipalIndex (K := K)).tsum_eq
    (fun s : Γ ↦ f (s • x))

public theorem ideleClassQuotientNormOne_smul (a : Γ) (x : I₁) : q₁ (a • x) = q₁ x := by
  obtain ⟨b, rfl⟩ := (idelePrincipalIndex (K := K)).surjective a
  exact ((ideleClassQuotientNormOne_eq_iff x _).mpr ⟨b, (idelePrincipalIndex_smul b x).symm⟩).symm

/-- Invariance of the sum under a change of representative is just the
bijection `a ↦ a * b` of the actual field units. -/
public theorem idelePrincipal_tsum_mul {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : I₁ → E) (b : Kˣ) (x : I₁) :
    (∑' a : Kˣ, f (d a * (d b * x))) = ∑' a : Kˣ, f (d a * x) := by
  simp_rw [← mul_assoc, ← map_mul]
  exact (Equiv.mulRight b).tsum_eq (fun a : Kˣ ↦ f (d a * x))

variable [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

/-- The inherited Borel space on the actual norm-one classes detects
measurability by pullback along the principal quotient. No measurable
inverse on the fundamental domain is presumed. -/
public theorem measurable_comp_ideleClassQuotientNormOne_iff {E : Type*} [MeasurableSpace E]
    {F : C₁ → E} : Measurable (F ∘ q₁) ↔ Measurable F := by
  let : CompactSpace C₁ := (compactHausdorff_ideleClassNormOne (K := K)).1
  have hq := isOpenQuotientMap_ideleClassQuotientNormOne (K := K)
  exact ⟨measurable_of_comp_openQuotientMap hq exists_open_injOn_ideleClassQuotientNormOne,
    fun hF ↦ hF.comp hq.continuous.measurable⟩

/-- Any Borel fibre-constant function descends to a Borel function on the
actual quotient. The chosen representative need not be a measurable section. -/
public theorem exists_measurable_ideleClassQuotientNormOne_lift {E : Type*} [MeasurableSpace E]
    {f : I₁ → E} (hf : Measurable f) (hperiod : ∀ (a : Kˣ) x, f (d a * x) = f x) :
    ∃ F : C₁ → E, Measurable F ∧ ∀ x, F (q₁ x) = f x := by
  have hq := (isOpenQuotientMap_ideleClassQuotientNormOne (K := K)).surjective
  let s : C₁ → I₁ := Function.surjInv hq
  let F : C₁ → E := f ∘ s
  have hEq (x : I₁) : F (q₁ x) = f x := by
    have hs : q₁ (s (q₁ x)) = q₁ x := Function.rightInverse_surjInv hq (q₁ x)
    obtain ⟨a, ha⟩ := (ideleClassQuotientNormOne_eq_iff x (s (q₁ x))).mp hs.symm
    change f (s (q₁ x)) = f x
    rw [← ha, hperiod]
  have hcomp : F ∘ q₁ = f := funext hEq
  exact ⟨F, measurable_comp_ideleClassQuotientNormOne_iff.mp (hcomp.symm ▸ hf), hEq⟩

end Masullo
