module

public import Theorems.IdeleClassQuotientHaar

/-! Borel descent and the full principal action in the log-split coordinates.
The log coordinate is fixed by the principal group by the product formula. -/

open NumberField MeasureTheory Set Topology
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped Masullo Pointwise

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)
local notation "C₁" => ideleClassNormOne (K := K)
local notation "P" => ClassGroup (𝓞 K)
local notation "L" => Multiplicative ℝ
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "d₁" => idelePrincipalNormOne (K := K)
local notation "q" => (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
local notation "q₁" => ideleClassQuotientNormOne (K := K)
local notation "Γ" => Subgroup.op (IdeleGroup.principalSubgroup (𝓞 K) K)
local notation "W" => (w₀ : InfinitePlace K)
local notation "σ" => ideleLogSplit (ideleLogSection W) (ideleLogNorm_section W)
local notation "τ" => ideleClassLogSplit (ideleClassLogSection W) (ideleClassLogNorm_section W)

/-- In the matching log splits, the principal quotient is the identity
on the log coordinate and `q₁` on the norm-one coordinate. -/
public theorem ideleFullQuotient_split (p : L × I₁) :
    q (σ p) = τ (Prod.map id q₁ p) := by
  change (QuotientGroup.mk (σ p) : C) = _
  rw [← ideleClassLogSplit_mk W p]
  congr 1
  exact Prod.ext rfl (Subtype.ext (coe_ideleClassQuotientNormOne p.2).symm)

/-- The principal translation affects only the norm-one coordinate. -/
public theorem ideleFullPrincipal_split (a : Kˣ) (p : L × I₁) :
    d a * σ p = σ (p.1, d₁ a * p.2) := by
  rw [ideleLogSplit_apply, ideleLogSplit_apply, Subgroup.coe_mul, coe_idelePrincipalNormOne]
  ac_rfl

/-- Index full principal translations by actual field units. -/
@[expose] public noncomputable def ideleFullPrincipalIndex : Kˣ ≃ Γ :=
  Equiv.ofBijective (fun a ↦ ⟨MulOpposite.op (d a), ⟨a, rfl⟩⟩) (by
    constructor
    · intro a b hab
      apply idelePrincipalNormOne_injective
      apply Subtype.ext
      exact MulOpposite.op_injective (congrArg (fun s : Γ ↦ s.val) hab)
    · rintro ⟨s, hs⟩
      obtain ⟨a, ha⟩ := hs
      exact ⟨a, Subtype.ext (MulOpposite.unop_injective ha)⟩)

private theorem principalIndex_smul (a : Kˣ) (x : I) :
    ideleFullPrincipalIndex a • x = d a * x := by
  change x * d a = d a * x
  exact mul_comm _ _

public theorem ideleFullPrincipalIndex_tsum {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : I → E) (x : I) : (∑' a : Kˣ, f (d a * x)) = ∑' s : Γ, f (s • x) := by
  simpa only [principalIndex_smul] using
    (ideleFullPrincipalIndex (K := K)).tsum_eq (fun s : Γ ↦ f (s • x))

/-- The full domain is the product of the unrestricted log line and the
norm-one domain, transported back to ideles. -/
@[expose] public noncomputable def ideleFullFundamentalDomain (v : InfinitePlace K) (r : P → I₁) :
    Set I := σ '' (univ ×ˢ ideleFundamentalDomain v r)

private theorem quotient_open : IsOpenQuotientMap (q : I → C) :=
  QuotientGroup.isOpenQuotientMap_mk

variable [MeasurableSpace (IdeleGroup (𝓞 K) K)] [BorelSpace (IdeleGroup (𝓞 K) K)]

public theorem measurable_ideleFullQuotient
    [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)] :
    Measurable (q : I → C) :=
  (quotient_open (K := K)).continuous.measurable

section Domain

variable [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]

public theorem measurableSet_ideleFullFundamentalDomain (v : InfinitePlace K) (r : P → I₁) :
    MeasurableSet (ideleFullFundamentalDomain v r) :=
  (σ).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
    (MeasurableSet.univ.prod (measurableSet_ideleFundamentalDomain v r))

public theorem isFundamentalDomain_ideleFullFundamentalDomain (μ : Measure I)
    (v : InfinitePlace K) (r : P → I₁) (hr : ∀ p, ideleIdealClassNormOne (r p) = p) :
    IsFundamentalDomain Γ (ideleFullFundamentalDomain v r) μ := by
  apply IsFundamentalDomain.mk' (measurableSet_ideleFullFundamentalDomain v r).nullMeasurableSet
  intro x
  obtain ⟨p, rfl⟩ := (σ).surjective x
  have hmem (a : Kˣ) : ideleFullPrincipalIndex a • σ p ∈ ideleFullFundamentalDomain v r ↔
      d₁ a * p.2 ∈ ideleFundamentalDomain v r := by
    rw [principalIndex_smul, ideleFullPrincipal_split, ideleFullFundamentalDomain,
      (σ).injective.mem_set_image]
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨mem_univ _, hx⟩⟩
  obtain ⟨a, ha, huniq⟩ := existsUnique_idelePrincipal_translate v r hr p.2
  refine ⟨ideleFullPrincipalIndex a, (hmem a).mpr ha, ?_⟩
  intro b hb
  obtain ⟨b, rfl⟩ := (ideleFullPrincipalIndex (K := K)).surjective b
  exact congrArg ideleFullPrincipalIndex (huniq b ((hmem b).mp hb))

end Domain

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]

/-- Inverse charts for the full quotient are the norm-one inverse charts
crossed with the log line. The actual quotient has the required Borel descent. -/
public theorem measurable_comp_ideleFullQuotient_iff {E : Type*} [MeasurableSpace E]
    {F : C → E} : Measurable (F ∘ q) ↔ Measurable F := by
  let hq := quotient_open (K := K)
  let : SecondCountableTopology C := hq.secondCountableTopology
  refine ⟨measurable_of_comp_openQuotientMap hq ?_,
    fun hF ↦ hF.comp measurable_ideleFullQuotient⟩
  intro x
  obtain ⟨p, rfl⟩ := (σ).surjective x
  obtain ⟨U, hU, hp, hinj⟩ := exists_open_injOn_ideleClassQuotientNormOne p.2
  refine ⟨σ '' (univ ×ˢ U), (σ).toHomeomorph.isOpenMap _ (isOpen_univ.prod hU),
    mem_image_of_mem _ ⟨mem_univ _, hp⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ heq
  rw [ideleFullQuotient_split, ideleFullQuotient_split] at heq
  have hpair := (τ).injective heq
  exact congrArg σ (Prod.ext (congrArg (Prod.fst : L × C₁ → L) hpair)
    (hinj hy.2 hz.2 (congrArg (Prod.snd : L × C₁ → C₁) hpair)))

/-- Measurable orbit-constant functions lift to the full class group. -/
public theorem exists_measurable_ideleFullQuotient_lift {E : Type*} [MeasurableSpace E]
    {f : I → E} (hf : Measurable f) (hperiod : ∀ (a : Kˣ) x, f (d a * x) = f x) :
    ∃ F : C → E, Measurable F ∧ ∀ x, F (q x) = f x := by
  have hq := (quotient_open (K := K)).surjective
  let s : C → I := Function.surjInv hq
  let F : C → E := f ∘ s
  have hEq (x : I) : F (q x) = f x := by
    have hs : q (s (q x)) = q x := Function.rightInverse_surjInv hq (q x)
    obtain ⟨a, ha⟩ := QuotientGroup.eq_iff_div_mem.mp hs
    have heq : d a * x = s (q x) := eq_div_iff_mul_eq'.mp ha
    change f (s (q x)) = f x
    rw [← heq, hperiod]
  have hcomp : F ∘ q = f := funext hEq
  exact ⟨F, measurable_comp_ideleFullQuotient_iff.mp (hcomp.symm ▸ hf), hEq⟩

end Masullo
