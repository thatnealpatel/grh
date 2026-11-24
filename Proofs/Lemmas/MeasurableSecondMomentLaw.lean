module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Lemmas.SecondMomentDisk
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable four-node laws for the second-moment disk

Source: `75ca254:.godel/bob/full-lattice-deletion-33.md:21–25`.
Consumer: the conditional circle law in `6aa093a:.godel/bob/half-step-deletion-33.md:5–7`.
Owning check session: `01a20d4e-3533-70d0-b28a-ab27fa9217cc`.

Scope: exact first and second moments for measurable parameters in the closed disk,
including the center, boundary, and collapsed disk. The construction supplies labeled
weights and nodes for the same law; it does not assert the numerical price bound.
-/

open Set
open scoped BigOperators

namespace Masullo.MeasurableSecondMomentLaw

-- A minimum over a compact fiber is measurable because its sublevel sets are pulled
-- back from compact images of closed cuts of the original compact set.
private theorem measurable_fiber_min {Ω X Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {K : Set X} (hK : IsCompact K)
    {F : X → Y} (hF : Continuous F) {f : Ω → Y} (hf : Measurable f)
    (h : ∀ a, ∃ x ∈ K, F x = f a) {c : X → ℝ} (hc : Continuous c) :
    ∃ g : Ω → ℝ, Measurable g ∧ ∀ a, ∃ x ∈ K, F x = f a ∧ c x = g a := by
  have hmin (a : Ω) : ∃ x ∈ K ∩ F ⁻¹' {f a}, IsMinOn c (K ∩ F ⁻¹' {f a}) x :=
    (hK.inter_right (isClosed_singleton.preimage hF)).exists_isMinOn (h a) hc.continuousOn
  choose x hx hxmin using hmin
  let g : Ω → ℝ := fun a ↦ c (x a)
  refine ⟨g, measurable_of_Iic fun t ↦ ?_, fun a ↦ ⟨x a, (hx a).1, (hx a).2, rfl⟩⟩
  have hset : g ⁻¹' Iic t = f ⁻¹' (F '' (K ∩ c ⁻¹' Iic t)) := by
    ext a
    constructor
    · intro ha
      exact ⟨x a, ⟨(hx a).1, ha⟩, (hx a).2⟩
    · rintro ⟨y, ⟨hyK, hyt⟩, hyF⟩
      exact (isMinOn_iff.mp (hxmin a) y ⟨hyK, hyF⟩).trans hyt
  rw [hset]
  exact hf ((hK.inter_right (isClosed_Iic.preimage hc)).image hF).measurableSet

-- Retain each minimum by appending it to the target of the next fiber constraint.
private theorem measurable_fiber_coordinates {Ω X Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {K : Set X} (hK : IsCompact K)
    {F : X → Y} (hF : Continuous F) {f : Ω → Y} (hf : Measurable f)
    (h : ∀ a, ∃ x ∈ K, F x = f a) (k : ℕ) (c : Fin k → X → ℝ)
    (hc : ∀ i, Continuous (c i)) :
    ∃ g : Fin k → Ω → ℝ, (∀ i, Measurable (g i)) ∧
      ∀ a, ∃ x ∈ K, F x = f a ∧ ∀ i, c i x = g i a := by
  induction k generalizing Y with
  | zero =>
    refine ⟨Fin.elim0, fun i ↦ i.elim0, fun a ↦ ?_⟩
    obtain ⟨x, hx, hFx⟩ := h a
    exact ⟨x, hx, hFx, fun i ↦ i.elim0⟩
  | succ k ih =>
    obtain ⟨g, hg, hgF⟩ := measurable_fiber_min hK hF hf h (hc 0)
    have h' (a : Ω) : ∃ x ∈ K, (F x, c 0 x) = (f a, g a) := by
      obtain ⟨x, hx, hFx, hcx⟩ := hgF a
      exact ⟨x, hx, Prod.ext hFx hcx⟩
    obtain ⟨v, hv, hvF⟩ := ih (hF.prodMk (hc 0)) (hf.prodMk hg) h'
      (fun i ↦ c i.succ) (fun i ↦ hc i.succ)
    refine ⟨Fin.cases g v, Fin.forall_fin_succ.mpr ⟨?_, ?_⟩, fun a ↦ ?_⟩
    · simpa only [Fin.cases_zero] using hg
    · intro i
      simpa only [Fin.cases_succ] using hv i
    · obtain ⟨x, hx, hFx, hcx⟩ := hvF a
      refine ⟨x, hx, congrArg Prod.fst hFx, Fin.forall_fin_succ.mpr ⟨?_, ?_⟩⟩
      · simpa only [Fin.cases_zero] using congrArg Prod.snd hFx
      · intro i
        simpa only [Fin.cases_succ] using hcx i

private abbrev Law := (Fin 4 → ℝ) × (Fin 4 → ℂ)

private def massSimplex : Set (Fin 4 → ℝ) := {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

private theorem isCompact_massSimplex : IsCompact massSimplex := by
  have hnonneg : IsClosed {p : Fin 4 → ℝ | ∀ i, 0 ≤ p i} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
  have hmass : IsClosed {p : Fin 4 → ℝ | ∑ i, p i = 1} :=
    isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const
  have hbox : IsCompact (Icc (0 : Fin 4 → ℝ) 1) := isCompact_Icc
  refine hbox.of_isClosed_subset (hnonneg.inter hmass) fun p hp ↦ ⟨hp.1, fun i ↦ ?_⟩
  calc
    p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ ↦ hp.1 j) (Finset.mem_univ i)
    _ = 1 := hp.2

private def lawDomain : Set Law := massSimplex ×ˢ {z | ∀ i, ‖z i‖ = 1}

private theorem isCompact_lawDomain : IsCompact lawDomain := by
  have hnodes : IsCompact {z : Fin 4 → ℂ | ∀ i, z i ∈ Metric.sphere 0 1} :=
    isCompact_pi_infinite fun _ ↦ isCompact_sphere _ _
  exact isCompact_massSimplex.prod (by
    simpa only [mem_sphere_iff_norm, sub_zero] using hnodes)

private def moments (l : Law) : ℂ × ℂ :=
  (∑ i, (l.1 i : ℂ) * l.2 i, ∑ i, (l.1 i : ℂ) * l.2 i ^ 2)

private theorem continuous_moments : Continuous moments := by
  have hw (i : Fin 4) : Continuous (fun l : Law ↦ (l.1 i : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst)
  have hz (i : Fin 4) : Continuous (fun l : Law ↦ l.2 i) :=
    (continuous_apply i).comp continuous_snd
  exact (continuous_finsetSum _ fun i _ ↦ (hw i).mul (hz i)).prodMk
    (continuous_finsetSum _ fun i _ ↦ (hw i).mul ((hz i).pow 2))

private abbrev Coord := Fin 4 ⊕ Fin 4 ⊕ Fin 4

private def lawCoordinate : Coord → Law → ℝ
  | .inl i, l => l.1 i
  | .inr (.inl i), l => (l.2 i).re
  | .inr (.inr i), l => (l.2 i).im

private theorem continuous_lawCoordinate (j : Coord) : Continuous (lawCoordinate j) := by
  rcases j with i | (i | i)
  · exact (continuous_apply i).comp continuous_fst
  · exact Complex.continuous_re.comp ((continuous_apply i).comp continuous_snd)
  · exact Complex.continuous_im.comp ((continuous_apply i).comp continuous_snd)

/-- Measurable pairs in the closed second-moment disk have an exact measurable four-node
law. Zero weights and coinciding unit nodes are allowed. Applying this to the subtype of
admissible moment pairs gives Borel selectors. -/
public theorem exists_measurable_four_node_law {Ω : Type*} [MeasurableSpace Ω]
    {m n : Ω → ℂ} (hm : Measurable m) (hn : Measurable n)
    (h : ∀ a, ‖m a‖ ^ 2 + ‖n a - m a ^ 2‖ ≤ 1) :
    ∃ (p : Fin 4 → Ω → ℝ) (z : Fin 4 → Ω → ℂ),
      (∀ i, Measurable (p i)) ∧ (∀ i, Measurable (z i)) ∧
      ∀ a, (∀ i, 0 ≤ p i a) ∧ (∀ i, ‖z i a‖ = 1) ∧ (∑ i, p i a) = 1 ∧
        (∑ i, (p i a : ℂ) * z i a) = m a ∧ (∑ i, (p i a : ℂ) * z i a ^ 2) = n a := by
  have hF (a : Ω) : ∃ l ∈ lawDomain, moments l = (m a, n a) := by
    have hsq : ‖m a‖ ^ 2 ≤ 1 := (le_add_of_nonneg_right (norm_nonneg _)).trans (h a)
    have hnorm : ‖m a‖ ≤ 1 := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)
    have hdisk : ‖n a - m a ^ 2‖ ≤ 1 - ‖m a‖ ^ 2 := le_sub_iff_add_le'.mpr (h a)
    obtain ⟨p, z, hp, hz, hmass, hfirst, hsecond⟩ :=
      SecondMomentDisk.exists_four_node_law hnorm hdisk
    exact ⟨(p, z), ⟨⟨hp, hmass⟩, hz⟩, Prod.ext hfirst hsecond⟩
  let e := Fintype.equivFin Coord
  obtain ⟨g, hg, hgF⟩ := measurable_fiber_coordinates isCompact_lawDomain continuous_moments
    (hm.prodMk hn) hF _ (fun j ↦ lawCoordinate (e.symm j))
    (fun j ↦ continuous_lawCoordinate (e.symm j))
  let p (i : Fin 4) := g (e (.inl i))
  let z (i : Fin 4) (a : Ω) : ℂ := ⟨g (e (.inr (.inl i))) a, g (e (.inr (.inr i))) a⟩
  refine ⟨p, z, fun i ↦ hg (e (.inl i)), fun i ↦ ?_, fun a ↦ ?_⟩
  · exact Complex.equivRealProdCLM.toHomeomorph.toMeasurableEquiv.symm.measurable.comp
      ((hg (e (.inr (.inl i)))).prodMk (hg (e (.inr (.inr i)))))
  · obtain ⟨l, hl, hlmom, hcoords⟩ := hgF a
    have hread (j : Coord) : lawCoordinate j l = g (e j) a := by
      simpa only [Equiv.symm_apply_apply] using hcoords (e j)
    have heq : ((fun i ↦ p i a), (fun i ↦ z i a)) = l := by
      refine Prod.ext (funext fun i ↦ (hread (.inl i)).symm) (funext fun i ↦ ?_)
      exact Complex.ext (hread (.inr (.inl i))).symm (hread (.inr (.inr i))).symm
    rw [← heq] at hl hlmom
    exact ⟨hl.1.1, hl.2, hl.1.2, congrArg Prod.fst hlmom, congrArg Prod.snd hlmom⟩

end Masullo.MeasurableSecondMomentLaw
