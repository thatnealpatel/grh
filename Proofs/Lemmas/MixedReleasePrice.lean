module

public import Lemmas.FullAtomBernsteinCell
public import Mathlib.Probability.Kernel.Basic

/-!
# Mixed constant-law and measurable-cell prices

Sources: `63af631ef047:.godel/bob/five-release-independent-price-33.md:37–78`
(the affine contribution and the two sorts of cell bounds) and
`cc368e8d4ef4:.godel/bob/five-release-batch-decision.md:33–43` (local replacement).
Owning check session: `01a20fbf-64d4-7ae0-ac41-09f991160e63`.

Scope: a generic certificate for a score decomposed into finitely many slabs and a
common tail. An unreleased slab uses one probability law; a released slab sums
measurable-cell prices over its subdivision. Coefficient support caps, released
control caps, and the common tail allowance are inputs. The certificate acts on
the cellwise score decomposition; it does not verify mesh geometry or give a
numerical exclusion.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory

namespace Masullo.MixedReleasePrice

open FullAtomBernsteinCell (mass score)
open MeasurableBernsteinCell (atomPayoff)

noncomputable section

/-- The score integrated against the cell's Lebesgue measure and its law at each time. -/
@[expose] public def cellScore (a b : ℝ → ℝ) (l r : ℝ)
    (ν : Kernel (Icc l r) (Icc (0 : ℝ) 1)) : ℝ :=
  ∫ t : Icc l r, (∫ u, score a b t u ∂ν t) ∂(volume.comap Subtype.val)

/-- The scalar atom polynomial of a cell, with the time coefficients integrated first. -/
@[expose] public def integratedPolynomial (a b : ℝ → ℝ) (l r u : ℝ) : ℝ :=
  let X := 2 * u ^ 2 - 1
  (∫ t in Icc l r, mass t) * u - (∫ t in Icc l r, a t) * X -
    (∫ t in Icc l r, b t) * (4 * X ^ 3 - 3 * X)

private abbrev Atom := Icc (0 : ℝ) 1
private abbrev atomX (u : Atom) : ℝ := 2 * (u : ℝ) ^ 2 - 1
private abbrev atomT (u : Atom) : ℝ := 4 * atomX u ^ 3 - 3 * atomX u

private theorem continuous_mass : Continuous mass := by
  have h : mass = fun t ↦ max t 0 * Real.exp (-t) := by
    funext t
    by_cases ht : 0 ≤ t
    · simp [mass, ht]
    · simp [mass, ht, max_eq_right (not_le.mp ht).le]
  rw [h]
  exact (continuous_id.max continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)

/-- For a single law on the entire cell, integrate the time coefficients before
averaging the resulting polynomial against that same law. -/
public theorem const_cellScore_eq_integral_polynomial {a b : ℝ → ℝ} {l r : ℝ}
    (ha : IntegrableOn a (Icc l r)) (hb : IntegrableOn b (Icc l r))
    (ρ : Measure (Icc (0 : ℝ) 1)) [IsProbabilityMeasure ρ] :
    cellScore a b l r (Kernel.const _ ρ) = ∫ u, integratedPolynomial a b l r u ∂ρ := by
  let : CompactSpace Atom := isCompact_iff_compactSpace.mp isCompact_Icc
  have atomIntegrable {f : Atom → ℝ} (hf : Continuous f) : Integrable f ρ :=
    integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
  have hu := atomIntegrable continuous_subtype_val
  have hx : Integrable atomX ρ := atomIntegrable (by fun_prop)
  have hy : Integrable atomT ρ := atomIntegrable (by fun_prop)
  have integrateAtom (m p q : ℝ) :
      (∫ u : Atom, m * u - p * atomX u - q * atomT u ∂ρ) =
        m * (∫ u : Atom, (u : ℝ) ∂ρ) - p * (∫ u : Atom, atomX u ∂ρ) -
          q * (∫ u : Atom, atomT u ∂ρ) := by
    rw [integral_sub (f := fun u : Atom ↦ m * u - p * atomX u)
      ((hu.const_mul m).sub (hx.const_mul p)) (hy.const_mul q),
      integral_sub (hu.const_mul m) (hx.const_mul p)]
    simp only [integral_const_mul]
  have hscore (t : ℝ) (u : Atom) : score a b t u =
      mass t * u - a t * atomX u - b t * atomT u := by
    unfold score atomPayoff
    ring
  simp only [cellScore, Kernel.const_apply, hscore, integratedPolynomial, integrateAtom]
  let EU := ∫ u : Atom, (u : ℝ) ∂ρ
  let EX := ∫ u : Atom, atomX u ∂ρ
  let ET := ∫ u : Atom, atomT u ∂ρ
  rw [integral_subtype_comap measurableSet_Icc (fun t ↦ mass t * EU - a t * EX - b t * ET)]
  have hm : IntegrableOn mass (Icc l r) := continuous_mass.integrableOn_Icc
  rw [integral_sub (f := fun t ↦ mass t * EU - a t * EX)
    ((hm.mul_const EU).sub (ha.mul_const EX)) (hb.mul_const ET),
    integral_sub (hm.mul_const EU) (ha.mul_const EX)]
  simp only [integral_mul_const, EU, EX, ET]

/-- A uniform support cap for the integrated polynomial bounds the entire
constant-law price. This comparison preserves probability mass one. -/
public theorem const_cellScore_le {a b : ℝ → ℝ} {l r cap : ℝ}
    (ha : IntegrableOn a (Icc l r)) (hb : IntegrableOn b (Icc l r))
    (ρ : Measure (Icc (0 : ℝ) 1)) [IsProbabilityMeasure ρ]
    (hcap : ∀ u ∈ Icc (0 : ℝ) 1, integratedPolynomial a b l r u ≤ cap) :
    cellScore a b l r (Kernel.const _ ρ) ≤ cap := by
  rw [const_cellScore_eq_integral_polynomial ha hb]
  let : CompactSpace Atom := isCompact_iff_compactSpace.mp isCompact_Icc
  have hc : Continuous (fun u : Atom ↦ integratedPolynomial a b l r u) := by
    unfold integratedPolynomial
    fun_prop
  have hi : Integrable (fun u : Atom ↦ integratedPolynomial a b l r u) ρ :=
    integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  calc
    _ ≤ ∫ _ : Atom, cap ∂ρ := integral_mono hi (integrable_const _) (fun u ↦ hcap u u.property)
    _ = cap := by simp

/-- An unsplit slab and its ordinary atom-support cap. No particular law is
needed to include this cap in the all-ordinary base. -/
public structure OrdinaryCell (a b : ℝ → ℝ) where
  left : ℝ
  right : ℝ
  a_integrable : IntegrableOn a (Icc left right)
  b_integrable : IntegrableOn b (Icc left right)
  cap : ℝ
  support_le : ∀ u ∈ Icc (0 : ℝ) 1, integratedPolynomial a b left right u ≤ cap

/-- A piece of a released slab: a cell on one mass branch, with its measurable
Markov law and the data for the full-score Bernstein price. -/
public structure ReleasedCell (a b : ℝ → ℝ) where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
  one_branch : right ≤ 0 ∨ 0 ≤ left
  a_smooth : ContDiffOn ℝ 3 a (Icc left right)
  b_smooth : ContDiffOn ℝ 3 b (Icc left right)
  law : Kernel (Icc left right) (Icc (0 : ℝ) 1)
  markov_law : IsMarkovKernel law
  leftCap : ℝ
  middleCap : ℝ
  rightCap : ℝ
  angularCap : ℝ
  angular_le : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Ioo left right,
    |iteratedDeriv 3 (fun s ↦ atomPayoff a b s (2 * u ^ 2 - 1)) t| ≤ angularCap
  left_le : ∀ u ∈ Icc (0 : ℝ) 1, score a b left u ≤ leftCap
  middle_le : ∀ u ∈ Icc (0 : ℝ) 1,
    2 * score a b ((left + right) / 2) u - (score a b left u + score a b right u) / 2 ≤ middleCap
  right_le : ∀ u ∈ Icc (0 : ℝ) 1, score a b right u ≤ rightCap

/-- A released cell pays for the three supports and the full remainder,
including the mass allowance on the nonnegative branch. -/
@[expose] public def ReleasedCell.price {a b : ℝ → ℝ} (c : ReleasedCell a b) : ℝ :=
  (c.right - c.left) * (c.leftCap + c.middleCap + c.rightCap) / 3 +
    (c.angularCap + (if 0 ≤ c.left then 3 * Real.exp (-c.left / 2) else 0)) *
      (c.right - c.left) ^ 4 / 192

public theorem ReleasedCell.cellScore_le {a b : ℝ → ℝ} (c : ReleasedCell a b) :
    cellScore a b c.left c.right c.law ≤ c.price := by
  let _ := c.markov_law
  exact FullAtomBernsteinCell.integral_score_le c.left_lt_right c.one_branch c.a_smooth c.b_smooth
    c.law c.angular_le c.left_le c.middle_le c.right_le

/-- Bound a mixed score by the all-ordinary upper plus one local replacement
per released slab. Each subtraction uses the very same cap included in the
base. The affine constant remains intact, and the tail upper is independent of
the release choice. On a released slab the score and price both sum over the
specified fine cells; no constant law is assumed there. -/
public theorem mixed_score_le_replacement {ι : Type*} [DecidableEq ι] {a b : ℝ → ℝ}
    (slabs released : Finset ι) (hsubset : released ⊆ slabs)
    (ordinary : ι → OrdinaryCell a b)
    (law : (slabs \ released : Finset ι) → Measure (Icc (0 : ℝ) 1))
    (hLaw : ∀ i, IsProbabilityMeasure (law i))
    {κ : released → Type*} (mesh : (i : released) → Finset (κ i))
    (piece : (i : released) → κ i → ReleasedCell a b)
    (affine tail tailUpper : ℝ) (hTail : tail ≤ tailUpper) :
    affine + tail +
        (∑ i ∈ (slabs \ released).attach,
          cellScore a b (ordinary i).left (ordinary i).right (Kernel.const _ (law i))) +
        (∑ i ∈ released.attach, ∑ j ∈ mesh i,
          cellScore a b (piece i j).left (piece i j).right (piece i j).law) ≤
      (affine + tailUpper + ∑ i ∈ slabs, (ordinary i).cap) +
        ∑ i ∈ released.attach, ((∑ j ∈ mesh i, (piece i j).price) - (ordinary i).cap) := by
  have hOrd :
      (∑ i ∈ (slabs \ released).attach,
        cellScore a b (ordinary i).left (ordinary i).right (Kernel.const _ (law i))) ≤
      ∑ i ∈ (slabs \ released).attach, (ordinary i).cap := by
    apply Finset.sum_le_sum
    intro i _
    let _ := hLaw i
    exact const_cellScore_le (ordinary i).a_integrable (ordinary i).b_integrable
      (law i) (ordinary i).support_le
  have hRel :
      (∑ i ∈ released.attach, ∑ j ∈ mesh i,
        cellScore a b (piece i j).left (piece i j).right (piece i j).law) ≤
      ∑ i ∈ released.attach, ∑ j ∈ mesh i, (piece i j).price :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (piece i j).cellScore_le
  calc
    _ ≤ affine + tailUpper + (∑ i ∈ (slabs \ released).attach, (ordinary i).cap) +
        (∑ i ∈ released.attach, ∑ j ∈ mesh i, (piece i j).price) :=
      add_le_add (add_le_add (add_le_add (le_refl affine) hTail) hOrd) hRel
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_attach (slabs \ released) (fun i ↦ (ordinary i).cap),
        Finset.sum_attach released (fun i ↦ (ordinary i).cap),
        ← Finset.sum_sdiff (f := fun i ↦ (ordinary i).cap) hsubset]
      ring

end

end Masullo.MixedReleasePrice
