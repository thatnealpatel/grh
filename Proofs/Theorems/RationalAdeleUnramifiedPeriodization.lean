module

public import Theorems.RationalAdeleWeil
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Lemmas.SchwartzLatticeTranslates
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Indicator

/-!
# Periodization of the rational unramified Schwartz tensor

For the adelic test `b ⊗ ∏ₚ 𝟙_{ℤₚ}`, the diagonal translates of an integral-finite
adele reduce to a real integer lattice sum. Clearing finite denominators and
reindexing gives absolute convergence at every adele. This treats the additive
periodization in Masullo's Lemma 2.2.2.1(1), pp. 77–78, at `g = 1`, with the
zero summand included. The Fourier-side hypothesis of Poisson summation is separate.
-/

open MeasureTheory NumberField Set Topology
open scoped Classical SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cq" => A ⧸ rationalDiagonal
local notation "π" => (QuotientAddGroup.mk : A → Cq)
local notation "ι" => algebraMap ℚ A

/-- The unramified tensor with archimedean factor `b` and the integral-ball
indicator at every finite place. -/
@[expose] public noncomputable def rationalAdeleUnramified (b : 𝓢(ℝ, ℂ)) : A → ℂ :=
  (rationalIntegralAdeles : Set A).indicator (fun a ↦ b (rationalAdeleReal a))

public theorem continuous_rationalAdeleUnramified (b : 𝓢(ℝ, ℂ)) :
    Continuous (rationalAdeleUnramified b) :=
  (show IsClopen (rationalIntegralAdeles : Set A) from
    ⟨rationalIntegralAdeles.isClosed_of_isOpen isOpen_rationalIntegralAdeles,
      isOpen_rationalIntegralAdeles⟩).continuous_indicator
    (b.continuous.comp continuous_rationalAdeleReal)

private noncomputable def diagonalInt (n : ℤ) : rationalDiagonal :=
  ⟨(n : A), ⟨(n : ℚ), map_intCast ι n⟩⟩

private theorem real_intCast (n : ℤ) : rationalAdeleReal (n : A) = (n : ℝ) := by
  rw [← map_intCast ι n, rationalAdeleReal_algebraMap, Rat.cast_intCast]

private theorem injective_diagonalInt : Function.Injective diagonalInt := by
  intro m n h
  have hr : rationalAdeleReal (m : A) = rationalAdeleReal (n : A) :=
    congrArg (fun d : rationalDiagonal ↦ rationalAdeleReal (d : A)) h
  rw [real_intCast, real_intCast] at hr
  exact Int.cast_injective hr

private theorem unramified_diagonalInt (b : 𝓢(ℝ, ℂ)) {a : A} (ha : a ∈ rationalIntegralAdeles)
    (n : ℤ) : rationalAdeleUnramified b (a + (diagonalInt n : A)) = b (rationalAdeleReal a + n) := by
  have hreal (x y : A) : rationalAdeleReal (x + y) = rationalAdeleReal x + rationalAdeleReal y := by
    simp only [rationalAdeleReal_apply]
    exact map_add (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) _ _
  change rationalAdeleUnramified b (a + (n : A)) = _
  rw [rationalAdeleUnramified, indicator_of_mem (rationalIntegralAdeles.add_mem ha
    (intCast_mem_rationalIntegralAdeles n)), hreal, real_intCast]

private theorem unramified_diagonal_eq_zero (b : 𝓢(ℝ, ℂ)) {a : A} (ha : a ∈ rationalIntegralAdeles)
    {d : rationalDiagonal} (hd : d ∉ range diagonalInt) : rationalAdeleUnramified b (a + (d : A)) = 0 := by
  apply indicator_of_notMem
  intro had
  obtain ⟨q, hq⟩ := d.property
  change ι q = (d : A) at hq
  have h : ι q ∈ rationalIntegralAdeles := by
    rw [hq, ← add_sub_cancel_left a (d : A)]
    exact rationalIntegralAdeles.sub_mem had ha
  obtain ⟨n, rfl⟩ := (algebraMap_mem_rationalIntegralAdeles_iff q).mp h
  exact hd ⟨n, Subtype.ext ((map_intCast ι n).symm.trans hq)⟩

/-- On the integral-finite stage, the support condition selects the
integer translates, retaining the zero index. -/
public theorem rationalAdeleComplexPeriodization_unramified_mk (b : 𝓢(ℝ, ℂ))
    {a : A} (ha : a ∈ rationalIntegralAdeles) :
    rationalAdeleComplexPeriodization (rationalAdeleUnramified b) (π a) =
      ∑' n : ℤ, b (rationalAdeleReal a + n) := by
  rw [rationalAdeleComplexPeriodization_mk]
  rw [← injective_diagonalInt.tsum_eq (fun d hd ↦ by
    by_contra h
    exact hd (unramified_diagonal_eq_zero b ha h))]
  exact tsum_congr (unramified_diagonalInt b ha)

private theorem summable_norm_rationalAdeleUnramified_add_of_mem (b : 𝓢(ℝ, ℂ))
    {a : A} (ha : a ∈ rationalIntegralAdeles) :
    Summable (fun d : rationalDiagonal ↦ ‖rationalAdeleUnramified b (a + (d : A))‖) := by
  apply (injective_diagonalInt.summable_iff (f := fun d : rationalDiagonal ↦
    ‖rationalAdeleUnramified b (a + (d : A))‖)
    (fun d hd ↦ by rw [unramified_diagonal_eq_zero b ha hd, norm_zero])).mp
  simpa only [Function.comp_def, unramified_diagonalInt b ha] using
    summable_norm_schwartz_add_int b (rationalAdeleReal a)

/-- Absolute convergence on every rational diagonal fiber, not merely almost everywhere. -/
public theorem summable_norm_rationalAdeleUnramified_add (b : 𝓢(ℝ, ℂ)) (a : A) :
    Summable (fun d : rationalDiagonal ↦ ‖rationalAdeleUnramified b (a + (d : A))‖) := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integral a
  let d₀ : rationalDiagonal := ⟨ι q, ⟨q, rfl⟩⟩
  have h := ((Equiv.addLeft d₀).summable_iff (f := fun d : rationalDiagonal ↦
    ‖rationalAdeleUnramified b (a - ι q + (d : A))‖)).mpr
    (summable_norm_rationalAdeleUnramified_add_of_mem b hq)
  convert h using 1
  ext d
  congr 2
  change a + (d : A) = a - ι q + (ι q + (d : A))
  abel

/-- The absolutely convergent periodization is continuous on the adele classes. -/
public theorem continuous_rationalAdeleComplexPeriodization_unramified (b : 𝓢(ℝ, ℂ)) :
    Continuous (rationalAdeleComplexPeriodization (rationalAdeleUnramified b)) := by
  let e := rationalAdeleQuotientEquiv
  apply e.toHomeomorph.isQuotientMap.continuous_iff.mpr
  apply (QuotientAddGroup.isQuotientMap_mk rationalIntegralDiagonal).continuous_iff.mpr
  have he : (rationalAdeleComplexPeriodization (rationalAdeleUnramified b) ∘ e.toHomeomorph) ∘
      (QuotientAddGroup.mk : rationalIntegralAdeles → rationalIntegralAdeles ⧸ rationalIntegralDiagonal) =
      fun w : rationalIntegralAdeles ↦ ∑' n : ℤ, b (rationalAdeleReal (w : A) + n) := by
    funext w
    change rationalAdeleComplexPeriodization (rationalAdeleUnramified b)
      (rationalAdeleQuotientEquiv (w : rationalIntegralAdeles ⧸ rationalIntegralDiagonal)) = _
    rw [rationalAdeleQuotientEquiv_mk, rationalAdeleComplexPeriodization_unramified_mk b w.property]
  rw [he]
  exact (continuous_tsum_schwartz_add_int b).comp
    (continuous_rationalAdeleReal.comp continuous_subtype_val)

set_option linter.concreteInstances false in
/-- The unramified tensor is integrable for normalized additive adelic Haar. -/
public theorem integrable_rationalAdeleUnramified [MeasurableSpace A] [BorelSpace A] (b : 𝓢(ℝ, ℂ)) :
    Integrable (rationalAdeleUnramified b) rationalAdeleAddHaar := by
  rw [rationalAdeleUnramified, integrable_indicator_iff isOpen_rationalIntegralAdeles.measurableSet]
  let j := rationalAdeleIntegralEmbedding
  have hj : MeasurableEmbedding j := isOpenEmbedding_rationalAdeleIntegralEmbedding.measurableEmbedding
  change Integrable (fun a ↦ b (rationalAdeleReal a))
    (rationalAdeleAddHaar.restrict (rationalIntegralAdeles : Set A))
  rw [← range_rationalAdeleIntegralEmbedding, ← hj.map_comap, hj.integrable_map_iff,
    comap_rationalAdeleAddHaar_integral]
  change Integrable (fun x : ℝ × RationalFiniteIntegers ↦
    b (rationalAdeleReal (rationalIntegralAdelesHomeomorph x : A)))
    (volume.prod rationalFiniteIntegersHaar)
  simpa only [rationalIntegralAdelesHomeomorph_real] using
    (b.integrable (μ := volume)).comp_fst rationalFiniteIntegersHaar

end Masullo
