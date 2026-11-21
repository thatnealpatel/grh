module

public import Lemmas.RationalIntegralAdeles

/-! # The rational adelic pairing on the integral-finite stage -/

open NumberField IsDedekindDomain Set
open scoped Classical

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K" => RationalFiniteIntegers
local notation "W" => (rationalIntegralAdeles : Set A)
local notation "χ" => rationalAdeleAddChar
local notation "j" => rationalAdeleIntegralEmbedding
local notation "eᵣ" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

private theorem real_mul (x y : A) : rationalAdeleReal (x * y) =
    rationalAdeleReal x * rationalAdeleReal y := by
  simp only [rationalAdeleReal_apply]
  exact map_mul eᵣ _ _

private theorem real_embedding (z : ℝ × K) : rationalAdeleReal (j z) = z.1 :=
  rationalIntegralAdelesHomeomorph_real z

/-- Integral finite coordinates contribute only the real phase. -/
public theorem rationalAdeleAddChar_mul_of_integral {x y : A} (hx : x ∈ W) (hy : y ∈ W) :
    χ (x * y) = Complex.exp (2 * Real.pi * Complex.I *
      ((rationalAdeleReal x * rationalAdeleReal y : ℝ) : ℂ)) := by
  rw [rationalAdeleAddChar_eq_prod _ ∅, Finset.prod_empty, mul_one, real_mul]
  exact fun v _ ↦ (v.adicCompletionIntegers ℚ).mul_mem _ _ (hx v) (hy v)

/-- A single finite coordinate witnesses nontriviality on the compact integral
factor, without translating in the real direction. -/
public theorem exists_rationalIntegralAdele_phase_ne_one {y : A} (hy : y ∉ W) :
    ∃ u ∈ W, rationalAdeleReal u = 0 ∧ χ (u * y) ≠ 1 := by
  have h : ¬ ∀ v : V, y.2 v ∈ v.adicCompletionIntegers ℚ := hy
  obtain ⟨v, hv⟩ := not_forall.mp h
  let z : ℝ × K := (0, Pi.single v 1)
  refine ⟨j z, (rationalIntegralAdelesHomeomorph z).property, real_embedding z, ?_⟩
  have hcoord (w : V) : (j z).2 w = (z.2 w : w.adicCompletion ℚ) :=
    rationalIntegralAdelesHomeomorph_finite z w
  have hzero (w : V) (hw : w ∉ ({v} : Finset V)) : (j z * y).2 w = 0 := by
    change (j z).2 w * y.2 w = 0
    rw [hcoord, show z.2 w = 0 from Pi.single_eq_of_ne (by simpa using hw) _, Subring.coe_zero,
      zero_mul]
  have hone : (j z * y).2 v = y.2 v := by
    change (j z).2 v * y.2 v = y.2 v
    rw [hcoord, show z.2 v = 1 from Pi.single_eq_same _ _, Subring.coe_one, one_mul]
  rw [rationalAdeleAddChar_eq_prod _ {v} (fun w hw ↦ by rw [hzero w hw]; exact zero_mem _),
    real_mul, real_embedding, show z.1 = 0 from rfl, zero_mul, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul, Finset.prod_singleton, hone]
  exact mt (rationalLocalFiniteAddChar_eq_one_iff v _).mp hv

end Masullo
