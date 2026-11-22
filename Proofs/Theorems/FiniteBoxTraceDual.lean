module

public import Lemmas.FiniteCompletionCodifferentFourier
public import Lemmas.FiniteIdeleIdealMembership
public import Theorems.ArchimedeanIdealDual
public import Theorems.FiniteCompletionDifferentExtension
public import Theorems.NumberFieldDiagonalPhase

/-! # Diagonal Fourier support and phase of a finite adelic box

Masullo, Example A.3.1.10, (A.3.1.8), PDF p. 558, uses the local inverse
different for the support of the centered integer-ring transform. Example
A.3.1.11, pp. 558–559, concerns the orthogonal of the S-integer lattice, not
the diagonal frequencies of an arbitrary finite box. For the lattice proof
of Theorem 2.2.3.2, p. 82, we identify that frequency set with the rational
trace dual of the box's ideal. On this set the phase at a local translation
center is unchanged on replacing the center by a diagonal representative.
The finite Fourier factors use the positive phases under the corrected
pairing (compare (2.2.4.32), p. 92). Source reading: Provisional Markdown
and numbered PDF layout.
-/

open Ideal IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped BigOperators Masullo nonZeroDivisors WithZero

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "J" => FractionalIdeal (𝓞 K)⁰ K
local notation "D" => differentIdeal ℤ (𝓞 K)
local notation "K[" v "]" => HeightOneSpectrum.adicCompletion K v
local notation "O[" v "]" => HeightOneSpectrum.adicCompletionIntegers K v
local notation "w[" v "]" => (Valued.v : Valuation K[v] ℤᵐ⁰)
local notation "k[" v "]" => algebraMap K K[v]
local notation "d[" v "]" => differentIdeal ℤ_[finiteCompletionBasePrime v] O[v]
local notation "χ[" v "]" => fun x : K[v] ↦ padicStdAddChar (finiteCompletionBasePrime v)
  (Algebra.trace ℚ_[finiteCompletionBasePrime v] K[v] x)

attribute [local instance] finiteCompletion_moduleFinite finiteCompletionIntegers_moduleFinite
  finiteCompletionIntegers_moduleFree

private theorem coordinate_ne_zero (g : Fˣ) (v : V) : g.val v ≠ 0 :=
  (FiniteAdeleRing.isUnit_iff.mp g.isUnit).1 v

-- An idele representing the different generates each of its completed ideals.
private theorem different_coordinates (h : Fˣ) (hh : (finiteIdeleIdeal K h : J) = D) :
    ∀ v : V, ∃ t : O[v], (t : K[v]) = h.val v ∧ Ideal.span {t} = d[v] := by
  have hint (v : V) : w[v] (h.val v) ≤ 1 := by
    apply (WithZero.log_le_log (finiteIdele_valuation_ne_zero h v) one_ne_zero).mp
    have hc := count_finiteIdeleIdeal h v
    rw [hh, FractionalIdeal.count_coeIdeal K v differentIdeal_ne_bot] at hc
    rw [WithZero.log_one, ← neg_nonneg, ← hc]
    exact Nat.cast_nonneg _
  obtain ⟨I, -, hI, hcoord⟩ := exists_ideal_finiteIdeleIdeal_of_integral h hint
  have hID : I = D := FractionalIdeal.coeIdeal_injective (K := K) (hI.trans hh)
  intro v
  let t : O[v] := ⟨h.val v, hint v⟩
  refine ⟨t, rfl, ?_⟩
  rw [← map_globalDifferent_eq_finiteCompletionDifferent v, ← hID]
  ext z
  rw [hcoord, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩
    rw [show ((t * q : O[v]) : K[v]) = (t : K[v]) * (q : K[v]) from rfl, w[v].map_mul]
    exact mul_le_of_le_one_right zero_le q.property
  · intro hz
    let q : O[v] := ⟨(z : K[v]) / h.val v, by
      change w[v] ((z : K[v]) / h.val v) ≤ 1
      rwa [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr (finiteIdele_valuation_ne_zero h v))]⟩
    refine ⟨q, Subtype.ext ?_⟩
    change (z : K[v]) = h.val v * ((z : K[v]) / h.val v)
    rw [mul_div_cancel₀ _ (coordinate_ne_zero h v)]

private theorem valuation_inv_coordinate (g : Fˣ) (v : V) :
    w[v] ((g⁻¹ : Fˣ).val v) = (w[v] (g.val v))⁻¹ := by
  have h : g.val v * (g⁻¹ : Fˣ).val v = 1 := by
    change ((g * g⁻¹ : Fˣ).val v) = 1
    rw [mul_inv_cancel]
    rfl
  rw [eq_inv_of_mul_eq_one_right h, map_inv₀]

/-- The diagonal frequencies annihilating the finite box `g ∏ O_v` are
exactly the rational trace dual of the fractional ideal of `g`. -/
public theorem mem_traceDual_finiteIdeleIdeal_iff (g : Fˣ) (y : K) :
    y ∈ FractionalIdeal.dual ℤ ℚ (finiteIdeleIdeal K g : J) ↔
      ∀ v : V, ∀ t : O[v], χ[v] (k[v] y * (g.val v * (t : K[v]))) = 1 := by
  have hD : (D : J) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  obtain ⟨h, hh⟩ := finiteIdeleIdeal_surjective K (Units.mk0 (D : J) hD)
  have hh' : (finiteIdeleIdeal K h : J) = D := congrArg Units.val hh
  have hdual : FractionalIdeal.dual ℤ ℚ (finiteIdeleIdeal K g : J) =
      (finiteIdeleIdeal K (h * g)⁻¹ : J) := by
    rw [fractionalIdeal_traceDual_eq, map_inv, map_mul, mul_inv_rev, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hh', mul_comm]
  rw [hdual, mem_finiteIdeleIdeal_iff]
  apply forall_congr'
  intro v
  obtain ⟨t, ht, htD⟩ := different_coordinates h hh' v
  -- Absorb the radius into the frequency, then use the local different
  -- generator to turn annihilation into an integrality test.
  simp only [← mul_assoc]
  rw [finiteCompletion_traceChar_trivial_iff, finiteCompletion_traceDual_eq_inv_differentIdeal,
    FractionalIdeal.mem_coeToSubmodule, finiteCompletion_mem_codifferent_iff v t htD]
  change w[v] (k[v] y) ≤ w[v] (((h * g)⁻¹ : Fˣ).val v) ↔ w[v] ((t : K[v]) * (k[v] y * g.val v)) ≤ 1
  rw [valuation_inv_coordinate, ← one_div, le_div_iff₀
    (pos_iff_ne_zero.mpr (finiteIdele_valuation_ne_zero (h * g) v)), ← w[v].map_mul, ht]
  change w[v] (k[v] y * (h.val v * g.val v)) ≤ 1 ↔ _
  rw [mul_left_comm]

/-- On the diagonal trace-dual support the positive finite Fourier phase of
a translated box is the positive Archimedean shift phase. The product is
finite in the sense that all but finitely many factors are one. -/
public theorem finiteBox_tracePhase_eq_diagonal (a : F) (g : Fˣ) (x₀ y : K)
    (hx₀ : ∀ v : V, w[v] (k[v] x₀ - a v) ≤ w[v] (g.val v))
    (hy : y ∈ FractionalIdeal.dual ℤ ℚ (finiteIdeleIdeal K g : J)) :
    (fun v : V ↦ χ[v] (k[v] y * a v)).HasFiniteMulSupport ∧
      (∏ᶠ v : V, χ[v] (k[v] y * a v)) =
        Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ K (x₀ * y) : ℂ)) := by
  have hfactor (v : V) : χ[v] (k[v] y * a v) = finiteCompletionDiagonalPhase v (x₀ * y) := by
    let q : O[v] := ⟨(k[v] x₀ - a v) / g.val v, by
      change w[v] ((k[v] x₀ - a v) / g.val v) ≤ 1
      rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr (finiteIdele_valuation_ne_zero g v))]
      exact hx₀ v⟩
    have hann := (mem_traceDual_finiteIdeleIdeal_iff g y).mp hy v q
    have hq : g.val v * (q : K[v]) = k[v] x₀ - a v :=
      mul_div_cancel₀ _ (coordinate_ne_zero g v)
    have hadd (b c : K[v]) : χ[v] (b + c) = χ[v] b * χ[v] c := by
      simp only [map_add, AddChar.map_add_eq_mul]
    rw [finiteCompletionDiagonalPhase_apply, map_mul, mul_comm (k[v] x₀),
      ← sub_add_cancel (k[v] x₀) (a v), mul_add, ← hq]
    change χ[v] (k[v] y * a v) = χ[v] (k[v] y * (g.val v * (q : K[v])) + k[v] y * a v)
    rw [hadd, hann, one_mul]
  exact ⟨by simpa only [hfactor] using finiteCompletionDiagonalPhase_hasFiniteMulSupport (x₀ * y),
    (finprod_congr hfactor).trans (finiteCompletionDiagonalPhase_finprod (x₀ * y))⟩

end Masullo
