module

public import Theorems.RationalAdeleCharacter

/-! # Detecting finite coordinates by inverse prime powers -/

open NumberField IsDedekindDomain
open scoped Padic ComplexConjugate

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "pOf" => Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
local notation "F" v => HeightOneSpectrum.adicCompletion ℚ v
local notation "O" v => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "realEquiv" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

private theorem inv_prime_pow_mem_integral {v w : V} (h : w ≠ v) (n : ℕ) :
    algebraMap ℚ (F w) ((pOf v : ℚ) ^ n)⁻¹ ∈ O w := by
  apply (rationalLocalFiniteAddChar_eq_one_iff w _).mp
  rw [rationalLocalFiniteAddChar_rat, ← one_div]
  have hphase := rationalPadicPhase_primePower_eq_one_of_ne ((pOf).injective.ne h) n 1
  rw [Nat.cast_one] at hphase
  rw [hphase, map_one]

private theorem eq_zero_of_integral_prime_tests (v : V) (x : F v)
    (h : ∀ n : ℕ, x * algebraMap ℚ (F v) ((pOf v : ℚ) ^ n)⁻¹ ∈ O v) : x = 0 := by
  let p := pOf v
  let : Fact (p : ℕ).Prime := ⟨p.property⟩
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let y : ℚ_[(p : ℕ)] := e x
  apply e.injective
  rw [map_zero]
  change y = 0
  by_contra hy
  -- For nonzero y, the valuation of y / p^n is v_p(y) - n.
  have hn (n : ℕ) : 0 ≤ y.valuation - (n : ℤ) := by
    have hm := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo (h n)
    change e (x * algebraMap ℚ (F v) ((p : ℚ) ^ n)⁻¹) ∈ PadicInt.subring p at hm
    rw [PadicInt.mem_subring_iff, Padic.norm_le_one_iff_val_nonneg] at hm
    rw [map_mul, AlgHomClass.commutes] at hm
    change 0 ≤ (y * ((((p : ℚ) ^ n)⁻¹ : ℚ) : ℚ_[(p : ℕ)])).valuation at hm
    push_cast at hm
    have hp : (p : ℚ_[(p : ℕ)]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
    simpa only [Padic.valuation_mul hy (inv_ne_zero (pow_ne_zero n hp)),
      Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p, mul_one, sub_eq_add_neg] using hm
  have hlarge := hn (y.valuation.natAbs + 1)
  omega

/-- A real-zero adele with integral finite part is detected place by place
    by testing at diagonal inverse prime powers. -/
public theorem rationalAdele_eq_zero_of_prime_tests (a : A)
    (hreal : rationalAdeleReal a = 0) (hint : ∀ v : V, a.2 v ∈ O v)
    (htest : ∀ (v : V) (n : ℕ),
      rationalAdeleAddChar (a * algebraMap ℚ A ((pOf v : ℚ) ^ n)⁻¹) = 1) : a = 0 := by
  classical
  refine Prod.ext ?_ (FiniteAdeleRing.ext ℚ fun v ↦ ?_)
  · funext w
    rw [Subsingleton.elim w Rat.infinitePlace]
    rw [rationalAdeleReal_apply] at hreal
    exact (realEquiv).injective (hreal.trans (map_zero realEquiv).symm)
  · change a.2 v = 0
    apply eq_zero_of_integral_prime_tests v (a.2 v)
    intro n
    let b := a * algebraMap ℚ A ((pOf v : ℚ) ^ n)⁻¹
    have hbReal : rationalAdeleReal b = 0 := by
      rw [rationalAdeleReal_apply] at hreal ⊢
      change realEquiv (a.1 Rat.infinitePlace * _) = 0
      rw [map_mul, hreal, zero_mul]
    have hbIntegral (w : V) (hw : w ∉ ({v} : Finset V)) : b.2 w ∈ O w :=
      (O w).mul_mem _ _ (hint w) (inv_prime_pow_mem_integral (by simpa using hw) n)
    have hb := htest v n
    rw [rationalAdeleAddChar_eq_prod b {v} hbIntegral, hbReal] at hb
    apply (rationalLocalFiniteAddChar_eq_one_iff v (b.2 v)).mp
    simpa using hb

end Masullo
