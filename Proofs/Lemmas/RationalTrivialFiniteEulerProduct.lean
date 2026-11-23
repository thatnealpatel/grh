module

public import Theorems.FiniteHeckeCharacterEulerProduct
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # The trivial finite Hecke Euler product over the rationals -/

open IsDedekindDomain NumberField

namespace Masullo

local notation "χ₀" => (1 : HeckeCharacter (𝓞 ℚ) ℚ)

private lemma finitePlaceNorm_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    finitePlaceNorm v = ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℝ) := by
  let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  let p := Rat.HeightOneSpectrum.natGenerator v
  change (v.asIdeal.absNorm : ℝ) = (p : ℝ)
  have hspan : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
    calc
      v.asIdeal = (v.asIdeal.map e).map e.symm := by
        rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ e.bijective]
      _ = Ideal.span {(p : 𝓞 ℚ)} := by
        rw [← Rat.HeightOneSpectrum.span_natGenerator v]
        simp [Ideal.map_span, p]
  rw [hspan, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]

private lemma trivial_localFactor_rat (v : HeightOneSpectrum (𝓞 ℚ)) (s : ℂ) :
    ((HeckeCharacter.localPolynomial χ₀ v).eval
      (Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ))))⁻¹ =
      (1 - (Rat.HeightOneSpectrum.primesEquiv v : ℂ) ^ (-s))⁻¹ := by
  have hr (x : (v.adicCompletion ℚ)ˣ) :
      HeckeCharacter.restrict χ₀ v (x : v.adicCompletion ℚ) = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hu : HeckeCharacter.IsUnramifiedAt χ₀ v := HeckeCharacter.isUnramifiedAt_iff.mpr
    (fun x ↦ hr (Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom x))
  obtain ⟨π, hπ⟩ := (Valued.v : Valuation (v.adicCompletion ℚ)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  have hv : HeckeCharacter.localValue χ₀ v = 1 :=
    (hu.localValue_eq π hπ).trans (hr (Units.mk0 (π : v.adicCompletion ℚ) hπ.ne_zero))
  have he : Complex.exp (-s * (Real.log (finitePlaceNorm v) : ℂ)) =
      (Rat.HeightOneSpectrum.primesEquiv v : ℂ) ^ (-s) := by
    let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
    have hp : p ≠ 0 := (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero
    change _ = (p : ℂ) ^ (-s)
    rw [finitePlaceNorm_rat, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp),
      ← Complex.ofReal_natCast, ← Complex.ofReal_log p.cast_nonneg, mul_comm (-s)]
  rw [he]
  simp [HeckeCharacter.localPolynomial, hu, hv]

/-- The finite Euler product of the trivial Hecke character over `ℚ` is the Riemann zeta function
on the half-plane of absolute convergence. -/
public lemma finiteHeckeCharacterEulerProduct_one_rat {s : ℂ} (hs : 1 < s.re) :
    finiteHeckeCharacterEulerProduct (1 : HeckeCharacter (𝓞 ℚ) ℚ) s = riemannZeta s := by
  have hz := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).hasProd_iff.mpr
    (riemannZeta_eulerProduct_hasProd hs)
  exact (hz.congr_fun (fun v ↦ trivial_localFactor_rat v s)).tprod_eq

end Masullo
