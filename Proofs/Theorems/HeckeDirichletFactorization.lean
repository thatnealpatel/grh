module

public import Theorems.FiniteHeckeCharacterEulerProduct
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# From grouped finite Hecke denominators to Dirichlet continuation

For (3.2.1.7), p. 124, group the finite places by the rational prime below
them. A polynomial identity in each fiber suffices to identify the
right-half-plane product with the product of two Dirichlet L-functions.
-/

open Complex IsDedekindDomain NumberField Polynomial

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)

/-- The rational prime below a finite place. -/
@[expose] public noncomputable def heckeRationalPrime (v : Places) : Nat.Primes := by
  haveI : NeZero v.asIdeal := ⟨v.ne_bot⟩
  exact ⟨(v.asIdeal.under ℤ).absNorm, Nat.absNorm_under_prime v.asIdeal⟩

/-- The fiber of finite places over a rational prime. -/
@[expose] public def heckePrimeFiber (K : Type*) [Field K] [NumberField K] (p : Nat.Primes) :=
  {v : HeightOneSpectrum (𝓞 K) // heckeRationalPrime v = p}

public theorem heckePrimeFiber_under_eq_span (p : Nat.Primes) (v : heckePrimeFiber K p) :
    v.1.asIdeal.under ℤ = Ideal.span {(p.val : ℤ)} := by
  have h := congrArg Subtype.val v.2
  change (v.1.asIdeal.under ℤ).absNorm = p.val at h
  rw [← h, Int.ideal_span_absNorm_eq_self]

public noncomputable instance (p : Nat.Primes) : Fintype (heckePrimeFiber K p) := by
  classical
  letI := (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K)
    (Ideal.span {(p.val : ℤ)})).fintype
  apply Fintype.ofInjective (α := heckePrimeFiber K p) (β := (Ideal.span {(p.val : ℤ)}).primesOver (𝓞 K))
    (fun v ↦ ⟨v.1.asIdeal, v.1.isPrime, ⟨(heckePrimeFiber_under_eq_span p v).symm⟩⟩)
  intro v w h
  exact Subtype.ext (HeightOneSpectrum.ext_iff.mpr (congrArg Subtype.val h))

/-- Grouped denominator in the variable `X = p^(-s)`, with the residue-degree
power for each place. It is independent of `s`. -/
@[expose] public noncomputable def heckeRationalDenominator (χ : HeckeCharacter (𝓞 K) K)
    (p : Nat.Primes) : ℂ[X] :=
  ∏ v : heckePrimeFiber K p, (χ.localPolynomial v.1).comp (X ^ v.1.asIdeal.inertiaDeg ℤ)

private theorem rationalPrime_cpow_inertiaDeg (v : Places) (s : ℂ) :
    ((heckeRationalPrime v : ℂ) ^ (-s)) ^ v.asIdeal.inertiaDeg ℤ =
      exp (-s * (Real.log (finitePlaceNorm v) : ℂ)) := by
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  have hp : 0 < ((heckeRationalPrime v).val : ℝ) := by exact_mod_cast (heckeRationalPrime v).2.pos
  have hnorm : finitePlaceNorm v = ((heckeRationalPrime v).val : ℝ) ^ v.asIdeal.inertiaDeg ℤ := by
    unfold finitePlaceNorm
    exact_mod_cast h.symm
  rw [hnorm, Real.log_pow, ofReal_mul, ofReal_natCast]
  rw [← ofReal_natCast, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hp.ne'),
    ← ofReal_log hp.le, ← exp_nat_mul]
  congr 1
  ring

/-- If the grouped local polynomials match those of two Dirichlet characters,
their continued L-functions multiply to the given Hecke Euler product on
`Re s > 1`. The grouped polynomial premise includes every rational prime. -/
public theorem finiteHeckeCharacterEulerProduct_eq_dirichlet_of_local
    (χ : HeckeCharacter (𝓞 K) K) {m n : ℕ} [NeZero m] [NeZero n]
    (ψ : DirichletCharacter ℂ m) (η : DirichletCharacter ℂ n)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (hlocal : ∀ p : Nat.Primes, heckeRationalDenominator χ p =
      (1 - C (ψ p.val) * X) * (1 - C (η p.val) * X))
    {s : ℂ} (hs : 1 < s.re) :
    finiteHeckeCharacterEulerProduct χ s = ψ.LFunction s * η.LFunction s := by
  let f : Places → ℂ := fun v ↦
    ((χ.localPolynomial v).eval (exp (-s * (Real.log (finitePlaceNorm v) : ℂ))))⁻¹
  have hf (v : Places) : f v = finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s :=
    finiteHecke_localPolynomial_eval_inv χ v s
  have hpoint : HasProd f (finiteHeckeCharacterEulerProduct χ s) := by
    have h := HasProdLocallyUniformlyOn.hasProd (x := s)
      (finiteHeckeEulerFactor_hasProdLocallyUniformlyOn (K := K)
        (norm_finiteHeckeCoefficient_le_one χ hχ)) (show s ∈ {t : ℂ | 1 < t.re} from hs)
    rw [show finiteHeckeCharacterEulerProduct χ s = _ from tprod_congr hf]
    exact h.congr_fun hf
  have hSigma : HasProd (fun v : (Σ p : Nat.Primes, heckePrimeFiber K p) ↦ f v.2.1)
      (finiteHeckeCharacterEulerProduct χ s) :=
    (Equiv.sigmaFiberEquiv (heckeRationalPrime (K := K))).hasProd_iff.mpr hpoint
  have hP : HasProd (fun p : Nat.Primes ↦ ∏ v : heckePrimeFiber K p, f v.1)
      (finiteHeckeCharacterEulerProduct χ s) :=
    hSigma.sigma fun p ↦ hasProd_fintype (fun v : heckePrimeFiber K p ↦ f v.1)
  rw [ψ.LFunction_eq_LSeries hs, η.LFunction_eq_LSeries hs]
  have hD := (ψ.LSeries_eulerProduct_hasProd hs).mul (η.LSeries_eulerProduct_hasProd hs)
  refine hP.unique (hD.congr_fun ?_)
  intro p
  let x : ℂ := (p : ℂ) ^ (-s)
  have hp := congrArg (eval x) (hlocal p)
  have heval (v : heckePrimeFiber K p) :
      eval x ((χ.localPolynomial v.1).comp (X ^ v.1.asIdeal.inertiaDeg ℤ)) =
        eval (exp (-s * (Real.log (finitePlaceNorm v.1) : ℂ))) (χ.localPolynomial v.1) := by
    rw [eval_comp, eval_pow, eval_X]
    congr 1
    dsimp only [x]
    have hx := congrArg (fun q : Nat.Primes ↦ (q : ℂ) ^ (-s)) v.2
    exact (congrArg (· ^ v.1.asIdeal.inertiaDeg ℤ) hx).symm.trans
      (rationalPrime_cpow_inertiaDeg v.1 s)
  simp only [heckeRationalDenominator, eval_prod, heval, eval_mul, eval_sub, eval_one,
    eval_C, eval_X] at hp
  change (∏ v : heckePrimeFiber K p, f v.1) = (1 - ψ p.val * x)⁻¹ * (1 - η p.val * x)⁻¹
  dsimp only [f]
  calc
    _ = (∏ v : heckePrimeFiber K p,
        eval (exp (-s * (Real.log (finitePlaceNorm v.1) : ℂ))) (χ.localPolynomial v.1))⁻¹ :=
      Finset.prod_inv_distrib _
    _ = _ := by simpa only [mul_inv_rev, mul_comm] using congrArg Inv.inv hp

/-- The quadratic Dirichlet character of discriminant `-4`. -/
@[expose] public noncomputable def dirichletNegFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- The quadratic Dirichlet character of discriminant `5`. -/
@[expose] public noncomputable def dirichletFive : DirichletCharacter ℂ 5 :=
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)

private theorem dirichletNegFour_ne_one : dirichletNegFour ≠ 1 := by
  intro h
  have h3 := congrArg (fun χ : DirichletCharacter ℂ 4 ↦ χ (3 : ZMod 4)) h
  have hunit : IsUnit (3 : ZMod 4) := isUnit_iff_exists_inv.mpr ⟨3, by decide⟩
  change dirichletNegFour (3 : ZMod 4) = (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) at h3
  rw [MulChar.one_apply hunit] at h3
  have hx : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  norm_num [dirichletNegFour, MulChar.ringHomComp_apply, hx] at h3

private theorem dirichletFive_ne_one : dirichletFive ≠ 1 := by
  intro h
  have h2 := congrArg (fun χ : DirichletCharacter ℂ 5 ↦ χ (2 : ZMod 5)) h
  have hne : (2 : ZMod 5) ≠ 0 := by decide
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  change dirichletFive (2 : ZMod 5) = (1 : DirichletCharacter ℂ 5) (2 : ZMod 5) at h2
  rw [MulChar.one_apply hne.isUnit] at h2
  have hns : ¬ IsSquare (2 : ZMod 5) := by decide
  have hx := (quadraticChar_eq_neg_one_iff_not_one hne).mpr
    (mt (quadraticChar_one_iff_isSquare hne).mp hns)
  norm_num [dirichletFive, MulChar.ringHomComp_apply, hx] at h2

/-- The entire product of the two quadratic Dirichlet L-functions. -/
@[expose] public noncomputable def qSqrtNegFiveDirichletProduct (s : ℂ) : ℂ :=
  dirichletNegFour.LFunction s * dirichletFive.LFunction s

/-- The explicit Dirichlet product is entire, independently of any Hecke comparison. -/
public theorem differentiable_qSqrtNegFiveDirichletProduct :
    Differentiable ℂ qSqrtNegFiveDirichletProduct :=
  (DirichletCharacter.differentiable_LFunction dirichletNegFour_ne_one).mul
    (DirichletCharacter.differentiable_LFunction dirichletFive_ne_one)

/-- Specialization to the proposed entire continuation on the nontrivial class isotype.
The local comparison is a premise, not a construction of the class character. -/
public theorem finiteHeckeCharacterEulerProduct_eq_qSqrtNegFiveDirichletProduct_of_local
    (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (hlocal : ∀ p : Nat.Primes, heckeRationalDenominator χ p =
      (1 - C (dirichletNegFour p.val) * X) * (1 - C (dirichletFive p.val) * X))
    {s : ℂ} (hs : 1 < s.re) :
    finiteHeckeCharacterEulerProduct χ s = qSqrtNegFiveDirichletProduct s :=
  finiteHeckeCharacterEulerProduct_eq_dirichlet_of_local χ dirichletNegFour dirichletFive hχ hlocal hs

end Masullo
