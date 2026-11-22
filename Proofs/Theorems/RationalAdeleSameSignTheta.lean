module

public import Theorems.RationalAdeleBoxThetaInversion

/-! # Rational theta inversion with the same-sign character

Use the positive real and positive finite characters of Examples A.3.1.5–8,
pp. 557–558, and conjugate their product in the integral as in (2.2.4.32),
p. 92. This keeps the additive Haar measure unchanged but reflects the
finite frequency. In the box-sum form of (2.2.3.2), p. 82, the spatial
sum is consequently evaluated at the finite-sign idele times the original idele.
-/

open NumberField IsDedekindDomain MeasureTheory Filter
open scoped BigOperators ComplexConjugate SchwartzMap

namespace Masullo

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "J" => IdeleGroup (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "Cq" => A ⧸ rationalDiagonal
local notation "ιˣ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ
local notation "pOf" => Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
local notation "realEquiv" =>
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

/-- The idele with infinite component one and with every finite component minus one. -/
@[expose] public noncomputable def rationalAdeleFiniteSign : J where
  val := (1, -1)
  inv := (1, -1)
  val_inv := by
    change (1 * 1, (-1) * (-1)) = ((1, 1) : A)
    simp
  inv_val := by
    change (1 * 1, (-1) * (-1)) = ((1, 1) : A)
    simp

local notation "σ" => rationalAdeleFiniteSign

@[simp] public theorem rationalAdeleFiniteSign_mul_self : σ * σ = 1 := by
  apply Units.ext
  exact Units.val_inv σ

@[simp] public theorem rationalAdeleFiniteSign_inv : σ⁻¹ = σ :=
  inv_eq_of_mul_eq_one_left rationalAdeleFiniteSign_mul_self

@[simp] public theorem ideleNorm_rationalAdeleFiniteSign : ideleNorm σ = 1 := by
  rw [ideleNorm_apply, AdeleRing.norm_apply_of_isUnit (Units.isUnit σ)]
  change (∏ v : InfinitePlace ℚ, ‖(1 : v.Completion)‖ ^ v.mult) *
    (∏ᶠ v : V, ‖(-1 : v.adicCompletion ℚ)‖) = 1
  simp only [norm_one, norm_neg, one_pow, Finset.prod_const_one, finprod_one, one_mul]

/-- The positive real character times the positive finite character product. -/
public noncomputable def rationalAdeleSameSignAddChar : AddChar A ℂ where
  toFun a := Complex.exp (2 * Real.pi * Complex.I * (rationalAdeleReal a : ℂ)) *
    conj (rationalFiniteAdeleAddChar a.2)
  map_zero_eq_one' := by
    have h : rationalAdeleReal (0 : A) = 0 := by
      rw [rationalAdeleReal_apply]
      exact map_zero realEquiv
    simp [h]
  map_add_eq_mul' a b := by
    have hreal : rationalAdeleReal (a + b) = rationalAdeleReal a + rationalAdeleReal b := by
      simp only [rationalAdeleReal_apply]
      exact map_add realEquiv _ _
    simp only [hreal, Complex.ofReal_add, mul_add, Complex.exp_add]
    change _ * conj (rationalFiniteAdeleAddChar (a.2 + b.2)) = _
    rw [AddChar.map_add_eq_mul, map_mul]
    ac_rfl

/-- The finite factors are exactly the positive standard characters, with any set
containing all nonintegral places serving as the product index. -/
public theorem rationalAdeleSameSignAddChar_eq_prod (a : A) (S : Finset V)
    (hS : ∀ v ∉ S, a.2 v ∈ v.adicCompletionIntegers ℚ) :
    rationalAdeleSameSignAddChar a =
      Complex.exp (2 * Real.pi * Complex.I * (rationalAdeleReal a : ℂ)) *
        ∏ v ∈ S, @padicStdAddChar (pOf v : ℕ) ⟨(pOf v).property⟩
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a.2 v)) := by
  change _ * conj (rationalFiniteAdeleAddChar a.2) = _
  rw [rationalFiniteAdeleAddChar_eq_prod _ S hS, map_prod]
  simp only [rationalLocalFiniteAddChar_apply, Complex.conj_conj]

private theorem rationalAdeleSameSignAddChar_eq (a : A) :
    rationalAdeleSameSignAddChar a = rationalAdeleAddChar ((σ : A) * a) := by
  classical
  let w : A := (σ : A) * a
  let S := (eventually_cofinite.mp w.2.cofinite_mem_adicCompletionIntegers).toFinset
  have hS : ∀ v ∉ S, w.2 v ∈ v.adicCompletionIntegers ℚ := by
    intro v hv
    simpa [S] using hv
  have hreal : rationalAdeleReal w = rationalAdeleReal a := by
    simp only [rationalAdeleReal_apply]
    change realEquiv (1 * a.1 Rat.infinitePlace) = _
    rw [one_mul]
  have hfinite : w.2 = -a.2 := neg_one_mul _
  change rationalAdeleSameSignAddChar a = rationalAdeleAddChar w
  rw [rationalAdeleAddChar_eq_prod w S hS, ← rationalFiniteAdeleAddChar_eq_prod w.2 S hS,
    hreal, hfinite, AddChar.map_neg_eq_inv,
    Complex.inv_eq_conj (norm_rationalFiniteAdeleAddChar _)]
  rfl

/-- Conjugating the same-sign product gives the existing kernel at the
frequency reflected only at the finite places. -/
public theorem rationalAdeleSameSignKernel_eq (z y : A) :
    conj (rationalAdeleSameSignAddChar (z * y)) =
      conj (rationalAdeleAddChar (z * ((σ : A) * y))) := by
  rw [rationalAdeleSameSignAddChar_eq, mul_left_comm (σ : A) z]

set_option linter.concreteInstances false

variable [MeasurableSpace A] [BorelSpace A]

/-- The Fourier integral with the conjugated same-sign character product. -/
@[expose] public noncomputable def rationalAdeleSameSignFourier (f : A → ℂ) (y : A) : ℂ :=
  ∫ z, f z * conj (rationalAdeleSameSignAddChar (z * y)) ∂rationalAdeleAddHaar

/-- This is a change of frequency, with no change of integration variable. -/
public theorem rationalAdeleSameSignFourier_eq (f : A → ℂ) (y : A) :
    rationalAdeleSameSignFourier f y = rationalAdeleFourier f ((σ : A) * y) := by
  unfold rationalAdeleSameSignFourier rationalAdeleFourier
  congr 1
  funext z
  rw [rationalAdeleSameSignKernel_eq]

@[simp] public theorem rationalAdeleSameSignFourier_zero (f : A → ℂ) :
    rationalAdeleSameSignFourier f 0 = rationalAdeleFourier f 0 := by
  rw [rationalAdeleSameSignFourier_eq, mul_zero]

private theorem fourier_theta_term_eq (f : A → ℂ) (k : J) (q : ℚˣ) :
    rationalAdeleSameSignFourier f ((ιˣ q * k : J) : A) =
      rationalAdeleFourier f ((ιˣ q * (σ * k) : J) : A) := by
  rw [rationalAdeleSameSignFourier_eq, ← Units.val_mul, mul_left_comm σ]

private theorem fourier_theta_eq (f : A → ℂ) (k : J) :
    rationalAdeleTheta (rationalAdeleSameSignFourier f) k =
      rationalAdeleTheta (rationalAdeleFourier f) (σ * k) := by
  simp only [rationalAdeleTheta, fourier_theta_term_eq]

variable {I : Type*} (s : Finset I) (c : I → ℂ) (b : I → 𝓢(ℝ, ℂ))
  (a : I → A) (g : I → J) (k : J)

local notation "f" => rationalAdeleBoxSum s c b a g

/-- Both nonzero sums in the same-sign formula converge absolutely. -/
public theorem summable_norm_rationalAdeleBoxSum_sameSign_theta :
    Summable (fun q : ℚˣ ↦ ‖f ((ιˣ q * (σ * k) : J) : A)‖) ∧
      Summable (fun q : ℚˣ ↦ ‖rationalAdeleSameSignFourier f ((ιˣ q * k⁻¹ : J) : A)‖) := by
  simpa only [fourier_theta_term_eq, mul_inv_rev, rationalAdeleFiniteSign_inv, mul_comm k⁻¹ σ]
    using summable_norm_rationalAdeleBoxSum_theta s c b a g (σ * k)

variable [MeasurableSpace Cq] [BorelSpace Cq]

/-- For the same-sign Fourier kernel the spatial sum is reflected, while the
inverse idele on the Fourier side, the norm factor, and both zero modes keep
their original form. -/
public theorem rationalAdeleBoxSum_sameSign_theta_inversion :
    rationalAdeleTheta f (σ * k) =
      (ideleNorm k)⁻¹ • rationalAdeleTheta (rationalAdeleSameSignFourier f) k⁻¹ +
        (ideleNorm k)⁻¹ • rationalAdeleSameSignFourier f 0 - f 0 := by
  have h := rationalAdeleBoxSum_theta_inversion s c b a g (σ * k)
  rw [map_mul, ideleNorm_rationalAdeleFiniteSign, one_mul, mul_inv_rev,
    rationalAdeleFiniteSign_inv, mul_comm k⁻¹ σ, ← fourier_theta_eq,
    ← rationalAdeleSameSignFourier_zero] at h
  exact h

end Masullo
