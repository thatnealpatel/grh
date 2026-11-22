module

public import Theorems.IdeleClassRapidDecay
import Lemmas.IdeleHeckeGaussianDecay

/-! # Uniform large-norm decay of the Gaussian periodization

Specialize the absolute-sum estimate from Theorem 2.2.3.4(1), PDF p. 83,
to the corrected Gaussian from Definition 3.4.3.2, PDF p. 152. The
finite-coordinate integral support bound needs no dilation in this case.
-/

open IsDedekindDomain NumberField
open scoped Masullo

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]

local notation "I" => IdeleGroup (𝓞 K) K
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- The absolute principal series for the corrected Gaussian converges at
    every norm at least one and is uniformly `O_N(t⁻ᴺ)` there, for every
    representative of every class. -/
public theorem ideleHeckeGaussian_periodization_rapidDecay
    (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ z : IdeleClassGroup (𝓞 K) K, ‖χ z‖ = 1)
    (T : Finset V) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : I, 1 ≤ ideleNorm g →
      (Summable fun a : Kˣ ↦ ‖ideleHeckeGaussian χ hχ T (d a * g)‖) ∧
      (∑' a : Kˣ, ‖ideleHeckeGaussian χ hχ T (d a * g)‖) ≤ C * ideleNorm g ^ (-(N : ℤ)) :=
  idele_periodization_rapidDecay_of_support (ideleHeckeGaussian χ hχ T) 1
    (fun _ hg v ↦ by simpa only [one_mul] using
      norm_finite_le_one_of_ideleHeckeGaussian_ne_zero χ hχ T hg v)
    (exists_ideleHeckeGaussian_norm_mul_pow_le χ hχ T) N

end Masullo
