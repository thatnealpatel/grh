module

public import Theorems.RationalLocalRadialPrimeSamples
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Prime.Int

/-!
# Sum of the rational radial finite-place terms

We supply the finite-place part of the passage from (B.4.2.10)–(11),
p. 615, to (B.4.4.16), p. 623, which footnote 27 on p. 625 asks to
explain. Masullo gives the per-place expansion and the large-place
support argument in (B.4.4.22). For a radial test the subtracted unit
shell vanishes; a bound on the log support then bounds the *prime
powers*, not just the primes. We use that bound to regroup by integers.
The locators use the pinned text extraction.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Function Set

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K[" v "]" => adicCompletion ℚ v
local notation "P[" v "]" => ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)

/-- The canonical rational finite-place term of a log-radial test, before
its subtraction in (B.4.4.16). Its integrability for compact profiles is
proved in `rationalLocalRadialFourier_eq_primeSamples`. -/
public noncomputable def rationalLocalRadialFourier (v : V) (F : ℝ → ℂ) : ℂ :=
  -(∫ ξ, (Real.log (P[v] : ℝ) : ℂ) * rationalLocalLogFourierIntegrand v
      (rationalLocalShiftedTest v (fun y : K[v]ˣ ↦ F (Real.log ‖(y : K[v])‖))) ξ
    ∂rationalLocalFieldAddHaar v)

private noncomputable def primePower (a : V × ℕ) : ℕ := P[a.1] ^ (a.2 + 1)

private theorem primePower_injective : Injective primePower := by
  intro a b hab
  obtain ⟨hp, hm⟩ := Nat.Prime.pow_inj (Rat.HeightOneSpectrum.primesEquiv a.1).property
    (Rat.HeightOneSpectrum.primesEquiv b.1).property hab
  exact Prod.ext (Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hp)) hm

private theorem mem_range_primePower {n : ℕ} (hn : IsPrimePow n) : n ∈ range primePower := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  cases k with
  | zero => omega
  | succ m =>
    refine ⟨(Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩, m), ?_⟩
    exact congrArg (fun q : Nat.Primes ↦ (q : ℕ) ^ (m + 1))
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨p, hp⟩)

/-- Regroup the canonical finite-place values by positive prime powers.
For a compact log profile both the individual place-exponent samples and
whole local values are finitely supported. The positive von Mangoldt sum
is the one subtracted in the reflected contour formula; the same outer
minus sign goes on the sum of the local values in (B.4.4.16). -/
public theorem rationalLocalRadialFourier_tsum_eq_vonMangoldt {F : ℝ → ℂ}
    (hF : HasCompactSupport F) :
    let g := fun x : ℝ ↦ Complex.exp (-(x : ℂ) / 2) * F x
    let A := fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) *
      (g (Real.log n) + g (-Real.log n) / (n : ℂ))
    let C := fun a : V × ℕ ↦
      let n := P[a.1] ^ (a.2 + 1)
      (Real.log (P[a.1] : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n) / (n : ℂ))
    HasFiniteSupport C ∧ HasFiniteSupport (fun v ↦ rationalLocalRadialFourier v F) ∧
      (∑' v, rationalLocalRadialFourier v F) = ∑' n, A n := by
  classical
  intro g A C
  -- Match the coefficient at each positive prime power, including its reflected weight.
  have hC : C = A ∘ primePower := by
    funext a
    simp only [C, A, comp_apply, primePower,
      ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero a.2),
      ArithmeticFunction.vonMangoldt_apply_prime (Rat.HeightOneSpectrum.primesEquiv a.1).property]
  -- Log support bounded by R implies any nonzero sample has n ≤ exp(R).
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hF.isBounded
  have hzero {x : ℝ} (hx : R < |x|) : g x = 0 := by
    have hz : F x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx.not_ge (by simpa [Real.dist_eq] using hR h))
    simp [g, hz]
  have hAf : HasFiniteSupport A := by
    refine (Finset.range (⌈Real.exp R⌉₊ + 1)).finite_toSet.subset ?_
    intro n hn
    by_contra hb
    have hnlarge : Real.exp R < (n : ℝ) := by
      have hlt : ⌈Real.exp R⌉₊ < n := by simpa using hb
      exact (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr hlt)
    have hnpos := (Real.exp_pos R).trans hnlarge
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Nat.cast_pos.mp hnpos)
    have hlog : R < Real.log n := Real.lt_log_iff_exp_lt hnpos |>.mpr hnlarge
    have hg₁ : g (Real.log n) = 0 := hzero (by rwa [abs_of_nonneg (Real.log_nonneg hn₁)])
    have hg₂ : g (-Real.log n) = 0 := hzero (by rwa [abs_neg, abs_of_nonneg (Real.log_nonneg hn₁)])
    exact hn (by simp [A, hg₁, hg₂])
  have hCf : HasFiniteSupport C := by
    rw [hC, HasFiniteSupport, support_comp_eq_preimage]
    exact hAf.preimage primePower_injective.injOn
  have hlocal (v : V) : rationalLocalRadialFourier v F = ∑' m, C (v, m) := by
    let : MeasurableSpace (K[v]ˣ) := borel _
    let : BorelSpace (K[v]ˣ) := ⟨rfl⟩
    simpa [rationalLocalRadialFourier, C, g] using
      (rationalLocalRadialFourier_eq_primeSamples v hF).2.2
  refine ⟨hCf, (hCf.image Prod.fst).subset ?_, ?_⟩
  · intro v hv
    by_contra hn
    apply hv
    change rationalLocalRadialFourier v F = 0
    rw [hlocal]
    have hz (m : ℕ) : C (v, m) = 0 :=
      notMem_support.mp (fun h ↦ hn ⟨(v, m), h, rfl⟩)
    simp [hz]
  · -- Sum on the Cartesian product before reindexing. Integers other than
    -- positive prime powers have zero von Mangoldt coefficient.
    simp_rw [hlocal]
    have hs : Summable C := summable_of_ne_finset_zero (s := hCf.toFinset)
      (fun _ ha ↦ notMem_support.mp (fun h ↦ ha ((Set.Finite.mem_toFinset hCf).mpr h)))
    rw [← hs.tsum_prod, hC]
    apply primePower_injective.tsum_eq
    intro n hn
    apply mem_range_primePower
    apply ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
    intro hz
    exact hn (by simp [A, hz])

end Masullo
