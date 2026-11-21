module

public import Theorems.RationalLocalMultiplicativeHaar
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Lemmas.RationalLocalAdditiveModulus
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Norm shells in the rational finite completions -/

open Function NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set
open scoped Padic

namespace Masullo

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation:max "K" v:max => adicCompletion ℚ v
local notation "G" v => (K v)ˣ
local notation "p[" v "]" => (Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes)
local notation "P[" v "]" => ((p[v] : ℕ) : ℝ)

local instance (v : V) : Fact (p[v] : ℕ).Prime := ⟨(p[v]).property⟩

/-- The shell of valuation `k` at the rational place `v`. -/
@[expose]
public def rationalLocalNormShell (v : V) (k : ℤ) : Set (G v) :=
  {x | ‖(x : K v)‖ = P[v]⁻¹ ^ k}

/-- The rational prime as a unit of its local field, not of the integral ring. -/
public noncomputable def rationalLocalUniformizer (v : V) : G v :=
  Units.mk0 ((p[v] : ℕ) : K v) (by
    intro h
    have he := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v) h
    rw [map_natCast, map_zero] at he
    exact (p[v]).property.ne_zero (Nat.cast_eq_zero.mp he))

namespace RationalLocalNormShell

public theorem one_lt_prime (v : V) : 1 < P[v] := by
  exact_mod_cast (p[v]).property.one_lt

public theorem prime_pos (v : V) : 0 < P[v] := (zero_lt_one.trans (one_lt_prime v))

private theorem norm_uniformizer (v : V) : ‖(rationalLocalUniformizer v : K v)‖ = P[v]⁻¹ := by
  change ‖((p[v] : ℕ) : K v)‖ = _
  rw [← norm_rationalLocal_padicEquiv v, map_natCast, Padic.norm_p]

/-- The image of integral units is precisely the norm-one subgroup. -/
public theorem mem_unitRange_iff (v : V) (x : G v) :
    x ∈ range (rationalLocalUnitInclusion v) ↔ ‖(x : K v)‖ = 1 := by
  have h (a : K v) : a ∈ v.adicCompletionIntegers ℚ ↔ ‖a‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff, ← mem_adicCompletionIntegers]
  constructor
  · rintro ⟨u, rfl⟩
    have h₁ := (h _).mp u.val.property
    have h₂ := (h _).mp u.inv.property
    change ‖((rationalLocalUnitInclusion v u) : K v)‖ ≤ 1 at h₁
    change ‖(((rationalLocalUnitInclusion v u)⁻¹ : G v) : K v)‖ ≤ 1 at h₂
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.mpr (Units.ne_zero _))] at h₂
    exact le_antisymm h₁ h₂
  · intro hx
    let a : v.adicCompletionIntegers ℚ := ⟨x.val, (h _).mpr hx.le⟩
    let b : v.adicCompletionIntegers ℚ := ⟨x.inv, (h _).mpr (by
      change ‖(↑(x⁻¹) : K v)‖ ≤ 1
      rw [Units.val_inv_eq_inv_val, norm_inv, hx, inv_one])⟩
    let u : (v.adicCompletionIntegers ℚ)ˣ :=
      ⟨a, b, Subtype.ext x.val_inv, Subtype.ext x.inv_val⟩
    exact ⟨u, Units.ext rfl⟩

/-- The valuation shell is a translate of the integral unit group. -/
public theorem eq_translate (v : V) (k : ℤ) : rationalLocalNormShell v k =
    (fun u : G v ↦ rationalLocalUniformizer v ^ k * u) ''
      range (rationalLocalUnitInclusion v) := by
  let a := rationalLocalUniformizer v ^ k
  have ha : ‖(a : K v)‖ = P[v]⁻¹ ^ k := by
    simp only [a, Units.val_zpow_eq_zpow_val, norm_zpow, norm_uniformizer]
  ext x
  change ‖(x : K v)‖ = P[v]⁻¹ ^ k ↔ x ∈ (fun u : G v ↦ a * u) '' _
  constructor
  · intro hx
    refine ⟨a⁻¹ * x, (mem_unitRange_iff v _).mpr ?_, by simp⟩
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, ← ha] at hx ⊢
    rw [hx, inv_mul_cancel₀ (norm_ne_zero_iff.mpr a.ne_zero)]
  · rintro ⟨u, hu, rfl⟩
    rw [Units.val_mul, norm_mul, (mem_unitRange_iff v u).mp hu, mul_one, ha]

public theorem measurableSet (v : V) [MeasurableSpace (G v)] [BorelSpace (G v)] (k : ℤ) :
    MeasurableSet (rationalLocalNormShell v k) :=
  (isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet

/-- Every integer shell has mass one in the normalization of (A.3.2.2). -/
public theorem measure (v : V) [MeasurableSpace (G v)] [BorelSpace (G v)] (k : ℤ) :
    rationalLocalMultiplicativeHaar v (rationalLocalNormShell v k) = 1 := by
  let a := rationalLocalUniformizer v ^ k
  have hpre : (fun u : G v ↦ a * u) ⁻¹' rationalLocalNormShell v k =
      range (rationalLocalUnitInclusion v) := by
    rw [eq_translate]
    exact Set.preimage_image_eq _ (mul_right_injective a)
  rw [← measure_preimage_mul (rationalLocalMultiplicativeHaar v) a (rationalLocalNormShell v k), hpre]
  exact rationalLocalMultiplicativeHaar_unitMass v

public theorem log_norm {v : V} {k : ℤ} {x : G v} (hx : x ∈ rationalLocalNormShell v k) :
    Real.log ‖(x : K v)‖ = -(k : ℝ) * Real.log P[v] := by
  change ‖(x : K v)‖ = P[v]⁻¹ ^ k at hx
  rw [hx, Real.log_zpow, Real.log_inv, mul_neg, neg_mul]

/-- The integer shells partition the entire rational local multiplicative group. -/
public theorem iUnion_eq_univ (v : V) : (⋃ k : ℤ, rationalLocalNormShell v k) = univ := by
  apply eq_univ_of_forall
  intro x
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have he : e (x : K v) ≠ 0 := (map_ne_zero_iff e e.injective).mpr x.ne_zero
  refine mem_iUnion.mpr ⟨(e (x : K v)).valuation, ?_⟩
  change ‖(x : K v)‖ = P[v]⁻¹ ^ (e (x : K v)).valuation
  rw [← norm_rationalLocal_padicEquiv v, Padic.norm_eq_zpow_neg_valuation he, inv_zpow']

public theorem pairwiseDisjoint (v : V) : Pairwise (Disjoint on rationalLocalNormShell v) := by
  intro j k hjk
  refine Set.disjoint_left.mpr (fun x h₁ h₂ ↦ hjk ?_)
  have hl := (Real.log_pos (one_lt_prime v)).ne'
  have he := mul_right_cancel₀ hl ((log_norm h₁).symm.trans (log_norm h₂))
  exact_mod_cast neg_injective he

public theorem norm_ne_one {v : V} {k : ℤ} {x : G v} (hk : k ≠ 0)
    (hx : x ∈ rationalLocalNormShell v k) : ‖(x : K v)‖ ≠ 1 := by
  intro h
  have h' := log_norm hx
  rw [h, Real.log_one] at h'
  exact hk (by exact_mod_cast neg_eq_zero.mp ((mul_eq_zero.mp h'.symm).resolve_right
    (Real.log_pos (one_lt_prime v)).ne'))

public theorem norm_sub_one (v : V) (x : G v) (hx : ‖(x : K v)‖ ≠ 1) :
    ‖1 - (x : K v)‖ = max 1 ‖(x : K v)‖ := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have he : ‖e (-(x : K v))‖ = ‖(x : K v)‖ := by
    rw [norm_rationalLocal_padicEquiv, norm_neg]
  rw [← norm_rationalLocal_padicEquiv v, sub_eq_add_neg]
  change ‖e (1 + -(x : K v))‖ = _
  rw [map_add, map_one, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one, he]
  simpa only [norm_one, he] using hx.symm

end RationalLocalNormShell
end Masullo
