module

public import Lemmas.FiniteHeckeLocalNormalization
public import Mathlib.MeasureTheory.Group.Measure

/-! # Nonnegative norm shells in a finite completion -/

open Function NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "G" v => (adicCompletion K v)ˣ

/-- The integer-unit subgroup, as a subset of the completion units. -/
@[expose] public def finiteLocalUnitSet (v : Places) : Set (G v) :=
  {x | ‖(x : v.adicCompletion K)‖ = 1}

private theorem integral_iff_norm_le_one (v : Places) (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, mem_adicCompletionIntegers]

/-- The norm-one set is exactly the image of the actual integer-ring units. -/
public theorem finiteLocalUnitSet_eq_range (v : Places) :
    finiteLocalUnitSet v = range (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom) := by
  ext x
  change ‖(x : v.adicCompletion K)‖ = 1 ↔ _
  constructor
  · intro hx
    let a : v.adicCompletionIntegers K := ⟨x.val, (integral_iff_norm_le_one v _).mpr hx.le⟩
    let b : v.adicCompletionIntegers K := ⟨x.inv, (integral_iff_norm_le_one v _).mpr (by
      change ‖(↑(x⁻¹) : v.adicCompletion K)‖ ≤ 1
      rw [Units.val_inv_eq_inv_val, norm_inv, hx, inv_one])⟩
    let u : (v.adicCompletionIntegers K)ˣ :=
      ⟨a, b, Subtype.ext x.val_inv, Subtype.ext x.inv_val⟩
    exact ⟨u, Units.ext rfl⟩
  · rintro ⟨u, rfl⟩
    have h₁ := (integral_iff_norm_le_one v _).mp u.val.property
    have h₂ := (integral_iff_norm_le_one v _).mp u.inv.property
    let y := Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u
    change ‖(y : v.adicCompletion K)‖ ≤ 1 at h₁
    change ‖(↑(y⁻¹) : v.adicCompletion K)‖ ≤ 1 at h₂
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.mpr y.ne_zero)] at h₂
    exact le_antisymm h₁ h₂

/-- The elements of valuation `k`, expressed via the norm of a uniformizer. -/
@[expose] public def finiteLocalNormShell (v : Places) (π : v.adicCompletion K) (k : ℕ) :
    Set (G v) := {x | ‖(x : v.adicCompletion K)‖ = ‖π‖ ^ k}

public theorem measurableSet_finiteLocalNormShell (v : Places) [MeasurableSpace (G v)]
    [BorelSpace (G v)] (π : v.adicCompletion K) (k : ℕ) :
    MeasurableSet (finiteLocalNormShell v π k) :=
  (isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet

public theorem measurableSet_finiteLocalUnitSet (v : Places) [MeasurableSpace (G v)]
    [BorelSpace (G v)] : MeasurableSet (finiteLocalUnitSet v) :=
  (isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet

public theorem finiteLocalNormShell_eq_preimage (v : Places) (π : G v) (k : ℕ) :
    finiteLocalNormShell v (π : v.adicCompletion K) k =
      (fun x ↦ (π ^ k)⁻¹ * x) ⁻¹' finiteLocalUnitSet v := by
  ext x
  change ‖(x : v.adicCompletion K)‖ = ‖(π : v.adicCompletion K)‖ ^ k ↔
    ‖(↑((π ^ k)⁻¹ * x) : v.adicCompletion K)‖ = 1
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    norm_mul, norm_inv, norm_pow, ← div_eq_inv_mul,
    div_eq_iff (pow_ne_zero _ (norm_ne_zero_iff.mpr π.ne_zero)), one_mul]

public theorem finiteLocalNormShell_measure (v : Places) [MeasurableSpace (G v)]
    [BorelSpace (G v)] (μ : Measure (G v)) [Measure.IsMulLeftInvariant μ] (π : G v) (k : ℕ) :
    μ (finiteLocalNormShell v (π : v.adicCompletion K) k) = μ (finiteLocalUnitSet v) := by
  rw [finiteLocalNormShell_eq_preimage, measure_preimage_mul]

private theorem uniformizer_norm_lt_one (v : Places) (π : v.adicCompletion K)
    (hπ : Valued.v.IsUniformizer π) : ‖π‖ < 1 := by
  rw [norm_uniformizer_eq_inv_finitePlaceNorm v π hπ]
  exact inv_lt_one_of_one_lt₀ ((by norm_num : (1 : ℝ) < 2).trans_le (two_le_finitePlaceNorm v))

public theorem finiteLocalNormShell_disjoint (v : Places) (π : v.adicCompletion K)
    (hπ : Valued.v.IsUniformizer π) : Pairwise (Disjoint on (finiteLocalNormShell v π)) := by
  intro j k hjk
  refine Set.disjoint_left.mpr (fun x hj hk ↦ hjk ?_)
  have hpow : StrictAnti (fun n : ℕ ↦ ‖π‖ ^ n) :=
    pow_right_strictAnti₀ (norm_pos_iff.mpr hπ.ne_zero) (uniformizer_norm_lt_one v π hπ)
  exact hpow.injective ((show ‖(x : v.adicCompletion K)‖ = ‖π‖ ^ j from hj).symm.trans hk)

/-- The nonnegative shells partition the nonzero elements of the integer ring. -/
public theorem finiteLocalNormShell_iUnion (v : Places) (π : v.adicCompletion K)
    (hπ : Valued.v.IsUniformizer π) :
    (⋃ k : ℕ, finiteLocalNormShell v π k) = {x : G v | ‖(x : v.adicCompletion K)‖ ≤ 1} := by
  ext x
  rw [mem_iUnion]
  change (∃ k : ℕ, ‖(x : v.adicCompletion K)‖ = ‖π‖ ^ k) ↔ ‖(x : v.adicCompletion K)‖ ≤ 1
  constructor
  · rintro ⟨k, hk⟩
    rw [hk]
    exact pow_le_one₀ (norm_nonneg _) (uniformizer_norm_lt_one v π hπ).le
  · intro hx
    let a : Valued.v.integer := ⟨x.val, (Valued.toNormedField.norm_le_one_iff.mp hx)⟩
    let p : Valuation.Uniformizer (Valued.v : Valuation (v.adicCompletion K)
        (WithZero (Multiplicative ℤ))) := ⟨⟨π, hπ.val_lt_one.le⟩, hπ⟩
    obtain ⟨k, u, hu⟩ := Valuation.exists_pow_Uniformizer (r := a)
      (fun ha ↦ x.ne_zero (congrArg Subtype.val ha)) p
    let y : G v := Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u
    have hy : y ∈ finiteLocalUnitSet v := by
      rw [finiteLocalUnitSet_eq_range]
      exact ⟨u, rfl⟩
    have heq : (x : v.adicCompletion K) = π ^ k * (y : v.adicCompletion K) := by
      have hpow : ((↑(p.val ^ k)) : v.adicCompletion K) = π ^ k := by
        exact Subring.coe_pow _ p.val k
      rw [hpow] at hu
      exact hu
    exact ⟨k, by rw [heq, norm_mul, norm_pow, (show ‖(y : v.adicCompletion K)‖ = 1 from hy), mul_one]⟩

end Masullo
