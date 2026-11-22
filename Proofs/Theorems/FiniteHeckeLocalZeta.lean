module

public import Lemmas.FiniteLocalNormShell
public import Theorems.FiniteHeckeCharacterEulerProduct
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The finite local zeta tests with their Haar masses

The tests are the two in (3.4.3.7)–(8), p. 152, paired as in (3.3.1.7),
p. 130. In the text-based reading of (3.4.3.10)–(13), p. 153, the
normalized eigendistribution pairs to one and the zeta integral is its
product with the local Euler factor. For the Haar measure specified by
(A.3.2.2), p. 560, the test pairing instead retains the unit mass.
The two theorems below give the corrected raw integral. Dividing the
local test by that positive mass restores the claimed calibration.
-/

open NumberField IsDedekindDomain HeightOneSpectrum MeasureTheory Set
open scoped ENNReal

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "G" v => (adicCompletion K v)ˣ

private theorem restrict_eq_one_on_finiteLocalUnitSet (χ : HeckeCharacter (𝓞 K) K)
    (v : Places) (h : χ.IsUnramifiedAt v) {x : G v} (hx : x ∈ finiteLocalUnitSet v) :
    χ.restrict v (x : v.adicCompletion K) = 1 := by
  rw [finiteLocalUnitSet_eq_range] at hx
  obtain ⟨u, rfl⟩ := hx
  have he := DFunLike.congr_fun h u
  exact congrArg Units.val he

private theorem norm_cpow_pow (r : ℝ) (hr : 0 ≤ r) (k : ℕ) (s : ℂ) :
    ((r ^ k : ℝ) : ℂ) ^ s = ((r : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ r, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg hr k) hr,
      hk, pow_succ]

private theorem finiteHeckeWeight_on_shell (χ : HeckeCharacter (𝓞 K) K)
    (v : Places) (h : χ.IsUnramifiedAt v) (π : G v) (s : ℂ) (k : ℕ) :
    EqOn (fun x : G v ↦ χ.restrict v (x : v.adicCompletion K) * (‖(x : v.adicCompletion K)‖ : ℂ) ^ s)
      (fun _ ↦ (χ.restrict v (π : v.adicCompletion K) * (‖(π : v.adicCompletion K)‖ : ℂ) ^ s) ^ k)
      (finiteLocalNormShell v (π : v.adicCompletion K) k) := by
  intro x hx
  have hnorm : ‖(x : v.adicCompletion K)‖ = ‖(π : v.adicCompletion K)‖ ^ k := hx
  let u : G v := (π ^ k)⁻¹ * x
  have hu : u ∈ finiteLocalUnitSet v := by
    rw [finiteLocalNormShell_eq_preimage] at hx
    exact hx
  have hxu : x = π ^ k * u := by simp [u]
  have hchar : χ.restrict v (x : v.adicCompletion K) = (χ.restrict v (π : v.adicCompletion K)) ^ k := by
    rw [hxu, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
      restrict_eq_one_on_finiteLocalUnitSet χ v h hu, mul_one]
  simp only [hchar, hnorm, norm_cpow_pow _ (norm_nonneg _) k s, mul_pow]

/-- The integral-ring indicator gives `μ.real U` times the unramified Euler
factor on `Re s > 0`, with absolute integrability. The repair to the pairing
in (3.4.3.10), (13) is to retain the mass prescribed in (A.3.2.2). The
nonnegative shells partition the punctured integer ring, each has mass
`μ U` by multiplicative invariance, and their values form a geometric series. -/
public theorem finiteHeckeLocalZeta_unramified (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
    (v : Places) [MeasurableSpace (G v)] [BorelSpace (G v)]
    (μ : Measure (G v)) [Measure.IsMulLeftInvariant μ] (hμ : μ (finiteLocalUnitSet v) ≠ ∞)
    (h : χ.IsUnramifiedAt v) {s : ℂ} (hs : 0 < s.re) :
    let F := {x : G v | ‖(x : v.adicCompletion K)‖ ≤ 1}.indicator
      (fun x ↦ χ.restrict v (x : v.adicCompletion K) * (‖(x : v.adicCompletion K)‖ : ℂ) ^ s)
    Integrable F μ ∧ (∫ x, F x ∂μ) =
      (μ.real (finiteLocalUnitSet v) : ℂ) * finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s := by
  intro F
  classical
  let f := fun x : G v ↦ χ.restrict v (x : v.adicCompletion K) * (‖(x : v.adicCompletion K)‖ : ℂ) ^ s
  let B : Set (G v) := {x | ‖(x : v.adicCompletion K)‖ ≤ 1}
  have hB : MeasurableSet B := (isClosed_le (continuous_norm.comp Units.continuous_val)
    continuous_const).measurableSet
  obtain ⟨p, hp⟩ := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : G v := Units.mk0 (p : v.adicCompletion K) hp.ne_zero
  let S := finiteLocalNormShell v (π : v.adicCompletion K)
  let z := finiteHeckeMonomial (finiteHeckeCoefficient χ) v s
  have hz : ‖z‖ < 1 := norm_finiteHeckeMonomial_lt_one (norm_finiteHeckeCoefficient_le_one χ hχ v) hs
  have hzπ : χ.restrict v (π : v.adicCompletion K) * (‖(π : v.adicCompletion K)‖ : ℂ) ^ s = z := by
    change χ.restrict v (p : v.adicCompletion K) * (‖(p : v.adicCompletion K)‖ : ℂ) ^ s =
      finiteHeckeMonomial (finiteHeckeCoefficient χ) v s
    rw [uniformizer_norm_cpow v _ hp, finiteHeckeMonomial, finiteHeckeCoefficient,
      ite_eq_left h, h.localValue_eq _ hp]
  have hS (k : ℕ) : MeasurableSet (S k) := measurableSet_finiteLocalNormShell v _ k
  have hmass (k : ℕ) : μ (S k) = μ (finiteLocalUnitSet v) := finiteLocalNormShell_measure v μ π k
  have hconst (k : ℕ) : EqOn f (fun _ ↦ z ^ k) (S k) := by
    rw [← hzπ]
    exact finiteHeckeWeight_on_shell χ v h π s k
  have hcover : (⋃ k, S k) = B := finiteLocalNormShell_iUnion v _ hp
  have hlocal (k : ℕ) : IntegrableOn f (S k) μ :=
    (integrableOn_const (by rw [hmass]; exact hμ)).congr_fun (hconst k).symm (hS k)
  have hnormsum : Summable (fun k ↦ ∫ x in S k, ‖f x‖ ∂μ) := by
    have heq (k : ℕ) : (∫ x in S k, ‖f x‖ ∂μ) = μ.real (finiteLocalUnitSet v) * ‖z‖ ^ k := by
      rw [setIntegral_congr_fun (hS k) (g := fun _ ↦ ‖z ^ k‖) (fun x hx ↦ congrArg norm (hconst k hx)),
        setIntegral_const, measureReal_def, hmass, ← measureReal_def, norm_pow, smul_eq_mul]
    simp_rw [heq]
    exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left _
  have hfi : IntegrableOn f (⋃ k, S k) μ := integrableOn_iUnion_of_summable_integral_norm hlocal hnormsum
  refine ⟨(integrable_indicator_iff hB).2 (hcover ▸ hfi), ?_⟩
  change (∫ x, B.indicator f x ∂μ) = _
  rw [integral_indicator hB, ← hcover, integral_iUnion hS (finiteLocalNormShell_disjoint v _ hp) hfi]
  have heq (k : ℕ) : (∫ x in S k, f x ∂μ) = (μ.real (finiteLocalUnitSet v) : ℂ) * z ^ k := by
    rw [setIntegral_congr_fun (hS k) (hconst k), setIntegral_const, measureReal_def, hmass,
      ← measureReal_def, Complex.real_smul]
  simp_rw [heq]
  rw [tsum_mul_left, (hasSum_geometric_of_norm_lt_one hz).tsum_eq]
  rfl

/-- On the local integer units, the inverse-character test in (3.4.3.8)
cancels the character and the norm twist is one. Thus the actual pairing
is the unit mass, also `μ.real U` times the ramified Euler factor `1`.
No unitarity or restriction on `s` is needed for this compact test. -/
public theorem finiteHeckeLocalZeta_ramified (χ : HeckeCharacter (𝓞 K) K)
    (v : Places) [MeasurableSpace (G v)] [BorelSpace (G v)]
    (μ : Measure (G v)) (hμ : μ (finiteLocalUnitSet v) ≠ ∞)
    (h : ¬χ.IsUnramifiedAt v) (s : ℂ) :
    let F := (finiteLocalUnitSet v).indicator (fun x : G v ↦
      (χ.restrict v (x : v.adicCompletion K))⁻¹ * χ.restrict v (x : v.adicCompletion K) *
        (‖(x : v.adicCompletion K)‖ : ℂ) ^ s)
    Integrable F μ ∧ (∫ x, F x ∂μ) =
      (μ.real (finiteLocalUnitSet v) : ℂ) * finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s := by
  intro F
  let U := finiteLocalUnitSet v
  let f := fun x : G v ↦ (χ.restrict v (x : v.adicCompletion K))⁻¹ * χ.restrict v (x : v.adicCompletion K) *
    (‖(x : v.adicCompletion K)‖ : ℂ) ^ s
  have hU : MeasurableSet U := measurableSet_finiteLocalUnitSet v
  have he : EqOn f (fun _ ↦ (1 : ℂ)) U := by
    intro x hx
    have hnorm : ‖(x : v.adicCompletion K)‖ = 1 := hx
    have hne : χ.restrict v (x : v.adicCompletion K) ≠ 0 := by
      rw [← MulChar.coe_toUnitHom]
      exact Units.ne_zero _
    dsimp only [f]
    rw [inv_mul_cancel₀ hne, hnorm, Complex.ofReal_one, Complex.one_cpow, mul_one]
  refine ⟨(integrable_indicator_iff hU).2 ((integrableOn_const hμ).congr_fun he.symm hU), ?_⟩
  change (∫ x, U.indicator f x ∂μ) = _
  rw [integral_indicator hU, setIntegral_congr_fun hU he, setIntegral_const,
    finiteHeckeEulerFactor_eq_one_of_ramified χ v s h, Complex.real_smul]

end Masullo
