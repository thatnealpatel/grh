module

public import Theorems.ArchimedeanCompletionGaussian
public import Theorems.IdeleZetaIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-! # The raw global Gaussian pairing above one

Definition 3.4.3.2, p. 152, supplies the local tests and their tensor
(3.4.3.3)–(9), and the next paragraph defines the completion by pairing
this tensor with the zeta density. The Euler convention (3.2.1.1)–(5),
pp. 122–123, does not give that raw pairing as printed: At a complex
place the bilinear pairing (3.3.1.7), p. 130, needs opposite angular
weight, and at a finite place (A.3.2.2), p. 560, need not give the units
mass one. We use the checked local Gaussian and finite zeta pairings,
and `ideleZetaIntegral_rightHalfPlane` gives the restricted-product
limit. The result compares the raw pairing directly with the Euler
completion, without invoking eigendistributions or continuation.
The assembly reading is provisional (Markdown and numbered PDF layout).
-/

open Complex IsDedekindDomain MeasureTheory NumberField Set
open InfinitePlace.Completion
open scoped Classical Masullo

namespace Masullo

variable {K : Type*} [Field K]

/-- The multiplicative measure of (A.3.2.2) in the real or complex
completion coordinate. -/
@[expose] public noncomputable def archimedeanCompletionHaar
    (v : InfinitePlace K) [MeasurableSpace v.Completionˣ] [BorelSpace v.Completionˣ] :
    Measure v.Completionˣ :=
  if hv : v.IsReal then realCompletionHaar hv
  else complexCompletionHaar (InfinitePlace.not_isReal_iff_isComplex.mp hv)

public instance archimedeanCompletionHaar_isHaarMeasure
    (v : InfinitePlace K) [MeasurableSpace v.Completionˣ] [BorelSpace v.Completionˣ] :
    (archimedeanCompletionHaar v).IsHaarMeasure := by
  by_cases hv : v.IsReal <;> simp only [archimedeanCompletionHaar, hv, dite_true, dite_false] <;>
    infer_instance

variable [NumberField K]
local notation "V" => HeightOneSpectrum (𝓞 K)
local notation "F" v => HeightOneSpectrum.adicCompletion K v
local notation "Ideg" => IdeleGroup (𝓞 K) K
set_option quotPrecheck false in
local notation "A" => ((v : InfinitePlace K) → v.Completionˣ)

variable (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)
variable [ma : ∀ v : InfinitePlace K, MeasurableSpace v.Completionˣ]
  [ba : ∀ v : InfinitePlace K, BorelSpace v.Completionˣ]

/-- The real parity Gaussian, or the corrected opposite-weight complex
Gaussian. The parity and weight are chosen before `s` is supplied. -/
@[expose] public noncomputable def archimedeanHeckeGaussian (v : InfinitePlace K) (u : v.Completionˣ) : ℂ :=
  if hv : v.IsReal then
    realZetaGaussian (realCompletionGaussianPair χ hχ hv).choose (extensionEmbeddingOfIsReal hv u.val)
  else
    complexZetaGaussian (complexCompletionGaussianPair χ hχ
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).choose (extensionEmbedding v u.val)

private theorem archimedeanHeckeGaussian_local (v : InfinitePlace K) {s : ℂ}
    (hs : 0 < s.re) :
    let g (u : v.Completionˣ) := archimedeanHeckeGaussian χ hχ v u *
      χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) * (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ s)
    Integrable g (archimedeanCompletionHaar v) ∧
      (∫ u, g u ∂archimedeanCompletionHaar v) = localHeckeGammaFactor χ hχ v s := by
  by_cases hv : v.IsReal
  · simpa only [archimedeanHeckeGaussian, archimedeanCompletionHaar, dite_eq_left hv] using
      (realCompletionGaussianPair χ hχ hv).choose_spec.2 s hs
  · simpa only [archimedeanHeckeGaussian, archimedeanCompletionHaar, dite_eq_right hv] using
      (complexCompletionGaussianPair χ hχ (InfinitePlace.not_isReal_iff_isComplex.mp hv)).choose_spec s hs

private theorem archimedeanHeckeGaussian_grouped {s : ℂ} (hs : 0 < s.re) :
    let g (x : A) := (∏ v, archimedeanHeckeGaussian χ hχ v (x v)) *
      (∏ v, χ (IdeleClassGroup.ofCompletion (𝓞 K) K v (x v))) *
      ((∏ v, ‖(x v : v.Completion)‖ ^ v.mult : ℝ) : ℂ) ^ s
    Integrable g (Measure.pi (fun v ↦ archimedeanCompletionHaar v)) ∧
      (∫ x, g x ∂Measure.pi (fun v ↦ archimedeanCompletionHaar v)) = ∏ v, localHeckeGammaFactor χ hχ v s := by
  let G (v : InfinitePlace K) (u : v.Completionˣ) := archimedeanHeckeGaussian χ hχ v u *
    χ (IdeleClassGroup.ofCompletion (𝓞 K) K v u) * (((‖u.val‖ ^ v.mult : ℝ) : ℂ) ^ s)
  have h (x : A) : (∏ v, archimedeanHeckeGaussian χ hχ v (x v)) *
      (∏ v, χ (IdeleClassGroup.ofCompletion (𝓞 K) K v (x v))) *
      ((∏ v, ‖(x v : v.Completion)‖ ^ v.mult : ℝ) : ℂ) ^ s = ∏ v, G v (x v) := by
    rw [prod_norm_cpow _ _ (fun _ ↦ pow_nonneg (norm_nonneg _) _) s,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  let (v : InfinitePlace K) : SigmaFinite (archimedeanCompletionHaar v) :=
    archimedeanHaar_sigmaFinite K (fun w ↦ archimedeanCompletionHaar w) v
  dsimp only
  simp_rw [h]
  refine ⟨Integrable.fintype_prod_dep (fun v ↦ (archimedeanHeckeGaussian_local χ hχ v hs).1), ?_⟩
  rw [integral_fintype_prod_eq_prod (μ := fun v ↦ archimedeanCompletionHaar v) G]
  exact Finset.prod_congr rfl fun v _ ↦ (archimedeanHeckeGaussian_local χ hχ v hs).2

/-- The two finite Gaussian tests (3.4.3.7)–(8), restricted to completion units. -/
@[expose] public noncomputable def finiteHeckeGaussian (v : V) (x : (F v)ˣ) : ℂ :=
  if χ.IsUnramifiedAt v then if ‖(x : F v)‖ ≤ 1 then 1 else 0
  else (finiteLocalUnitSet v).indicator (fun y ↦ (χ.restrict v (y : F v))⁻¹) x

/-- The tensor test of (3.4.3.9), with the angular correction. `T` includes
ramification; off `T` the default test is the integral-ring indicator. -/
@[expose] public noncomputable def ideleHeckeGaussian (T : Finset V) : Ideg → ℂ :=
  ideleZetaTest K T (fun x ↦ ∏ v, archimedeanHeckeGaussian χ hχ v (x v)) (finiteHeckeGaussian χ)

variable [mf : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)ˣ]
  [bf : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)ˣ]
  (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)ˣ) [hf : ∀ v, (μf v).IsHaarMeasure]

omit ma ba in
private theorem finiteHeckeGaussian_local
    (hunit : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) (v : V) {s : ℂ} (hs : 0 < s.re) :
    let g (x : (F v)ˣ) := finiteHeckeGaussian χ v x * χ.restrict v (x : F v) * (‖(x : F v)‖ : ℂ) ^ s
    Integrable g (μf v) ∧ (∫ x, g x ∂μf v) =
      ((finiteCompletionUnitMass K μf v).toReal : ℂ) * finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s := by
  let : CompactSpace (v.adicCompletionIntegers K)ˣ := compactSpace_finiteCompletionIntegralUnits K v
  have hc : IsCompact (finiteLocalUnitSet v) := by
    rw [finiteLocalUnitSet_eq_range]
    exact isCompact_range (isOpenEmbedding_finiteCompletionIntegralUnits K v).continuous
  have hm : μf v (finiteLocalUnitSet v) ≠ ⊤ := hc.measure_ne_top
  have hr : (μf v).real (finiteLocalUnitSet v) = (finiteCompletionUnitMass K μf v).toReal := by
    rw [Measure.real, finiteLocalUnitSet_eq_range]
    rfl
  dsimp only
  rw [← hr]
  by_cases hu : χ.IsUnramifiedAt v
  · have he (x : (F v)ˣ) : finiteHeckeGaussian χ v x * χ.restrict v (x : F v) * (‖(x : F v)‖ : ℂ) ^ s =
        {y : (F v)ˣ | ‖(y : F v)‖ ≤ 1}.indicator
          (fun y ↦ χ.restrict v (y : F v) * (‖(y : F v)‖ : ℂ) ^ s) x := by
      by_cases hx : ‖(x : F v)‖ ≤ 1 <;> simp only [finiteHeckeGaussian, ite_eq_left hu, Set.indicator_apply, Set.mem_ofPred_eq,
        hx, ite_true, ite_false, one_mul, zero_mul]
    simp_rw [he]
    exact finiteHeckeLocalZeta_unramified χ hunit v (μf v) hm hu hs
  · have he (x : (F v)ˣ) : finiteHeckeGaussian χ v x * χ.restrict v (x : F v) * (‖(x : F v)‖ : ℂ) ^ s =
        (finiteLocalUnitSet v).indicator (fun y : (F v)ˣ ↦
          (χ.restrict v (y : F v))⁻¹ * χ.restrict v (y : F v) * (‖(y : F v)‖ : ℂ) ^ s) x := by
      by_cases hx : x ∈ finiteLocalUnitSet v <;> simp only [finiteHeckeGaussian, ite_eq_right hu, Set.indicator_apply, hx, ite_true, ite_false, zero_mul]
    simp_rw [he]
    exact finiteHeckeLocalZeta_ramified χ v (μf v) hm hu s

omit ma ba mf bf in
private theorem finiteHeckeEulerProduct_recombine
    (hunit : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1) (T : Finset V) {s : ℂ} (hs : 1 < s.re) :
    (∏ v ∈ T, finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s) *
      finiteHeckeEulerProduct (fun v ↦ if v ∈ T then 0 else finiteHeckeCoefficient χ v) s =
      finiteHeckeCharacterEulerProduct χ s := by
  let z (v : V) := if v ∈ T then 0 else finiteHeckeCoefficient χ v
  let c (v : V) := finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s
  let d (v : V) := if v ∈ T then c v else 1
  have hd : HasProd d (∏ v ∈ T, c v) := by
    have h := hasProd_prod_of_ne_finset_one (s := T) (f := d) (L := SummationFilter.unconditional V)
      (fun v hv ↦ ite_eq_right hv)
    convert h using 1
    exact Finset.prod_congr rfl fun v hv ↦ (ite_eq_left hv).symm
  have hz (v : V) : ‖z v‖ ≤ 1 := by
    by_cases hv : v ∈ T
    · simp [z, hv]
    · simpa only [z, ite_eq_right hv] using norm_finiteHeckeCoefficient_le_one χ hunit v
  have htail := (finiteHeckeEulerFactor_hasProdLocallyUniformlyOn hz).hasProd (x := s) hs
  have hc (v : V) : d v * finiteHeckeEulerFactor z v s = c v := by
    by_cases hv : v ∈ T <;> simp [d, c, z, hv, finiteHeckeEulerFactor, finiteHeckeMonomial]
  have hp := (hd.mul htail).congr_fun fun v ↦ (hc v).symm
  rw [finiteHeckeCharacterEulerProduct]
  simp_rw [finiteHecke_localPolynomial_eval_inv]
  exact hp.tprod_eq.symm

variable [mu : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletionIntegers K)ˣ]
  [bu : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletionIntegers K)ˣ]
  [MeasurableSpace (IdeleGroup (𝓞 K) K)]

/-- For the single Gaussian tensor independent of `s`, the actual raw
idelic pairing converges absolutely on `Re s > 1`. It equals the completed
Euler product times the finite product of the actual unit masses. `T`
contains all ramified places of `χ` and all exceptions to unit mass one.
The measure hypothesis describes the exact restrictions of (A.3.2.5). -/
public theorem ideleHeckeGaussian_zetaIntegral [BorelSpace Ideg]
    (T : Finset V) (hT : ∀ v ∉ T, finiteCompletionUnitMass K μf v = 1)
    (hu : ∀ v ∉ T, χ.IsUnramifiedAt v) (μ : Measure Ideg)
    (hμ : ∀ S : Finset V, T ⊆ S → μ.comap (ideleFiniteStageEmbedding K S) =
      ideleFiniteStageProduct K (fun v ↦ archimedeanCompletionHaar v) μf S)
    {s : ℂ} (hs : 1 < s.re) :
    let g (a : Ideg) := ideleHeckeGaussian χ hχ T a *
      χ (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K) a) *
      (‖(a : AdeleRing (𝓞 K) K)‖ : ℂ) ^ s
    Integrable g μ ∧ (∫ a, g a ∂μ) =
      (∏ v ∈ T, ((finiteCompletionUnitMass K μf v).toReal : ℂ)) * completedHeckeEulerProduct χ hχ s := by
  let arch (x : A) := ∏ v, archimedeanHeckeGaussian χ hχ v (x v)
  -- First evaluate the grouped Archimedean block and each finite exception.
  obtain ⟨hA, hvalA⟩ := archimedeanHeckeGaussian_grouped χ hχ (zero_lt_one.trans hs)
  have hF (v : V) := finiteHeckeGaussian_local χ μf hχ v (s := s) (zero_lt_one.trans hs)
  -- The raw right-half-plane theorem gives absolute integrability before
  -- identifying the integral with the local values and the Euler tail.
  obtain ⟨hi, hval, _⟩ := ideleZetaIntegral_rightHalfPlane K (fun v ↦ archimedeanCompletionHaar v) μf T T
    (Finset.Subset.refl _) hT μ hμ χ hu hχ s hs arch (finiteHeckeGaussian χ) hA
    (fun v hv ↦ by simpa only [ideleFiniteTest, ite_eq_left hv] using (hF v).1)
  refine ⟨hi, ?_⟩
  have hfval : (∏ v ∈ T, ∫ x : (F v)ˣ,
      ideleFiniteTest K T (finiteHeckeGaussian χ) v x * χ.restrict v (x : F v) *
        (‖(x : F v)‖ : ℂ) ^ s ∂μf v) =
      ∏ v ∈ T, ((finiteCompletionUnitMass K μf v).toReal : ℂ) *
        finiteHeckeEulerFactor (finiteHeckeCoefficient χ) v s :=
    Finset.prod_congr rfl fun v hv ↦ by simpa only [ideleFiniteTest, ite_eq_left hv] using (hF v).2
  rw [ideleHeckeGaussian, hval, hvalA, hfval, Finset.prod_mul_distrib, completedHeckeEulerProduct]
  have hr := finiteHeckeEulerProduct_recombine χ hχ T hs
  rw [← hr]
  ac_rfl

end Masullo
