module

public import Props.ArchimedeanGammaLogDerivative
public import Theorems.ComplexArchimedeanHeckeRestriction
public import Theorems.FiniteHeckeCharacterEulerProduct
public import Theorems.RealArchimedeanHeckeRestriction

/-!
# The completed Hecke product on the right half-plane

Masullo's (3.2.1.2)–(5), p. 123, multiplies the finite Euler product by
one Gamma factor per infinite place. We use the checked restrictions of
the actual character for the real parity, complex angular weight, and
radial shift in the normalized local norm. In particular, the complex
factor is the manuscript's factor, not twice that factor.

In (B.4.2.5)–(7), p. 615, Masullo splits the logarithmic derivative
into local terms. We justify the split by the checked differentiation
of the locally uniformly convergent finite-place product and the
ordinary finite-product rule at infinity. The same result applies to
the conjugate character. This is a product on the half-plane of
convergence, not a continuation or a global zeta integral identity.
The source comparison uses Markdown and PDF layout, not rendered pages.
-/

open Complex NumberField InfinitePlace.Completion

namespace Masullo

variable {K : Type*} [Field K] [NumberField K]
variable (χ : HeckeCharacter (𝓞 K) K) (hχ : ∀ x : IdeleClassGroup (𝓞 K) K, ‖χ x‖ = 1)

/-- The factor of (3.2.1.3) attached to the actual character at `v`.
The choices are made once as functions of the character and place,
not separately at each argument `s`. -/
public noncomputable def localHeckeGammaFactor (v : InfinitePlace K) : ℂ → ℂ := by
  classical
  exact if hv : v.IsReal then
    let h := exists_archimedeanHeckeRestriction_real χ hχ hv
    archimedeanGammaFactor Real.pi 2 (h.choose : ℝ) h.choose_spec.choose
  else
    let h := exists_archimedeanHeckeRestriction_complex χ hχ
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)
    archimedeanGammaFactor (2 * Real.pi) 1 ((h.choose.natAbs : ℝ) / 2) h.choose_spec.choose

/-- The chosen real Gamma factor uses the parity and frequency of the
actual completion-unit character, as in (3.2.1.4). -/
public theorem localHeckeGammaFactor_real {v : InfinitePlace K} (hv : v.IsReal) :
    ∃ (b : ℕ) (τ : ℝ), b ≤ 1 ∧
      (∀ x : v.Completionˣ,
        let y := extensionEmbeddingOfIsReal hv (x : v.Completion)
        χ (IdeleClassGroup.ofCompletion (𝓞 K) K v x) =
          (if 0 < y then (1 : ℂ) else -1) ^ b * exp (((τ * Real.log |y| : ℝ) : ℂ) * I)) ∧
      localHeckeGammaFactor χ hχ v = archimedeanGammaFactor Real.pi 2 (b : ℝ) τ := by
  classical
  let h := exists_archimedeanHeckeRestriction_real χ hχ hv
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2, by rw [localHeckeGammaFactor, dite_eq_left hv]⟩

/-- The chosen complex Gamma factor uses the absolute angular weight in
(3.2.1.5) and the frequency for the log of the squared norm. -/
public theorem localHeckeGammaFactor_complex {v : InfinitePlace K} (hv : v.IsComplex) :
    ∃ (n : ℤ) (τ : ℝ),
      (∀ x : v.Completionˣ,
        let z := extensionEmbedding v (x : v.Completion)
        χ (IdeleClassGroup.ofCompletion (𝓞 K) K v x) =
          (z / (‖z‖ : ℂ)) ^ n * exp (((τ * Real.log (‖z‖ ^ 2) : ℝ) : ℂ) * I)) ∧
      localHeckeGammaFactor χ hχ v =
        archimedeanGammaFactor (2 * Real.pi) 1 ((n.natAbs : ℝ) / 2) τ := by
  classical
  let h := exists_archimedeanHeckeRestriction_complex χ hχ hv
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec,
    by rw [localHeckeGammaFactor, dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hv)]⟩

private theorem localHeckeGammaFactor_regular (v : InfinitePlace K) {s : ℂ} (hs : 0 < s.re) :
    localHeckeGammaFactor χ hχ v s ≠ 0 ∧ DifferentiableAt ℂ (localHeckeGammaFactor χ hχ v) s := by
  have hregular {B d b τ : ℝ} (hd : 0 < d) (hb : 0 ≤ b) :
      archimedeanGammaFactor B d b τ s ≠ 0 ∧
        DifferentiableAt ℂ (archimedeanGammaFactor B d b τ) s :=
    ⟨(logDeriv_archimedeanGammaFactor_eq_integral hd hb hs).1,
      (analyticOnNhd_archimedeanGammaFactor hd hb s hs).differentiableAt⟩
  rcases v.isReal_or_isComplex with hr | hc
  · obtain ⟨b, τ, _, _, h⟩ := localHeckeGammaFactor_real χ hχ hr
    rw [h]
    exact hregular (by norm_num) (Nat.cast_nonneg _)
  · obtain ⟨n, τ, _, h⟩ := localHeckeGammaFactor_complex χ hχ hc
    rw [h]
    exact hregular one_pos (by positivity)

/-- The completed product of (3.2.1.2). Its asserted domain is `1 < s.re`;
values of this formula outside that domain are not a continuation. -/
@[expose] public noncomputable def completedHeckeEulerProduct (s : ℂ) : ℂ :=
  (∏ v : InfinitePlace K, localHeckeGammaFactor χ hχ v s) * finiteHeckeCharacterEulerProduct χ s

/-- The split in (B.4.2.5)–(7) for a unitary character, before integration.
The joint finite-place series uses positive powers and zero coefficients
at omitted ramified places. -/
public theorem completedHeckeEulerProduct_logDeriv {s : ℂ} (hs : 1 < s.re) :
    completedHeckeEulerProduct χ hχ s ≠ 0 ∧
    DifferentiableAt ℂ (completedHeckeEulerProduct χ hχ) s ∧
    HasSum (finiteHeckeTerm (finiteHeckeCoefficient χ) s)
      ((∑ v : InfinitePlace K, logDeriv (localHeckeGammaFactor χ hχ v) s) -
        logDeriv (completedHeckeEulerProduct χ hχ) s) := by
  let A : ℂ → ℂ := fun t ↦ ∏ v : InfinitePlace K, localHeckeGammaFactor χ hχ v t
  have hloc := fun v ↦ localHeckeGammaFactor_regular χ hχ v (zero_lt_one.trans hs)
  have hA : A s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ (hloc v).1
  have hdA : DifferentiableAt ℂ A s := DifferentiableAt.fun_finsetProd fun v _ ↦ (hloc v).2
  obtain ⟨hF, hdF, hsum⟩ := finiteHeckeCharacterEulerProduct_logDeriv χ hχ hs
  refine ⟨mul_ne_zero hA hF, hdA.mul hdF, ?_⟩
  have hlogA : logDeriv A s = ∑ v : InfinitePlace K, logDeriv (localHeckeGammaFactor χ hχ v) s :=
    logDeriv_fun_prod (fun v _ ↦ (hloc v).1) (fun v _ ↦ (hloc v).2)
  change HasSum _ (_ - logDeriv (fun t ↦ A t * finiteHeckeCharacterEulerProduct χ t) s)
  rw [logDeriv_fun_mul s hA hF hdA hdF, hlogA, sub_add_cancel_left]
  exact hsum

end Masullo
