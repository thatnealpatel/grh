module

public import Lemmas.PrimeWindowModulation
public import Lemmas.PrimeTranslationSpanCancellation
import Mathlib.Tactic

/-! # Pole correction on escaping prime-window tests

Source: `bdd74f2a:.godel/adhoc/prime-translation-norm.md`, §§1 and 3
(lines 7–26 and 44–50). Untwisting and weak escape are from
`Lemmas.PrimeWindowModulation` at `e97a8a47`.
Owning check session: `01a20e90-1953-703f-a5c5-0300053aba36`.

Scope: for a fixed positive window, the positive twisted prime Rayleigh form
minus the actual two-pole quadratic, on some supported unit test, is at least
the positive untwisted form on any given supported unit test minus any
prescribed positive error. The prime form keeps the same strict power cutoff.
No spectral norm or archimedean estimate is asserted.
-/

open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology

namespace Masullo

local notation "𝓗" => Lp ℂ 2 (volume : Measure ℝ)

private theorem memLp_windowExp (D : ℝ) (a : ℝ → ℝ) (ha : Continuous a)
    (h : ∀ x ∈ Set.Icc 0 D, a x ≤ 0) :
    MemLp ((Set.Icc 0 D).indicator (fun x ↦ (Real.exp (a x) : ℂ))) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Icc 0 D)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine MemLp.of_bound
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp ha)).aestronglyMeasurable 1 ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (h x hx)

private theorem reflect_mem_window (D x : ℝ) : D - x ∈ Set.Icc 0 D ↔ x ∈ Set.Icc 0 D := by
  simp only [Set.mem_Icc, sub_nonneg, sub_le_self_iff, and_comm]

private theorem poleLeft_on {D x : ℝ} (hx : x ∈ Set.Icc 0 D) :
    primeTranslationProfile D x = Real.exp (-x / 2) :=
  Set.indicator_of_mem hx _

private theorem poleRight_on {D x : ℝ} (hx : x ∈ Set.Icc 0 D) :
    primeTranslationReflectedProfile D x = Real.exp (-(D - x) / 2) :=
  poleLeft_on ((reflect_mem_window D x).mpr hx)

private theorem poleRight_off {D x : ℝ} (hx : x ∉ Set.Icc 0 D) :
    primeTranslationReflectedProfile D x = 0 := by
  rw [primeTranslationReflectedProfile, primeTranslationProfile,
    Set.indicator_of_notMem (fun h ↦ hx ((reflect_mem_window D x).mp h))]

private theorem memLp_poleLeft (D : ℝ) :
    MemLp (fun x ↦ (primeTranslationProfile D x : ℂ)) 2 volume := by
  convert memLp_windowExp D (fun x ↦ -x / 2) (by fun_prop) (fun x hx ↦ by linarith [hx.1]) using 1
  funext x
  by_cases hx : x ∈ Set.Icc 0 D <;> simp [primeTranslationProfile, hx]

private theorem memLp_poleRight (D : ℝ) :
    MemLp (fun x ↦ (primeTranslationReflectedProfile D x : ℂ)) 2 volume := by
  convert memLp_windowExp D (fun x ↦ -(D - x) / 2) (by fun_prop)
    (fun x hx ↦ by linarith [hx.2]) using 1
  funext x
  by_cases hx : x ∈ Set.Icc 0 D
  · rw [poleRight_on hx, Set.indicator_of_mem hx]
  · rw [poleRight_off hx, Set.indicator_of_notMem hx, Complex.ofReal_zero]

private noncomputable def poleLeft (D : ℝ) : 𝓗 := (memLp_poleLeft D).toLp _
private noncomputable def poleRight (D : ℝ) : 𝓗 := (memLp_poleRight D).toLp _

private theorem poleLeft_ae (D : ℝ) :
    poleLeft D =ᵐ[volume] fun x ↦ (primeTranslationProfile D x : ℂ) :=
  (memLp_poleLeft D).coeFn_toLp

private theorem poleRight_ae (D : ℝ) :
    poleRight D =ᵐ[volume] fun x ↦ (primeTranslationReflectedProfile D x : ℂ) :=
  (memLp_poleRight D).coeFn_toLp

private theorem inner_window_profile (D : ℝ) (u a : 𝓗) (r : ℝ → ℝ)
    (ha : a =ᵐ[volume] fun x ↦ (r x : ℂ)) (hoff : ∀ x ∉ Set.Icc 0 D, r x = 0) :
    ⟪a, u⟫_ℂ = ∫ x in Set.Icc 0 D, (r x : ℂ) * u x := by
  have hout : ∀ᵐ x ∂volume, x ∉ Set.Icc 0 D → (r x : ℂ) * u x = 0 :=
    .of_forall fun x hx ↦ by simp [hoff x hx]
  rw [L2.inner_def, setIntegral_eq_integral_of_ae_compl_eq_zero hout]
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  rw [RCLike.inner_apply, hx, Complex.conj_ofReal, mul_comm]

/-- The two-pole action `exp (D / 2) • (f ⊗ g + g ⊗ f)` on full-line `L²`, with
`f` and `g` the zero-extended endpoint exponentials and `(a ⊗ b) u = ⟪b, u⟫ • a`. -/
public noncomputable def primeWindowPoleOperator (D : ℝ) (u : 𝓗) : 𝓗 :=
  (Real.exp (D / 2) : ℂ) •
    (⟪poleRight D, u⟫_ℂ • poleLeft D + ⟪poleLeft D, u⟫_ℂ • poleRight D)

/-- The `L²` pole action agrees with the windowed representative pole action. -/
public theorem primeWindowPoleOperator_ae (D : ℝ) (u : 𝓗) :
    primeWindowPoleOperator D u =ᵐ[volume] primeTranslationPoleApply D u := by
  let a := ⟪poleRight D, u⟫_ℂ
  let b := ⟪poleLeft D, u⟫_ℂ
  let E : ℂ := Real.exp (D / 2)
  have ha : a = ∫ x in Set.Icc 0 D, (primeTranslationReflectedProfile D x : ℂ) * u x :=
    inner_window_profile D u _ _ (poleRight_ae D) fun _ hx ↦ poleRight_off hx
  have hb : b = ∫ x in Set.Icc 0 D, (primeTranslationProfile D x : ℂ) * u x :=
    inner_window_profile D u _ _ (poleLeft_ae D) (by
      intro x hx
      simp [primeTranslationProfile, hx])
  change (⇑(E • (a • poleLeft D + b • poleRight D))) =ᵐ[volume] primeTranslationPoleApply D u
  filter_upwards [Lp.coeFn_smul E (a • poleLeft D + b • poleRight D),
    Lp.coeFn_add (a • poleLeft D) (b • poleRight D), Lp.coeFn_smul a (poleLeft D),
    Lp.coeFn_smul b (poleRight D), poleLeft_ae D, poleRight_ae D]
    with x hE hab hax hbx hfx hgx
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hE hab hax hbx
  rw [hE, hab, hax, hbx, hfx, hgx, ha, hb, primeTranslationPoleApply]
  dsimp only [E]
  ring

/-- The rank-two kernel in `primeTranslationPoleApply`, evaluated on the window,
is the source's two-pole kernel `2 cosh ((x - z) / 2)`. -/
public theorem primeWindowPole_kernel (D x z : ℝ) (hx : x ∈ Set.Icc 0 D) (hz : z ∈ Set.Icc 0 D) :
    Real.exp (D / 2) *
      (primeTranslationProfile D x * primeTranslationReflectedProfile D z +
        primeTranslationReflectedProfile D x * primeTranslationProfile D z) =
      2 * Real.cosh ((x - z) / 2) := by
  simp only [poleLeft_on hx, poleLeft_on hz, poleRight_on hx, poleRight_on hz, mul_add,
    ← Real.exp_add]
  rw [show D / 2 + (-x / 2 + -(D - z) / 2) = -((x - z) / 2) by ring,
    show D / 2 + (-(D - x) / 2 + -z / 2) = (x - z) / 2 by ring,
    Real.cosh_eq]
  ring

/-- The real Rayleigh quadratic of the two-pole operator, with no positivity
assumption on it. -/
@[expose] public noncomputable def primeWindowPoleQuadratic (D : ℝ) (u : 𝓗) : ℝ :=
  (⟪u, primeWindowPoleOperator D u⟫_ℂ).re

private theorem tendsto_poleQuadratic_of_pairings (D : ℝ) (v : ℕ → 𝓗)
    (hf : Tendsto (fun j ↦ ⟪poleLeft D, v j⟫_ℂ) atTop (𝓝 0))
    (hg : Tendsto (fun j ↦ ⟪poleRight D, v j⟫_ℂ) atTop (𝓝 0)) :
    Tendsto (fun j ↦ primeWindowPoleQuadratic D (v j)) atTop (𝓝 0) := by
  have hf' : Tendsto (fun j ↦ ⟪v j, poleLeft D⟫_ℂ) atTop (𝓝 0) := by
    simpa only [star_zero, Complex.star_def, inner_conj_symm] using hf.star
  have hg' : Tendsto (fun j ↦ ⟪v j, poleRight D⟫_ℂ) atTop (𝓝 0) := by
    simpa only [star_zero, Complex.star_def, inner_conj_symm] using hg.star
  have h : Tendsto (fun j ↦ ⟪v j, primeWindowPoleOperator D (v j)⟫_ℂ) atTop (𝓝 0) := by
    simpa only [primeWindowPoleOperator, inner_smul_right, inner_add_right, mul_zero, add_zero]
      using ((hg.mul hf').add (hf.mul hg')).const_mul (Real.exp (D / 2) : ℂ)
  exact Complex.continuous_re.continuousAt.tendsto.comp h

/-- For each supported unit test, a late modulation is a supported unit test
whose positive twisted form, after subtracting the pole quadratic, is at least
its untwisted positive form on the original test minus `ε`. -/
public theorem exists_primeWindowPoleCorrected_test {ι : Type*} [Fintype ι]
    (D : ℝ) (_hD : 0 < D) (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1)
    (u : 𝓗) (hu : PrimeWindowSupported D u) (hu₁ : ‖u‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : 𝓗, PrimeWindowSupported D v ∧ ‖v‖ = 1 ∧
      -(primeWindowSignedForm D p (fun _ ↦ 1) u).re - ε ≤
        -(primeWindowSignedForm D p c v).re - primeWindowPoleQuadratic D v := by
  obtain ⟨y, -, herr, htest, hweak⟩ := exists_primeWindowModulation D p hp hinj c hc
  let v j := primeWindowModulate (y j) u
  have hpole := tendsto_poleQuadratic_of_pairings D v (hweak (poleLeft D) u) (hweak (poleRight D) u)
  have hhalf : 0 < ε / 2 := half_pos hε
  have hlate : ∀ᶠ j in atTop, primeWindowModulationError D p c (y j) < ε / 2 ∧
      primeWindowPoleQuadratic D (v j) < ε / 2 :=
    (herr.eventually_lt_const hhalf).and (hpole.eventually_lt_const hhalf)
  obtain ⟨j, hjerr, hjpole⟩ := hlate.exists
  obtain ⟨hvs, hvnorm, hj⟩ := htest j u hu
  refine ⟨v j, hvs, hvnorm.trans hu₁, ?_⟩
  rw [hu₁, one_pow, mul_one] at hj
  let z := primeWindowSignedForm D p c (v j) - primeWindowSignedForm D p (fun _ ↦ 1) u
  have hjre : z.re < ε / 2 :=
    ((le_abs_self _).trans (Complex.abs_re_le_norm z)).trans_lt (hj.trans_lt hjerr)
  dsimp only [z, Complex.sub_re] at hjre
  linarith

end Masullo
