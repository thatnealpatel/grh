module

public import Theorems.RationalShortWindowStripTrace
public import Mathlib.Analysis.Convolution
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Theorems.RationalMellinDivisorJetBlock
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Signed coordinates for the short rational strip trace

The input is a real smooth log test with support in a short positive interval.
We use ordinary convolution (not convolution with the adjoint). The spectral
sum has the full order at each distinct zero in the open strip. Its signed
coordinates come from the checked scalar explicit formula, not from an
identification with any geometric operator.
-/

open Complex MeasureTheory Set
open scoped ContDiff Convolution ComplexConjugate Pointwise

namespace Masullo

local notation "M[" u "]" => compactLogMellin (fun t ↦ ((u : ℝ → ℝ) t : ℂ))
local notation "Lℝ" => ContinuousLinearMap.mul ℝ ℝ
local notation "Lℂ" => ContinuousLinearMap.mul ℂ ℂ

/-- The distinct zeros omitted by the open strip. Both edges are included. -/
public abbrev rationalShortOmittedZeros (a : ℝ) : Set criticalStripZetaZeros :=
  {ρ | a ≤ |(shiftedZetaZero ρ).re|}

/-- The negative open-strip sum on ordinary convolutions, expressed in product
Mellin coordinates with the positive log exponent. -/
@[expose] public noncomputable def rationalShortStripTrace (a : ℝ) (u v : ℝ → ℝ) : ℂ :=
  -∑' ρ : rationalRadialStripZeros a,
    (zetaZeroOrder ρ.val : ℂ) * M[u] (shiftedZetaZero ρ.val) * M[v] (shiftedZetaZero ρ.val)

private theorem mellin_real {u : ℝ → ℝ} (r : ℝ) :
    M[u] (r : ℂ) = ((∫ t, u t * Real.exp (r * t) : ℝ) : ℂ) := by
  simp only [compactLogMellin, ← ofReal_mul, ← ofReal_exp, integral_complex_ofReal]

private theorem re_mellin_mul_real (u v : ℝ → ℝ) (r : ℝ) :
    (M[u] (r : ℂ) * M[v] (r : ℂ)).re = (M[u] (r : ℂ)).re * (M[v] (r : ℂ)).re := by
  simp [mellin_real]

private theorem shortConvolution {l r : ℝ} {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hsu : tsupport u ⊆ Ioo l r) (hsv : tsupport v ⊆ Ioo l r) :
    let f := u ⋆[Lℝ, volume] v
    ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo (l + l) (r + r) ∧
    M[f] = M[u] * M[v] := by
  have hcu : HasCompactSupport u := isCompact_Icc.of_isClosed_subset isClosed_closure
    (hsu.trans Ioo_subset_Icc_self)
  have hcv : HasCompactSupport v := isCompact_Icc.of_isClosed_subset isClosed_closure
    (hsv.trans Ioo_subset_Icc_self)
  intro f
  have hf : ContDiff ℝ ∞ f := hcv.contDiff_convolution_right Lℝ
    (hu.continuous.integrable_of_hasCompactSupport hcu).locallyIntegrable hv
  have hc := hcu.convolution Lℝ (μ := volume) hcv
  have hs : tsupport f ⊆ tsupport u + tsupport v := closure_minimal
    ((support_convolution_subset Lℝ).trans (add_subset_add subset_closure subset_closure))
    (IsCompact.add hcu hcv).isClosed
  refine ⟨hf, hc, hs.trans ?_, ?_⟩
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨add_lt_add (hsu hx).1 (hsv hy).1, add_lt_add (hsu hx).2 (hsv hy).2⟩
  · have hcast : (fun t ↦ (f t : ℂ)) =
        (fun t ↦ (u t : ℂ)) ⋆[Lℂ, volume] (fun t ↦ (v t : ℂ)) := by
      funext t
      simp [f, MeasureTheory.convolution, ← ofReal_mul, integral_complex_ofReal]
    rw [hcast]
    exact compactLogMellin_convolution (continuous_ofReal.comp hu.continuous)
      (hcu.comp_left ofReal_zero) (continuous_ofReal.comp hv.continuous) (hcv.comp_left ofReal_zero)

set_option linter.concreteInstances false

/-- On all smooth real inputs supported in the short window, the absolutely
convergent open-strip sum is the archimedean series minus the remaining polar
term plus the sum over exactly the omitted zeros. No count is needed. The
identity also holds after restriction to mass-zero tests. -/
public theorem rationalShortStripTrace_decomposition
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {a l r : ℝ} (hl : 0 < l) (hr : r + r ≤ Real.log 2) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hsu : tsupport u ⊆ Ioo l r) (hsv : tsupport v ⊆ Ioo l r) :
    let term (ρ : criticalStripZetaZeros) :=
      (zetaZeroOrder ρ : ℂ) * M[u] (shiftedZetaZero ρ) * M[v] (shiftedZetaZero ρ)
    Summable (fun ρ ↦ ‖term ρ‖) ∧
    HasSum (fun n ↦ M[u] (rationalShortArchExponent (n + 1)) * M[v] (rationalShortArchExponent (n + 1)))
      (rationalShortStripTrace a u v + M[u] (1 / 2) * M[v] (1 / 2) -
        ∑' ρ : rationalShortOmittedZeros a, term ρ.val) := by
  obtain ⟨hf, hc, hs, hM⟩ := shortConvolution hu hv hsu hsv
  obtain ⟨habs, harch⟩ := rationalShortWindow_fullTrace (add_pos hl hl) hf hc
    (hs.trans fun _ ht ↦ ⟨ht.1, ht.2.trans_le hr⟩)
  simp only [hM, Pi.mul_apply, mul_assoc] at habs harch ⊢
  refine ⟨habs, ?_⟩
  have hp : (rationalRadialStripZeros a)ᶜ = rationalShortOmittedZeros a := by
    ext ρ
    change ¬ |(shiftedZetaZero ρ).re| < a ↔ a ≤ |(shiftedZetaZero ρ).re|
    exact not_lt
  have hsum := habs.of_norm
  have hsplit := (hsum.subtype (· ∈ rationalRadialStripZeros a)).tsum_add_tsum_compl
    (s := rationalRadialStripZeros a) (hsum.subtype (· ∈ (rationalRadialStripZeros a)ᶜ))
  rw [hp] at hsplit
  rw [← hsplit] at harch
  convert harch using 1
  unfold rationalShortStripTrace
  simp only [mul_assoc]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The product-coordinate trace is the negative of the convergent
normalized radial strip sum on the ordinary convolution profile. -/
public theorem rationalShortStripTrace_radial_hasSum
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {a l r : ℝ} (hl : 0 < l) (hr : r + r ≤ Real.log 2) {u v : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hsu : tsupport u ⊆ Ioo l r) (hsv : tsupport v ⊆ Ioo l r) :
    let f := u ⋆[Lℝ, volume] v
    HasSum (fun ρ : rationalRadialStripZeros a ↦ (zetaZeroOrder ρ.val : ℂ) *
      rationalIdeleRadialMellin (fun t ↦ (f t : ℂ)) ρ.val) (-rationalShortStripTrace a u v) := by
  obtain ⟨habs, _⟩ := rationalShortStripTrace_decomposition hl hr hu hv hsu hsv (a := a)
  obtain ⟨hf, hc, _, hM⟩ := shortConvolution hu hv hsu hsv
  intro f
  have hff : Continuous f := hf.continuous
  have hfc : HasCompactSupport f := hc
  have hconv : M[f] = M[u] * M[v] := hM
  have hrad (s : ℂ) : rationalIdeleRadialMellin (fun t ↦ (f t : ℂ)) s =
      M[u] (s - 1 / 2) * M[v] (s - 1 / 2) :=
    (rationalIdeleRadialMellin_eq_shiftedCompactLogMellin
      (continuous_ofReal.comp hff) (hfc.comp_left ofReal_zero) s).trans (congrFun hconv _)
  simpa only [hrad, ← mul_assoc, rationalShortStripTrace, neg_neg, shiftedZetaZero, Function.comp_def] using
    (habs.of_norm.subtype (· ∈ rationalRadialStripZeros a)).hasSum

private noncomputable def conjZero (ρ : criticalStripZetaZeros) : criticalStripZetaZeros :=
  ⟨conj ρ.val, by
    obtain ⟨h, h₀, h₁⟩ := mem_criticalStripZetaZeros.mp ρ.property
    exact mem_criticalStripZetaZeros.mpr ⟨by simp [riemannZeta_conj, h], h₀, h₁⟩⟩

private theorem conjZero_shift (ρ : criticalStripZetaZeros) :
    shiftedZetaZero (conjZero ρ) = conj (shiftedZetaZero ρ) := by
  simp [conjZero, shiftedZetaZero, map_ofNat]

private theorem conjZero_involutive : Function.Involutive conjZero := fun ρ ↦ by
  apply Subtype.ext
  simp [conjZero]

private theorem conjZero_order (ρ : criticalStripZetaZeros) :
    zetaZeroOrder (conjZero ρ) = zetaZeroOrder ρ := by
  have hζ (σ : criticalStripZetaZeros) : AnalyticAt ℂ riemannZeta σ.val :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) _ <| by
      intro h
      have h' : (σ : ℂ) = 1 := mem_singleton_iff.mp h
      have hs := (mem_criticalStripZetaZeros.mp σ.property).2.2
      simp [h'] at hs
  have hderiv (n : ℕ) :
      iteratedDeriv n riemannZeta = conj ∘ iteratedDeriv n riemannZeta ∘ conj := by
    induction n with
    | zero => ext z; simp [riemannZeta_conj]
    | succ n ih =>
      simpa only [iteratedDeriv_succ, deriv_conj_conj] using congrArg deriv ih
  have he (n : ℕ) : iteratedDeriv n riemannZeta (conjZero ρ).val =
      conj (iteratedDeriv n riemannZeta ρ.val) := by
    have h := congrFun (hderiv n) (conj (ρ : ℂ))
    simpa [conjZero, Function.comp_def] using h
  have hρ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hζ ρ)).mp (zetaZeroOrder_cast_eq ρ).symm
  have hc := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hζ (conjZero ρ)) (n := zetaZeroOrder ρ)).mpr
    ⟨fun k hk ↦ by simp [he, hρ.1 k hk], by simpa [he] using hρ.2⟩
  exact ENat.natCast_inj.mp ((zetaZeroOrder_cast_eq (conjZero ρ)).trans hc)

private theorem mellin_conj (u : ℝ → ℝ) (z : ℂ) : M[u] (conj z) = conj (M[u] z) := by
  unfold compactLogMellin
  rw [← integral_conj]
  apply integral_congr_ae
  exact .of_forall fun t ↦ by simp [← Complex.exp_conj, map_mul]

/-- The strip sum on real inputs is real. Conjugating permutes the distinct
interior zeros and preserves their full analytic orders. -/
public theorem rationalShortStripTrace_real (a : ℝ) (u v : ℝ → ℝ) :
    (rationalShortStripTrace a u v).im = 0 := by
  have hm (ρ : criticalStripZetaZeros) (hρ : ρ ∈ rationalRadialStripZeros a) :
      conjZero ρ ∈ rationalRadialStripZeros a := by
    change |(shiftedZetaZero (conjZero ρ)).re| < a
    change |(shiftedZetaZero ρ).re| < a at hρ
    simpa only [conjZero_shift, conj_re] using hρ
  let e : rationalRadialStripZeros a ≃ rationalRadialStripZeros a :=
    { toFun := fun ρ ↦ ⟨conjZero ρ.val, hm ρ.val ρ.property⟩
      invFun := fun ρ ↦ ⟨conjZero ρ.val, hm ρ.val ρ.property⟩
      left_inv := fun ρ ↦ Subtype.ext (conjZero_involutive ρ.val)
      right_inv := fun ρ ↦ Subtype.ext (conjZero_involutive ρ.val) }
  have h : conj (rationalShortStripTrace a u v) = rationalShortStripTrace a u v := by
    unfold rationalShortStripTrace
    rw [map_neg, conj_tsum]
    congr 1
    exact (tsum_congr fun ρ ↦ by
      simp only [map_mul, map_natCast, e, Equiv.coe_fn_mk, conjZero_order, conjZero_shift, mellin_conj]).trans
      (e.tsum_eq _)
  have hi := congrArg Complex.im h
  rw [conj_im] at hi
  linarith

/-- The omitted zeros of strictly positive ordinate, one per nonreal
omitted conjugate pair. Orders do not enter this index set. -/
public abbrev rationalShortOmittedUpperZeros (a : ℝ) : Set criticalStripZetaZeros :=
  {ρ | ρ ∈ rationalShortOmittedZeros a ∧ 0 < (ρ : ℂ).im}

private theorem mellin_im_zero_of_real (u : ℝ → ℝ) {z : ℂ} (hz : z.im = 0) :
    (M[u] z).im = 0 := by
  have hc : conj z = z := Complex.ext (by simp) (by simp [hz])
  have he := congrArg Complex.im (mellin_conj u z)
  rw [hc, conj_im] at he
  linarith

/-- On the kernel of the omitted imaginary moments, the only potentially
negative direction is the surviving pole. This is a one-sided assertion;
it neither invokes the density bound nor realizes any negative direction. -/
public theorem rationalShortStripTrace_polarCorrected_nonneg
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {a l r : ℝ} (hl : 0 < l) (hr : r + r ≤ Real.log 2) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hsu : tsupport u ⊆ Ioo l r)
    (hi : ∀ ρ : rationalShortOmittedUpperZeros a, (M[u] (shiftedZetaZero ρ.val)).im = 0) :
    0 ≤ (rationalShortStripTrace a u u).re + (M[u] (1 / 2)).re ^ 2 := by
  obtain ⟨habs, harch⟩ := rationalShortStripTrace_decomposition hl hr hu hu hsu hsu (a := a)
  have hreal (ρ : rationalShortOmittedZeros a) : (M[u] (shiftedZetaZero ρ.val)).im = 0 := by
    rcases lt_trichotomy ρ.val.val.im 0 with hn | hz | hp
    · have hmem : conjZero ρ.val ∈ rationalShortOmittedUpperZeros a := by
        refine ⟨?_, ?_⟩
        · change a ≤ |(shiftedZetaZero (conjZero ρ.val)).re|
          rw [conjZero_shift, conj_re]
          exact ρ.property
        · simpa [conjZero] using hn
      have h := hi ⟨conjZero ρ.val, hmem⟩
      simp only [conjZero_shift, mellin_conj, conj_im, neg_eq_zero] at h
      exact h
    · apply mellin_im_zero_of_real
      simpa [shiftedZetaZero] using hz
    · exact hi ⟨ρ.val, ρ.property, hp⟩
  have ho : Summable (fun ρ : rationalShortOmittedZeros a ↦
      (zetaZeroOrder ρ.val : ℂ) * M[u] (shiftedZetaZero ρ.val) * M[u] (shiftedZetaZero ρ.val)) :=
    habs.of_norm.subtype (· ∈ rationalShortOmittedZeros a)
  have hpos : 0 ≤ (∑' ρ : rationalShortOmittedZeros a,
      (zetaZeroOrder ρ.val : ℂ) * M[u] (shiftedZetaZero ρ.val) * M[u] (shiftedZetaZero ρ.val)).re := by
    change 0 ≤ Complex.reCLM (∑' ρ : rationalShortOmittedZeros a, _)
    rw [Complex.reCLM.map_tsum ho]
    apply tsum_nonneg
    intro ρ
    simp only [Complex.reCLM_apply, mul_re, mul_im, hreal ρ, natCast_re, natCast_im,
       zero_mul, mul_zero, sub_zero, add_zero]
    rw [mul_assoc, ← pow_two]
    positivity
  have harch' := Complex.reCLM.hasSum harch
  have harchpos : 0 ≤ ∑' n, (M[u] (rationalShortArchExponent (n + 1)) *
      M[u] (rationalShortArchExponent (n + 1))).re := by
    apply tsum_nonneg
    intro n
    rw [re_mellin_mul_real, ← pow_two]
    positivity
  rw [show (∑' n, (M[u] (rationalShortArchExponent (n + 1)) *
        M[u] (rationalShortArchExponent (n + 1))).re) = _ from harch'.tsum_eq] at harchpos
  simp only [Complex.reCLM_apply, sub_re, add_re] at harchpos
  have hpole := re_mellin_mul_real u u ((1 : ℝ) / 2)
  push_cast at hpole
  rw [hpole, ← pow_two] at harchpos
  linarith

/-- The mass-zero real test space of the short-interval inertia problem. -/
@[expose] public noncomputable def rationalShortWindowTests (l r : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {u | ContDiff ℝ ∞ u ∧ tsupport u ⊆ Ioo l r ∧ (∫ t, u t) = 0}
  zero_mem' := by
    simp [contDiff_const, Pi.zero_def]
  add_mem' := by
    rintro u v ⟨hu, hsu, hmu⟩ ⟨hv, hsv, hmv⟩
    have hcu : HasCompactSupport u := isCompact_Icc.of_isClosed_subset isClosed_closure
      (hsu.trans Ioo_subset_Icc_self)
    have hcv : HasCompactSupport v := isCompact_Icc.of_isClosed_subset isClosed_closure
      (hsv.trans Ioo_subset_Icc_self)
    refine ⟨hu.add hv, (tsupport_add u v).trans (union_subset hsu hsv), ?_⟩
    change (∫ t, u t + v t) = 0
    rw [integral_add (hu.continuous.integrable_of_hasCompactSupport hcu)
      (hv.continuous.integrable_of_hasCompactSupport hcv), hmu, hmv, add_zero]
  smul_mem' := by
    rintro c u ⟨hu, hsu, hmu⟩
    refine ⟨hu.const_smul c, (tsupport_smul_subset_right (fun _ : ℝ ↦ c) u).trans hsu, ?_⟩
    change (∫ t, c * u t) = 0
    rw [integral_const_mul, hmu, mul_zero]

private theorem shortTest_integrable_mellin {l r : ℝ} (u : rationalShortWindowTests l r) (z : ℂ) :
    Integrable (fun t ↦ (u.val t : ℂ) * Complex.exp (z * (t : ℂ))) := by
  have hct : HasCompactSupport u.val := isCompact_Icc.of_isClosed_subset isClosed_closure
    (u.property.2.1.trans Ioo_subset_Icc_self)
  exact ((continuous_ofReal.comp u.property.1.continuous).mul
    (continuous_exp.comp (continuous_const.mul continuous_ofReal))).integrable_of_hasCompactSupport
      (hct.comp_left ofReal_zero).mul_right

private noncomputable def shortMellinLinear {l r : ℝ} (z : ℂ) : rationalShortWindowTests l r →ₗ[ℝ] ℂ where
  toFun u := M[u.val] z
  map_add' u v := by
    simp only [compactLogMellin, Submodule.coe_add, Pi.add_apply, ofReal_add, add_mul]
    exact integral_add (shortTest_integrable_mellin u z) (shortTest_integrable_mellin v z)
  map_smul' c u := by
    change (∫ t, ((c * u.val t : ℝ) : ℂ) * Complex.exp (z * (t : ℂ))) = c • M[u.val] z
    simp_rw [ofReal_mul, mul_assoc, integral_const_mul, Complex.real_smul, compactLogMellin]

/-- The short-window trace as a real bilinear form on the mass-zero test space. -/
public noncomputable def rationalShortStripBilinForm
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {l r : ℝ} (a : ℝ) (hl : 0 < l) (hr : r + r ≤ Real.log 2) :
    LinearMap.BilinForm ℝ (rationalShortWindowTests l r) := by
  let V := rationalShortWindowTests l r
  let F (u v : V) := (rationalShortStripTrace a u.val v.val).re
  let A (u v : V) (ρ : rationalRadialStripZeros a) := (zetaZeroOrder ρ.val : ℂ) *
    shortMellinLinear (shiftedZetaZero ρ.val) u * shortMellinLinear (shiftedZetaZero ρ.val) v
  have hF (u v : V) : F u v = -(∑' ρ, A u v ρ).re := by
    rw [← neg_re]
    rfl
  have hA (u v : V) : Summable (A u v) := by
    obtain ⟨h, _⟩ := rationalShortStripTrace_decomposition (a := a) hl hr
      u.property.1 v.property.1 u.property.2.1 v.property.2.1
    exact h.of_norm.subtype (· ∈ rationalRadialStripZeros a)
  have hsymm (u v : V) : F u v = F v u := by
    rw [hF, hF]
    congr 1
    exact congrArg Complex.re (tsum_congr fun ρ ↦ by simp only [A, mul_right_comm])
  have hadd (u v w : V) : F (u + v) w = F u w + F v w := by
    have h : A (u + v) w = fun ρ ↦ A u w ρ + A v w ρ := by
      funext ρ
      simp only [A, map_add, mul_add, add_mul]
    rw [hF, hF, hF, h, (hA u w).tsum_add (hA v w), add_re, neg_add]
  have hsmul (c : ℝ) (u v : V) : F (c • u) v = c • F u v := by
    have h : A (c • u) v = fun ρ ↦ (c : ℂ) * A u v ρ := by
      funext ρ
      simp only [A, map_smul, Complex.real_smul]
      ring
    rw [hF, hF, h, tsum_mul_left, smul_eq_mul, mul_neg]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact LinearMap.mk₂ ℝ F hadd hsmul
    (fun u v w ↦ (hsymm _ _).trans ((hadd v w u).trans (congrArg₂ (· + ·) (hsymm _ _) (hsymm _ _))))
    (fun c u v ↦ (hsymm _ _).trans ((hsmul c v u).trans (congrArg (c • ·) (hsymm _ _))))

/-- The bundled real form evaluates to the real part of the negative strip sum. -/
public theorem rationalShortStripBilinForm_apply
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {l r : ℝ} (a : ℝ) (hl : 0 < l) (hr : r + r ≤ Real.log 2) (u v : rationalShortWindowTests l r) :
    rationalShortStripBilinForm a hl hr u v = (rationalShortStripTrace a u.val v.val).re := by
  unfold rationalShortStripBilinForm
  rfl

/-- Symmetry follows from the two ordinary Mellin factors, with no adjoint. -/
public theorem rationalShortStripBilinForm_symm
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {l r : ℝ} (a : ℝ) (hl : 0 < l) (hr : r + r ≤ Real.log 2) (u v : rationalShortWindowTests l r) :
    rationalShortStripBilinForm a hl hr u v = rationalShortStripBilinForm a hl hr v u := by
  simp only [rationalShortStripBilinForm_apply, rationalShortStripTrace]
  exact congrArg (fun z : ℂ ↦ (-z).re) (tsum_congr fun _ ↦ mul_right_comm _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- For finitely many omitted conjugate pairs the negative dimension is at
most one plus their number. For the polar-corrected form it is at most
that number. These are upper bounds on every negative subspace, not an
assertion of attained inertia. -/
public theorem rationalShortStripTrace_finrank_bounds
    [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {a l r : ℝ} (hl : 0 < l) (hr : r + r ≤ Real.log 2)
    [Fintype (rationalShortOmittedUpperZeros a)]
    (W : Submodule ℝ (rationalShortWindowTests l r)) :
    let B := rationalShortStripBilinForm a hl hr
    ((∀ w : W, w ≠ 0 → B w.val w.val < 0) →
      FiniteDimensional ℝ W ∧ Module.finrank ℝ W ≤ 1 + Fintype.card (rationalShortOmittedUpperZeros a)) ∧
    ((∀ w : W, w ≠ 0 → B w.val w.val + (M[w.val.val] (1 / 2)).re ^ 2 < 0) →
      FiniteDimensional ℝ W ∧ Module.finrank ℝ W ≤ Fintype.card (rationalShortOmittedUpperZeros a)) := by
  dsimp only
  simp only [rationalShortStripBilinForm_apply]
  let N := rationalShortOmittedUpperZeros a → ℝ
  let P : W →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap.comp ((shortMellinLinear (1 / 2)).comp W.subtype)
  let Q : W →ₗ[ℝ] N := LinearMap.pi fun ρ ↦
    Complex.imCLM.toLinearMap.comp ((shortMellinLinear (shiftedZetaZero ρ.val)).comp W.subtype)
  have hnonneg (w : W) (hQ : Q w = 0) := rationalShortStripTrace_polarCorrected_nonneg (a := a)
    hl hr w.val.property.1 w.val.property.2.1 fun ρ ↦ congrFun hQ ρ
  constructor
  · intro hneg
    have hk (w : W) (hw : (P.prod Q) w = 0) : w = 0 := by
      have hp : (M[w.val.val] (1 / 2)).re = 0 := congrArg Prod.fst hw
      have h := hnonneg w (congrArg Prod.snd hw)
      rw [hp, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at h
      by_contra hn
      exact (hneg w hn).not_ge h
    have hi : Function.Injective (P.prod Q) := by
      intro x y h
      exact sub_eq_zero.mp (hk (x - y) ((P.prod Q).map_sub x y |>.trans (sub_eq_zero.mpr h)))
    refine ⟨FiniteDimensional.of_injective (P.prod Q) hi, ?_⟩
    simpa only [N, Module.finrank_prod, Module.finrank_self, Module.finrank_pi] using
      LinearMap.finrank_le_finrank_of_injective hi
  · intro hneg
    have hk (w : W) (hw : Q w = 0) : w = 0 := by
      by_contra hn
      exact (hneg w hn).not_ge (hnonneg w hw)
    have hi : Function.Injective Q := by
      intro x y h
      exact sub_eq_zero.mp (hk (x - y) (Q.map_sub x y |>.trans (sub_eq_zero.mpr h)))
    refine ⟨FiniteDimensional.of_injective Q hi, ?_⟩
    simpa only [N, Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective hi

end Masullo
