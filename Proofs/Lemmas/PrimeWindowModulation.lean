module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Lemmas.PrimePhaseRecurrence
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Tactic

/-! # Uniform modulation of the signed prime-window form

Source: `bdd74f2a:.godel/adhoc/prime-translation-norm.md`, §1 (lines 7–26)
and the use of its modulation argument in §3 (lines 44–50).
Owning check session: `01a20e74-7a96-7653-9648-0eb1c4d5d43d`.

Scope: the strict-cutoff, negative prime form on complex `L²` zero extensions
from `[0,D]`. One sequence of real frequencies tending to `+∞` removes the
unit prime phases with an error uniform on the unit ball; the same modulations
are weakly null on fixed tests. No spectral supremum, compact-correction bound,
or archimedean cost estimate is asserted.
-/

open Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate InnerProductSpace Topology

namespace Masullo

local notation "𝓗" => Lp ℂ 2 (volume : Measure ℝ)

/-- The full-line `L²` model of zero extensions from `[0,D]`. -/
@[expose] public def PrimeWindowSupported (D : ℝ) (u : 𝓗) : Prop :=
  ∀ᵐ x ∂volume, x ∉ Set.Icc 0 D → u x = 0

/-- The unimodular factor for modulation by angular frequency `y`. -/
@[expose] public noncomputable def primeWindowPhase (y x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (y : ℂ) * (x : ℂ))

private theorem phase_norm (y x : ℝ) : ‖primeWindowPhase y x‖ = 1 := by
  rw [primeWindowPhase, show Complex.I * (y : ℂ) * (x : ℂ) = ((y * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem phase_add (y x t : ℝ) :
    primeWindowPhase y (x + t) = primeWindowPhase y x * primeWindowPhase y t := by
  simp only [primeWindowPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem phase_neg (y t : ℝ) : primeWindowPhase y (-t) = conj (primeWindowPhase y t) := by
  rw [primeWindowPhase, primeWindowPhase, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring_nf

private theorem phase_mul_conj (y x : ℝ) : primeWindowPhase y x * conj (primeWindowPhase y x) = 1 := by
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, phase_norm]

private theorem modulation_memLp (y : ℝ) (u : 𝓗) :
    MemLp (fun x ↦ primeWindowPhase y x * u x) 2 volume :=
  (Lp.memLp u).congr_norm ((by unfold primeWindowPhase; fun_prop :
    Continuous (primeWindowPhase y)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
    (.of_forall fun x ↦ by rw [norm_mul, phase_norm, one_mul])

/-- Multiplication by `exp (I * y * x)` on full-line complex `L²`. -/
public noncomputable def primeWindowModulate (y : ℝ) (u : 𝓗) : 𝓗 :=
  (modulation_memLp y u).toLp _

public theorem primeWindowModulate_ae (y : ℝ) (u : 𝓗) :
    primeWindowModulate y u =ᵐ[volume] fun x ↦ primeWindowPhase y x * u x :=
  (modulation_memLp y u).coeFn_toLp

public theorem norm_primeWindowModulate (y : ℝ) (u : 𝓗) :
    ‖primeWindowModulate y u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (primeWindowModulate_ae y u)]
  congr 1
  exact eLpNorm_congr_norm_ae (modulation_memLp y u).aestronglyMeasurable
    (Lp.aestronglyMeasurable u) (.of_forall fun x ↦ by rw [norm_mul, phase_norm, one_mul])

public theorem PrimeWindowSupported.modulate {D : ℝ} {u : 𝓗}
    (hu : PrimeWindowSupported D u) (y : ℝ) : PrimeWindowSupported D (primeWindowModulate y u) := by
  filter_upwards [hu, primeWindowModulate_ae y u] with x hux hMx hx
  rw [hMx, hux hx, mul_zero]

private theorem translate_preserving (t : ℝ) :
    MeasurePreserving (fun x : ℝ ↦ x + t) volume volume := measurePreserving_add_right volume t

/-- Full-line translation by `x ↦ x + t`; its pairing with a supported test is
that of the translation compressed to the window. -/
public noncomputable def primeWindowTranslate (t : ℝ) (u : 𝓗) : 𝓗 :=
  Lp.compMeasurePreserving _ (translate_preserving t) u

public theorem primeWindowTranslate_ae (t : ℝ) (u : 𝓗) :
    primeWindowTranslate t u =ᵐ[volume] fun x ↦ u (x + t) :=
  Lp.coeFn_compMeasurePreserving u (translate_preserving t)

public theorem norm_primeWindowTranslate (t : ℝ) (u : 𝓗) :
    ‖primeWindowTranslate t u‖ = ‖u‖ := Lp.norm_compMeasurePreserving u (translate_preserving t)

private theorem inner_translate_integral (t : ℝ) (v u : 𝓗) :
    ⟪v, primeWindowTranslate t u⟫_ℂ = ∫ x, u (x + t) * conj (v x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [primeWindowTranslate_ae t u] with x hx
  rw [RCLike.inner_apply, hx]

/-- For a zero-extended test the full-line pairing is exactly the window pairing. -/
public theorem primeWindowTranslate_inner_window (t : ℝ) (u : 𝓗) {D : ℝ} {v : 𝓗}
    (hv : PrimeWindowSupported D v) :
    ⟪v, primeWindowTranslate t u⟫_ℂ = ∫ x in Set.Icc 0 D, u (x + t) * conj (v x) := by
  rw [inner_translate_integral]
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hv] with x hvx hx
  simp [hvx hx]

/-- Reversing the shift gives the adjoint, also in the pairings compressed to the window. -/
public theorem primeWindowTranslate_adjoint (t : ℝ) (v u : 𝓗) :
    ⟪v, primeWindowTranslate t u⟫_ℂ = ⟪primeWindowTranslate (-t) v, u⟫_ℂ := by
  rw [inner_translate_integral, L2.inner_def]
  calc
    _ = ∫ x, u x * conj (v (x + -t)) := by
      simpa only [add_neg_cancel_right] using
        integral_add_right_eq_self (fun x ↦ u x * conj (v (x + -t))) t
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [primeWindowTranslate_ae (-t) v] with x hx
      rw [RCLike.inner_apply, hx]

/-- Modulation multiplies an actual translated pairing by the phase at its shift.
In particular, the backward/adjoint term has the conjugate phase. -/
public theorem primeWindowModulate_inner_translate (y t : ℝ) (v u : 𝓗) :
    ⟪primeWindowModulate y v, primeWindowTranslate t (primeWindowModulate y u)⟫_ℂ =
      primeWindowPhase y t * ⟪v, primeWindowTranslate t u⟫_ℂ := by
  rw [inner_translate_integral, inner_translate_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [primeWindowModulate_ae y v,
    (translate_preserving t).quasiMeasurePreserving.ae_eq_comp (primeWindowModulate_ae y u)]
    with x hv hu
  change primeWindowModulate y u (x + t) = primeWindowPhase y (x + t) * u (x + t) at hu
  rw [hv, hu, phase_add, map_mul]
  calc
    _ = (primeWindowPhase y x * conj (primeWindowPhase y x)) *
        (primeWindowPhase y t * (u (x + t) * conj (v x))) := by ring
    _ = _ := by rw [phase_mul_conj, one_mul]

/-- Modulation is weakly null at positive infinity: for each fixed pair of full-line
`L²` vectors the pairing is the Fourier integral of their integrable product. -/
public theorem tendsto_primeWindowModulate_inner (v u : 𝓗) :
    Tendsto (fun y : ℝ ↦ ⟪v, primeWindowModulate y u⟫_ℂ) atTop (𝓝 0) := by
  let f : ℝ → ℂ := fun x ↦ ⟪v x, u x⟫_ℂ
  have hf : Integrable f := L2.integrable_inner v u
  let F := hf.toL1 f
  have hscale : Tendsto (fun y : ℝ ↦ -y / (2 * Real.pi)) atTop (cocompact ℝ) :=
    (Tendsto.atBot_div_const (by positivity) tendsto_neg_atTop_atBot).mono_right atBot_le_cocompact
  refine ((Real.tendsto_integral_exp_smul_cocompact (⇑F)).comp hscale).congr' (.of_forall fun y ↦ ?_)
  simp only [Function.comp_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1, primeWindowModulate_ae y u] with x hFx hx
  have h : 2 * Real.pi * -(x * (-y / (2 * Real.pi))) = y * x := by
    field_simp [Real.pi_ne_zero]
  have hphase : Complex.exp ((↑(2 * Real.pi * -(x * (-y / (2 * Real.pi)))) : ℂ) * Complex.I) =
      primeWindowPhase y x := by
    rw [h, primeWindowPhase, Complex.ofReal_mul]
    congr 1
    ring
  rw [Circle.smul_def, Real.fourierChar_apply, hphase, show F x = f x from hFx, hx]
  simp only [f, RCLike.inner_apply, smul_eq_mul, mul_assoc]

section Powers

variable {ι : Type*} [Fintype ι]

/-- All positive powers of the indexed primes with `log (p ^ k) < D`.
The inclusive ceiling on the exponent is only a finite search bound. -/
@[expose] public noncomputable def primeWindowPowers (D : ℝ) (p : ι → ℕ) : Finset (ι × ℕ) := by
  classical
  exact (Finset.univ ×ˢ Finset.Icc 1 ⌈D / Real.log 2⌉₊).filter
    (fun ik ↦ Real.log ((p ik.1 ^ ik.2 : ℕ) : ℝ) < D)

public theorem mem_primeWindowPowers {D : ℝ} {p : ι → ℕ} (hp : ∀ i, (p i).Prime) (i : ι) (k : ℕ) :
    (i, k) ∈ primeWindowPowers D p ↔ 1 ≤ k ∧ Real.log ((p i ^ k : ℕ) : ℝ) < D := by
  classical
  simp only [primeWindowPowers, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_Icc]
  refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, ?_⟩, h.2⟩⟩
  have hp₂ : (2 : ℝ) ≤ (p i : ℝ) := by exact_mod_cast (hp i).two_le
  have hlog : Real.log 2 ≤ Real.log (p i : ℝ) := Real.log_le_log (by norm_num) hp₂
  have hk : (k : ℝ) * Real.log 2 < D := calc
    _ ≤ (k : ℝ) * Real.log (p i : ℝ) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
    _ = Real.log ((p i ^ k : ℕ) : ℝ) := by rw [Nat.cast_pow, Real.log_pow]
    _ < D := h.2
  exact Nat.cast_le.mp (((lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hk).le.trans
    (Nat.le_ceil (D / Real.log 2)))

/-- The prime weight `Λ(p ^ k) / sqrt (p ^ k)`. -/
@[expose] public noncomputable def primeWindowPowerWeight (p k : ℕ) : ℝ :=
  Λ (p ^ k) / Real.sqrt ((p ^ k : ℕ) : ℝ)

/-- The forward translation with coefficient `a` and its conjugate-coefficient
adjoint, tested on `u`. Lean's inner product is linear in the second variable. -/
@[expose] public noncomputable def primeWindowShiftForm (t : ℝ) (a : ℂ) (u : 𝓗) : ℂ :=
  a * ⟪u, primeWindowTranslate t u⟫_ℂ + conj a * ⟪u, primeWindowTranslate (-t) u⟫_ℂ

/-- The negative prime part of the Weil form on supported tests, with a general
unit coefficient `c i` at each active prime and its `k`-th power at `p i ^ k`. -/
@[expose] public noncomputable def primeWindowSignedForm (D : ℝ) (p : ι → ℕ) (c : ι → ℂ)
    (u : 𝓗) : ℂ :=
  -(∑ ik ∈ primeWindowPowers D p, (primeWindowPowerWeight (p ik.1) ik.2 : ℂ) *
    primeWindowShiftForm (Real.log ((p ik.1 ^ ik.2 : ℕ) : ℝ)) (c ik.1 ^ ik.2) u)

/-- Explicit uniform error coefficient, independent of the test vector. -/
@[expose] public noncomputable def primeWindowModulationError (D : ℝ) (p : ι → ℕ) (c : ι → ℂ)
    (y : ℝ) : ℝ :=
  ∑ ik ∈ primeWindowPowers D p, |primeWindowPowerWeight (p ik.1) ik.2| *
    (2 * ‖c ik.1 ^ ik.2 * primeWindowPhase y (Real.log ((p ik.1 ^ ik.2 : ℕ) : ℝ)) - 1‖)

/-- A single prime-power pair acquires a phase on the forward coefficient and its
conjugate on the adjoint coefficient. -/
public theorem primeWindowShiftForm_modulate (y t : ℝ) (a : ℂ) (u : 𝓗) :
    primeWindowShiftForm t a (primeWindowModulate y u) =
      primeWindowShiftForm t (a * primeWindowPhase y t) u := by
  simp only [primeWindowShiftForm, primeWindowModulate_inner_translate, phase_neg, map_mul, mul_assoc]

private theorem norm_shiftForm_sub_one (t : ℝ) (a : ℂ) (u : 𝓗) :
    ‖primeWindowShiftForm t a u - primeWindowShiftForm t 1 u‖ ≤ 2 * ‖a - 1‖ * ‖u‖ ^ 2 := by
  let F := ⟪u, primeWindowTranslate t u⟫_ℂ
  let B := ⟪u, primeWindowTranslate (-t) u⟫_ℂ
  have h (s : ℝ) : ‖⟪u, primeWindowTranslate s u⟫_ℂ‖ ≤ ‖u‖ ^ 2 := by
    simpa only [norm_primeWindowTranslate, pow_two] using
      norm_inner_le_norm (𝕜 := ℂ) u (primeWindowTranslate s u)
  have hconj : ‖conj a - 1‖ = ‖a - 1‖ := by
    simpa only [map_sub, map_one] using Complex.norm_conj (a - 1)
  calc
    _ = ‖(a - 1) * F + (conj a - 1) * B‖ := by
      simp only [primeWindowShiftForm, map_one, one_mul]
      congr 1
      ring
    _ ≤ ‖(a - 1) * F‖ + ‖(conj a - 1) * B‖ := norm_add_le _ _
    _ = ‖a - 1‖ * ‖F‖ + ‖a - 1‖ * ‖B‖ := by rw [norm_mul, norm_mul, hconj]
    _ ≤ ‖a - 1‖ * ‖u‖ ^ 2 + ‖a - 1‖ * ‖u‖ ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left (h t) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (h (-t)) (norm_nonneg _))
    _ = _ := by ring

/-- Uniform modulation bound, obtained from the finite triangle inequality and
Cauchy–Schwarz for the full-line translates. It holds in particular on the window. -/
public theorem norm_primeWindowSignedForm_modulate_sub (D : ℝ) (p : ι → ℕ) (c : ι → ℂ)
    (y : ℝ) (u : 𝓗) :
    ‖primeWindowSignedForm D p c (primeWindowModulate y u) -
        primeWindowSignedForm D p (fun _ ↦ 1) u‖ ≤ primeWindowModulationError D p c y * ‖u‖ ^ 2 := by
  rw [primeWindowSignedForm, primeWindowSignedForm, neg_sub_neg, ← neg_sub, norm_neg,
    ← Finset.sum_sub_distrib, primeWindowModulationError, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ik _ ↦ ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, primeWindowShiftForm_modulate,
    one_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_shiftForm_sub_one _ _ _) (abs_nonneg _)

/-- The same escaping frequency sequence untwists the entire signed form uniformly
on supported unit tests and gives weak-null modulations against every fixed test.
The quantitative error bound is homogeneous in the input `L²` norm. -/
public theorem exists_primeWindowModulation (D : ℝ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    ∃ y : ℕ → ℝ, Tendsto y atTop atTop ∧
      Tendsto (fun j ↦ primeWindowModulationError D p c (y j)) atTop (𝓝 0) ∧
      (∀ j (u : 𝓗), PrimeWindowSupported D u →
        PrimeWindowSupported D (primeWindowModulate (y j) u) ∧
        ‖primeWindowModulate (y j) u‖ = ‖u‖ ∧
        ‖primeWindowSignedForm D p c (primeWindowModulate (y j) u) -
          primeWindowSignedForm D p (fun _ ↦ 1) u‖ ≤ primeWindowModulationError D p c (y j) * ‖u‖ ^ 2) ∧
      ∀ v u : 𝓗, Tendsto (fun j ↦ ⟪v, primeWindowModulate (y j) u⟫_ℂ) atTop (𝓝 0) := by
  obtain ⟨y, hy, -, hcancel⟩ := exists_primePowerPhaseCancellation p hp hinj c hc
  refine ⟨y, hy, ?_, fun j u hu ↦ ⟨hu.modulate _, norm_primeWindowModulate _ _,
    norm_primeWindowSignedForm_modulate_sub D p c _ u⟩,
    fun v u ↦ (tendsto_primeWindowModulate_inner v u).comp hy⟩
  have hterm (ik : ι × ℕ) : Tendsto (fun j ↦ |primeWindowPowerWeight (p ik.1) ik.2| *
      (2 * ‖c ik.1 ^ ik.2 * primeWindowPhase (y j) (Real.log ((p ik.1 ^ ik.2 : ℕ) : ℝ)) - 1‖))
      atTop (𝓝 0) := by
    have hdiff := ((hcancel ik.1 ik.2).sub (tendsto_const_nhds (x := (1 : ℂ)))).norm
    simpa only [sub_self, norm_zero, mul_zero, primeWindowPhase] using
      (hdiff.const_mul 2).const_mul |primeWindowPowerWeight (p ik.1) ik.2|
  simpa only [primeWindowModulationError, Finset.sum_const_zero] using
    tendsto_finsetSum (primeWindowPowers D p) (fun ik _ ↦ hterm ik)

end Powers

end Masullo
