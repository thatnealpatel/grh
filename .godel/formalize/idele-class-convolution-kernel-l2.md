# Pointwise class-Haar convolution on L² inputs

Chapter 01, passage `cbe7541ca4910c70218c814152e02feb148c55a653b7a34c098d53717d68607b`, proof revision `fdf92798757da8d775b443c8af08eb1376f8031db2aca8bfcbf831469d0a9325`. [Receipt](cbe7541ca4910c70218c814152e02feb148c55a653b7a34c098d53717d68607b-fdf92798757da8d775b443c8af08eb1376f8031db2aca8bfcbf831469d0a9325.json). Owning exact-candidate check session: `01a2067e-7a16-743c-a308-7e83ee37c77e`. Writer base: `697feb624394c2fc95bc6162d040e06d20dd83ab`.

## Printed obligation and interpretation

Masullo, *The Music of the Primes*, 940 pages, 6,756,996 bytes. The writer verified the PDF SHA-256 against the [edition pin](../sources/masullo/README.md): `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. Printed pages equal one-based PDF ordinals (zero-based renderer index is page minus one). The writer rendered the pages at 220 dpi with `pdftoppm -gray -png`, used OCR to locate the passages, and inspected the display and symbol crops from the raster pixels.

- **§1.2.1(1)(a,b), p. 13; first unnumbered display on p. 14; §1.2.1(3), first paragraph of item (3), p. 15.** The base is \(I=[-a,a]\), \(a>0\), and \(\varphi\) is a compactly supported test whose support lies where \(|g|_F>1+\epsilon\), \(\epsilon>0\). The p. 14 display is \((A(\varphi)f)(x)=\int_{C_F}\varphi(g) f(g^{-1}x)\,d\bar\mu(g)\). Item (3) asserts kernel \(\varphi(xy^{-1})\) on the middle Hardy–Sobolev space \(W_I^{s,2}(C_F)(\chi|_{C_F^1})\), vanishing on the diagonal. This is not the difference kernel of item (4) or the kernel of the isotype operator extended by zero to the other isotypes.
- **Terminology 4.3.2.1, eigenspace display, p. 180; §9.3.1, inverse-left translation and Definition 9.3.1.1, (9.3.1.1)–(9.3.1.2), p. 419.** The subgroup eigenvalue is \(\chi(h)\) for the operation \(f(x)\mapsto f(h^{-1}x)\), not its complex conjugate. The operator in the printed definition is the Pettis regularization of continuous left translation. **Lemma 9.3.1.3, pp. 419–420** treats the test and completed spaces (degree \(s\ge 0\), including zero), with continuity from the locally convex inductive limit topology into the bounded-set operator topology. The proof uses a compact-support/invariance stage and the Mellin transform; the last line of its proof takes \(E=W_I^s(G)\). The scalar proof below does not invoke the lemma or verify that step.
- **Definition A.1.4.1, (A.1.4.1)–(A.1.4.2), p. 542; Definition A.3.2.1 and volume display (A.3.2.1), pp. 559–560.** The class group is the topological quotient of idèles by principal idèles, with the descended norm and its norm-one kernel. Counting measure on \(F^\times\) gives the class quotient Haar from idèle Haar; \(dt/t\) in the norm factor and the prescribed norm-one volume fix the convention. Here Lean takes a single Borel class Haar \(\mu\) throughout. The result is independent of the choice of scale and in particular applies to the source normalization. The client uses the actual counting-quotient/log-product construction from `Theorems.IdeleClassWeil`; it does not compute the volume in the display.
- **§1.1.3, p. 11, compact-interval norm display; Lemma 9.2.2.10(2), (9.2.2.34), p. 417.** These displays use squared modulus, a square root outside the integral, the maximum of the two norm powers, and a real exponent \(s/2\) on \(1+|\log|y|_F|^2\). With \(I=[-a,a]\), the density is \(w(y)=\max(e^{-2az},e^{2az})(1+z^2)^{s/2}\), \(z=\log|y|_F\). It is the existing scalar formula `logSobolevWeight (-a) a s z` composed with the class log norm, not a new definition of the completed space. The [unsquared p. 36 display](../walk/first-hardy-sobolev-display.md) does not give this norm; we use the squared displays directly.

## Checked partial proof

The five endpoints in [`Theorems.IdeleClassConvolutionKernelL2`](../../Proofs/Theorems/IdeleClassConvolutionKernelL2.lean) quantify over every number field \(K\), the actual `NumberField.IdeleClassGroup (𝓞 K) K` with its Borel structure, and arbitrary Haar \(\mu\) there. They use the existing class topology and norm-one subgroup. A continuous compactly supported kernel is in \(L^2(\mu)\) by finiteness of Haar on compacts; the Lean results also apply to noncontinuous kernels in \(L^2(\mu)\). Denote the scalar kernel integral by \(T_\varphi f(x)\).

- `Masullo.ideleClass_convolution_kernel_memLp`: for `MemLp φ 2 μ` and `MemLp f 2 μ`, both products in the two formulas are integrable for **every** \(x\) and the integrals equal. The change of variables \(g=x/y\) is inversion followed by left multiplication by \(x\), so it preserves abelian class Haar; \((x/y)^{-1}x=y\). Preservation transports both `MemLp` and the \(L^2\) norm. Product integrability uses the `MemLp` multiplication lemma.
- `Masullo.ideleClass_convolution_kernel_ae_congr`: given \(\varphi=\varphi'\) and \(f=f'\) \(\mu\)-a.e., the scalar integrals agree at **each** \(x\). The only null-set pullback needed is that of the kernel factor by the measure-preserving map for that fixed \(x\). Together with the first endpoint this justifies changing representatives of actual \(L^2\) inputs and kernels, rather than treating point values of an equivalence class as invariants. The equality itself needs no `MemLp` assumption.
- `Masullo.norm_ideleClass_convolution_kernel_le`: for the two `MemLp` hypotheses, \(|T_\varphi f(x)|\le\|\varphi\|_{L^2(\mu)}\|f\|_{L^2(\mu)}\) for every \(x\), by applying Hölder to the product of the norms at exponents 2 and 2. The right side is `eLpNorm` converted to finite reals.
- `Masullo.ideleClass_convolution_kernel_isotype_ae`: under the same `MemLp` hypotheses, if \(f(h^{-1}y)=\chi(h) f(y)\) \(\mu\)-a.e. for a fixed \(h\in C_F^1\), then \(T_\varphi f(h^{-1}x)=\chi(h)T_\varphi f(x)\) for every \(x\). For each \(h\), its a.e. relation is pulled back along \(g\mapsto x/g\) in the inverse-left integral. There is no assumption of a common conull set for all \(h\). This verifies scalar equivariance, not a statement about membership in the manuscript's completed isotype.
- `Masullo.tendstoUniformly_ideleClass_convolution_kernel_of_measure_le`: for any filter and \(\mu\le\nu\), if \(u_i\to v\) in `Lp ℂ 2 ν` and \(\varphi\) is in \(L^2(\mu)\), the functions \(T_\varphi u_i\) converge uniformly on the entire class group to \(T_\varphi v\). Absolute continuity permits the a.e. subtraction of representatives under \(\mu\); monotonicity bounds the Haar norm of the difference by the \(L^2(\nu)\) norm. In particular, the client checks \(w\ge1\) for the symmetric squared weight (since one exponential is at least 1 and \(s\ge0\)) and applies this result with \(\nu=w\mu\). The integrals in both formulas are still against \(\mu\), not against \(w\mu\).

These formulas agree with the existing continuous-input formula wherever both hypotheses hold: the input, kernel, measure and both integral expressions are literally the same. The [earlier handoff](idele-class-convolution-kernel.md) replays the four original endpoints (also listed in the receipt at `0c1d5fcef0853fb9f213253b7f60dbd15173c8f9`): `ideleClass_convolution_kernel`, `ideleClass_convolution_kernel_isotype`, `ideleClass_convolution_kernel_eq_zero_of_norm_le`, `ideleClass_convolution_kernel_diagonal`. The still-existing support results are pointwise statements about the **given test** \(\varphi\), not about diagonal values for arbitrary a.e. replacements of it. A later addition to that defining file, `ideleClass_convolution_star_self_eq_zero_of_one` at `23c2c523ebe18b1e4b2d4ebf273dc855f842793f`, did not change those original declarations. This update leaves the earlier Lean file unchanged and changes the receipt to cite the new endpoints.

## Remaining bridge

Uniform convergence of scalar representatives on the class group does not give output weighted-L² integrability or convergence. To finish item (3), identify the source completed middle isotype inside the actual weighted \(L^2(w\mu)\), prove density of the source tests in that model, and supply the bounded inverse-left action agreeing with the test integral and preserving the completed isotype. Then the bounded action gives weighted-L² convergence of outputs; an a.e.-convergent subsequence identifies the operator's output with the pointwise kernel limit (using \(\mu\le w\mu\)). These source identification, density, output bound and a.e. comparison steps are not checked here. The [rational-radial result](rational-radial-hilbert-convolution.md) is for \(\mathbb Q\) and the trivial isotype, not a proof of these general premises. Neither the checked advance nor the earlier support vanishing addresses quotient descent, trace class, or a trace identity.

## Reproduce the checks

The writer ran `lake build --wfail +Theorems.IdeleClassConvolutionKernelL2 +Theorems.IdeleClassWeil +Theorems.RadialHardySobolevCompletion` (8275 jobs), ordinary joint imports with `#check @Name` and `#print axioms Name` for each of the five receipt endpoints, and the following client with `lake env lean`. The signatures had exactly the hypotheses and conclusions described above. All five axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. No admitted proofs or native computation. The exact integrated candidate and independent review are checked and recorded separately by the owning session.

```lean
import Theorems.IdeleClassConvolutionKernelL2
import Theorems.IdeleClassWeil
import Theorems.RadialHardySobolevCompletion
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.WithDensity

open Filter Masullo MeasureTheory NumberField
open scoped ENNReal Topology

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)
local notation "I₁" => ideleNormOne (K := K)
variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

-- Evaluate an actual quotient-Haar L² class against a continuous compact kernel.
-- An arbitrary representative can be used in the inverse-left integral instead.
example (η : Measure I₁) [η.IsHaarMeasure] (b : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) (hfin : η (ideleFundamentalDomain b r) < ⊤)
    {φ : C → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    let μ := ideleClassQuotientMeasure η b r
    ∀ (u : Lp ℂ 2 μ) (f : C → ℂ), f =ᵐ[μ] u → ∀ (χ : PontryaginDual C₁) (h : C₁),
      ((fun y : C ↦ f ((h : C)⁻¹ * y)) =ᵐ[μ] fun y ↦ (χ h : ℂ) * f y) → ∀ x : C,
      Integrable (fun g ↦ φ g * f (g⁻¹ * x)) μ ∧
      Integrable (fun y ↦ φ (x / y) * f y) μ ∧
      ((∫ g, φ g * f (g⁻¹ * x) ∂μ) = ∫ y, φ (x / y) * u y ∂μ) ∧
      ‖∫ y, φ (x / y) * u y ∂μ‖ ≤ (eLpNorm φ 2 μ).toReal * ‖u‖ ∧
      (∫ y, φ (((h : C)⁻¹ * x) / y) * u y ∂μ) = (χ h : ℂ) * ∫ y, φ (x / y) * u y ∂μ := by
  intro μ u f hfu χ h hiso x
  let : μ.IsHaarMeasure := ideleClassQuotientMeasure_isHaarMeasure η b r hr hfin
  have hφ₂ : MemLp φ 2 μ := hφ.memLp_of_hasCompactSupport hc
  have hf₂ : MemLp f 2 μ := (Lp.memLp u).ae_eq hfu.symm
  obtain ⟨hi, hj, he⟩ := ideleClass_convolution_kernel_memLp μ hφ₂ hf₂ x
  have hrep (z : C) := ideleClass_convolution_kernel_ae_congr μ (EventuallyEq.rfl : φ =ᵐ[μ] φ) hfu z
  refine ⟨hi, hj, he.trans (hrep x), ?_, ?_⟩
  · rw [Lp.norm_def]
    exact norm_ideleClass_convolution_kernel_le μ hφ₂ (Lp.memLp u) x
  · rw [← hrep ((h : C)⁻¹ * x), ← hrep x]
    exact ideleClass_convolution_kernel_isotype_ae μ hφ₂ hf₂ χ h hiso x

-- The actual symmetric squared density, expressed using the existing weight
-- formula in the class log-norm coordinate. This is ambient L², not the
-- manuscript's completed test space. The proof permits s = 0.
example (η : Measure I₁) [η.IsHaarMeasure] (b : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ p, ideleIdealClassNormOne (r p) = p) (hfin : η (ideleFundamentalDomain b r) < ⊤)
    {φ : C → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    let μ := ideleClassQuotientMeasure η b r
    let w : C → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (logSobolevWeight (-a) a s (Real.log (ideleClassNorm y)))
    ∀ (u : ℕ → Lp ℂ 2 (μ.withDensity w)) (v : Lp ℂ 2 (μ.withDensity w)),
      Tendsto u atTop (𝓝 v) →
        TendstoUniformly (fun n x ↦ ∫ y, φ (x / y) * u n y ∂μ)
          (fun x ↦ ∫ y, φ (x / y) * v y ∂μ) atTop := by
  intro μ w u v huv
  let : μ.IsHaarMeasure := ideleClassQuotientMeasure_isHaarMeasure η b r hr hfin
  have hw (y : C) : 1 ≤ w y := by
    let z := Real.log (ideleClassNorm y)
    have hexp (t : ℝ) (ht : 0 ≤ t) : 1 ≤ Real.exp t := Real.exp_zero ▸ Real.exp_le_exp.mpr ht
    have hl : 1 ≤ max (Real.exp (2 * -a * z)) (Real.exp (2 * a * z)) := by
      rcases le_total z 0 with hz | hz
      · exact (hexp _ (mul_nonneg_of_nonpos_of_nonpos (by linarith) hz)).trans (le_max_left ..)
      · exact (hexp _ (mul_nonneg (by positivity) hz)).trans (le_max_right ..)
    have hp : 1 ≤ (1 + z ^ 2) ^ (s / 2) :=
      Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg z)) (div_nonneg hs (by norm_num))
    simpa only [w, z, logSobolevWeight, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (one_le_mul_of_one_le_of_one_le hl hp)
  have hle : μ ≤ μ.withDensity w := by
    have hd : μ.withDensity (1 : C → ℝ≥0∞) ≤ μ.withDensity w := withDensity_mono (ae_of_all μ hw)
    rwa [withDensity_one] at hd
  exact tendstoUniformly_ideleClass_convolution_kernel_of_measure_le μ hle
    (hφ.memLp_of_hasCompactSupport hc) huv
```
