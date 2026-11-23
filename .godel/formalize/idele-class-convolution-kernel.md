# Regular class-Haar kernel and support vanishing

Chapter 01, passage `cbe7541ca4910c70218c814152e02feb148c55a653b7a34c098d53717d68607b`, proof revision `fdf92798757da8d775b443c8af08eb1376f8031db2aca8bfcbf831469d0a9325`. [Receipt](cbe7541ca4910c70218c814152e02feb148c55a653b7a34c098d53717d68607b-fdf92798757da8d775b443c8af08eb1376f8031db2aca8bfcbf831469d0a9325.json). Owning integration session `01a2064a-fc1d-73f1-bb0a-52615e099bbf`.

## Rendered source

Masullo, *The Music of the Primes*, 940 pages and 6,756,996 bytes. Checked PDF SHA-256 against the [edition pin](../sources/masullo/README.md): `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. Printed page and one-based PDF ordinal agree at these locators. The reading uses page rasters and crops of the displays, with extracted text for navigation.

- **§1.2.1(3), p. 15:** on the middle space \(W_I^{s,2}(C_F)(\chi|_{C_F^1})\), \(A(\varphi)\) has kernel \(\varphi(xy^{-1})\); since \(\varphi\) is supported strictly above norm one, it vanishes on the diagonal. This is distinct from the spectral and difference kernels in items (2) and (4). **§1.2.1(1)(a,b), p. 13:** \(I=[-a,a]\) with \(a>0\), \(\varphi\) a compactly supported test, with support of norm strictly greater than \(1+\epsilon\) for some \(\epsilon>0\). **§1.2.1, p. 14, first unnumbered display:** \((A(\varphi)\psi)(x)=\int_{C_F}\varphi(g)\psi(g^{-1}x)\,d\bar\mu(g)\).
- **Terminology 4.3.2.1, p. 180, isotype display:** the eigenspace condition is \(\rho(h)\psi=\chi(h)\psi\). **§9.3.1, p. 419**, left-translation definition uses the inverse at the input; Definition 9.3.1.1, (9.3.1.1)–(9.3.1.2), regularizes this action by the Pettis integral. Lemma 9.3.1.3 (statement p. 419, proof p. 420) is the separate continuity claim for this regularization on the indicated test and completed spaces, including \(s=0\). The scalar calculation below does not check that lemma for arbitrary fields and isotypes.
- **Definition A.1.4.1, p. 542, (A.1.4.1)–(A.1.4.2):** the actual topological quotient by principal idèles, with the descended positive idelic norm and norm-one kernel. **Definition A.3.2.1, pp. 559–560 and (A.3.2.1):** class Haar \(\bar\mu\) uses counting on \(F^\times\) and the norm-factor measure \(dt/t\), with a prescribed norm-one volume. The calculation works for any class Haar, therefore in particular for that normalization; the same measure appears on both sides, not weighted measure or a Haar measure with a new scalar. The client uses the existing counting quotient measure with log-Lebesgue factor and does not compute the volume in (A.3.2.1).

## Checked scope

[`Theorems.IdeleClassConvolutionKernel`](../../Proofs/Theorems/IdeleClassConvolutionKernel.lean) works on `NumberField.IdeleClassGroup (𝓞 K) K` for every number field, with `ideleClassNorm` and `ideleClassNormOne` from the existing quotient. For continuous \(\varphi\) of compact support and continuous \(\psi\), the original integrand is continuous with compact support, so is integrable at each fixed \(x\). Set \(y=g^{-1}x\); its inverse is \(g=x/y\). Translation and inversion preserve this abelian Haar measure. Transporting integrability as well as the integral gives

\[
\int_{C_F}\varphi(g)\psi(g^{-1}x)\,d\bar\mu(g)
=\int_{C_F}\varphi(x/y)\psi(y)\,d\bar\mu(y).
\]

For any continuous norm-one character, the pointwise input condition \(\psi(h^{-1}y)=\chi(h)\psi(y)\) gives the same transformation law for the integral: commute the two inverse-left translations and pull the character value out of the integral. No projection or extension by zero is part of this calculation. The client below constructs such an input using the actual log splitting, a continuous log profile and the inverse character of the norm-one coordinate; it proves the condition rather than assuming it, and the input is nonzero when the profile is nonzero at log zero.

The norm homomorphism gives \(|x/y|_F=|x|_F/|y|_F\), with positive denominator. Topological support at norm \(>b\) gives vanishing when \(|x|_F\le b|y|_F\), including the boundary. Take \(b=1+\epsilon\) for the support gap, or just use \(b=1\) on the diagonal. The latter does not need to assume a quantitative gap. There is no width or degree hypothesis in either pointwise calculation.

## Remaining bridge

This is a kernel density against class Haar on continuous inputs, not yet the identification of this representative with the operator on all of \(W_I^{s,2}(C_F)(\chi|_{C_F^1})\). The existing [rational radial convolution](rational-radial-hilbert-convolution.md) gives a bounded action in the \(\mathbb Q\), trivial-isotype radial model, not the general comparison. A retry needs the actual general weighted isotype model, density of its continuous source tests and the bounded inverse-left regularization with agreement on those tests. With those inputs, a proposed route is Cauchy–Schwarz: if \(w\ge1\) is the actual symmetric-base squared-norm weight, then

\[
\left|\int \varphi(x/y)(f-g)(y)\,d\bar\mu(y)\right|
\le \|\varphi\|_{L^2(\bar\mu)}\|f-g\|_{L^2(w\bar\mu)}.
\]

Here the first norm is independent of \(x\) by the same Haar invariance, and is finite for a continuous compactly supported kernel. Apply the bound to test approximants to obtain a uniform pointwise limit of the kernel integrals. Boundedness of the same regularization gives weighted \(L^2\) convergence of the outputs, hence an almost-everywhere convergent subsequence; identify its limit with the pointwise representative. That passage to the actual completion is not formalized here. Diagonal and gap vanishing alone do not establish quotient descent, a trace-class estimate, or an operator trace identity.

## Reproduce the writer checks

Build `lake build --wfail +Theorems.IdeleClassConvolutionKernel +Theorems.IdeleClassWeil`. Both modules built on the writer workspace (8137 jobs). With the same two ordinary imports below, run `#check @Name` and `#print axioms Name` for each fully qualified declaration in the receipt; each uses exactly `propext`, `Classical.choice`, `Quot.sound`. Run the following client with `lake env lean` from the built workspace.

```lean
import Theorems.IdeleClassConvolutionKernel
import Theorems.IdeleClassWeil

open Masullo MeasureTheory NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "C₁" => ideleClassNormOne (K := K)
local notation "I₁" => ideleNormOne (K := K)
local notation "L" => Multiplicative ℝ
local notation "τ" v => ideleClassLogSplit (ideleClassLogSection v) (ideleClassLogNorm_section v)

private def profile (v : InfinitePlace K) (p : L → ℂ) (χ : PontryaginDual C₁) (y : C) : ℂ :=
  p (((τ v).symm y).1) * (χ (((τ v).symm y).2)⁻¹ : ℂ)

private theorem profile_continuous (v : InfinitePlace K) {p : L → ℂ} (hp : Continuous p)
    (χ : PontryaginDual C₁) : Continuous (profile v p χ) := by
  unfold profile
  exact (hp.comp (τ v).symm.continuous.fst).mul
    (continuous_subtype_val.comp (χ.continuous.comp (τ v).symm.continuous.snd.inv))

private theorem profile_isotype (v : InfinitePlace K) (p : L → ℂ) (χ : PontryaginDual C₁)
    (h : C₁) (y : C) : profile v p χ ((h : C)⁻¹ * y) = (χ h : ℂ) * profile v p χ y := by
  have hh : (τ v) (1, h) = (h : C) := by
    rw [ideleClassLogSplit_apply, map_one]
    exact one_mul (h : C)
  have hs : (τ v).symm (h : C) = (1, h) := (τ v).toEquiv.symm_apply_eq.mpr hh.symm
  unfold profile
  rw [map_mul, map_inv, hs]
  change p (1⁻¹ * ((τ v).symm y).1) *
    (χ ((h⁻¹ * ((τ v).symm y).2)⁻¹) : ℂ) =
      (χ h : ℂ) * (p (((τ v).symm y).1) * (χ (((τ v).symm y).2)⁻¹ : ℂ))
  simp only [inv_one, one_mul, mul_inv_rev, inv_inv, map_mul, Circle.coe_mul]
  ac_rfl

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

-- The actual counting quotient Haar; the input is a log profile times the inverse
-- character of the norm-one coordinate. Exercise the substitution and equivariance.
example (ν : Measure I₁) [ν.IsHaarMeasure] (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ a, ideleIdealClassNormOne (r a) = a) (hfin : ν (ideleFundamentalDomain v r) < ⊤)
    {φ : C → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {p : L → ℂ} (hp : Continuous p) (hp₁ : p 1 ≠ 0)
    (χ : PontryaginDual C₁) (h : C₁) (x : C) :
    let μ := ideleClassQuotientMeasure ν v r
    let ψ := profile v p χ
    ψ 1 ≠ 0 ∧ Integrable (fun g ↦ φ g * ψ (g⁻¹ * x)) μ ∧
    Integrable (fun y ↦ φ (x / y) * ψ y) μ ∧
    ((∫ g, φ g * ψ (g⁻¹ * x) ∂μ) = ∫ y, φ (x / y) * ψ y ∂μ) ∧
    (∫ y, φ (((h : C)⁻¹ * x) / y) * ψ y ∂μ) = (χ h : ℂ) * ∫ y, φ (x / y) * ψ y ∂μ := by
  intro μ ψ
  let : μ.IsHaarMeasure := ideleClassQuotientMeasure_isHaarMeasure ν v r hr hfin
  have hnonzero : ψ 1 ≠ 0 := by
    change profile v p χ 1 ≠ 0
    simpa [profile] using hp₁
  obtain ⟨hi, hj, he⟩ := ideleClass_convolution_kernel μ hφ hc (profile_continuous v hp χ) x
  exact ⟨hnonzero, hi, hj, he, ideleClass_convolution_kernel_isotype μ hφ hc
    (profile_continuous v hp χ) χ (profile_isotype v p χ) h x⟩

-- The upper boundary of the gap is included; diagonal only needs the weaker
-- support bound, with no explicit ε or Haar hypotheses in either support endpoint.
example {φ : C → ℂ} {ε : ℝ} (hφ : tsupport φ ⊆ {g | 1 + ε < ideleClassNorm g})
    {x y : C} (hxy : ideleClassNorm x = (1 + ε) * ideleClassNorm y) : φ (x / y) = 0 :=
  ideleClass_convolution_kernel_eq_zero_of_norm_le hφ hxy.le

example {φ : C → ℂ} (hφ : tsupport φ ⊆ {g | 1 < ideleClassNorm g}) (x : C) : φ (x / x) = 0 :=
  ideleClass_convolution_kernel_diagonal hφ x
```
