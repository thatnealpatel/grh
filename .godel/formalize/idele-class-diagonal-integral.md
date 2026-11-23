# Integrated class-Haar diagonal cancellation, conditional on spectral recovery

Chapter 01, proof key `38cb06c5a9befac2d4020b456deffc73a255af4146bef015478809b13b10e692`, revision `c75e0feabdadb014cd3b27b9d306288654fb37d5524c59cfa07af9d5d160a671`. [Receipt](38cb06c5a9befac2d4020b456deffc73a255af4146bef015478809b13b10e692-c75e0feabdadb014cd3b27b9d306288654fb37d5524c59cfa07af9d5d160a671.json). Writer base `85933a3338cd4d17662c07b9f27a3e6e818a6d38`, one unrelated fixed-band rational trace commit after request tip `021fb6f55c65487e32d54130f5e1b0ebeda089f7`. Owning exact-candidate check session: `01a20690-c4cd-7998-b70a-606f6bbe1fa7`. The build and client below are writer checks, not integration, independent review, or adoption.

## Printed claim and argument

Verified the 6,756,996-byte PDF of Masullo, *The Music of the Primes*, against the [edition pin](../sources/masullo/README.md), SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. Inspected rendered page rasters and display crops, using raster OCR for prose and extraction for navigation and notation. Printed page equals the one-based PDF ordinal at all locators below.

- **§1.2.1, p. 13, (1)(a,b) and (2):** the Hardy–Sobolev completion is of the half-twisted exact sequence on a fixed norm-one isotype. The base is \(I=[-a,a]\) with \(a>0\), the test \(\varphi\in\mathcal D(C_F)\) has compact support in \(\{|g|_F>1+\epsilon\}\) for some \(\epsilon>0\), and (2) takes degree \(s=0\). Its prose restricts the zero sum to \(L(\rho,\chi)=0\) with \(-a<\operatorname{Re}(\rho-1/2)<a\), with full multiplicities \(N(\rho)\). Do not take the ensuing positive-degree edge rule as part of the degree-zero sum.
- **§1.2.1, p. 15, unnumbered display after “We have the main Trace Formula”:** using tildes for the smoothed diagonals, the printed claim is
  \[
  \int_{C_F}\widetilde k_{\mathrm{geom},I,\varphi}(x,x)\,d\bar\mu(x)
  =-\int_{C_F}\widetilde k_{\mathrm{spec},I,\varphi}(x,x)\,d\bar\mu(x)
  =-\sum_{\rho,I}N(\rho)M(\varphi)(\chi|\cdot|_F^{\rho-1/2}).
  \]
  The summation domain comes from p. 13(2); (4.4.1.1), p. 189, defines the Mellin moment with the quasi-character multiplying the test, not its inverse. The prose immediately after the p. 15 display says the diagonal is defined by differentiation, rather than read off an arbitrary product-a.e. kernel representative.
- **Argument on pp. 14–15:** the opening p. 14 display uses inverse-left convolution; the transpose calculation gives the Mellin entry on each diagonal of the claimed zero blocks. The unnumbered finite-rank expansion uses the transpose-convolved jets as input rows. The p. 14 “Since \(\delta\)” paragraph before (1.2.1.1) instead writes bare rows, so its product-kernel assertion cannot simply be read as the trace-norm expansion for the test-dependent operator. The opening p. 15 lift projects the **outputs** orthogonally away from the completed half-twisted theta space. Item (3) asserts diagonal vanishing of the regular kernel \(\varphi(xy^{-1})\); item (4) subtracts the lifted spectral kernel from this regular kernel and appeals to nuclearity, maximal estimates and differentiation for smoothability. The subtraction explains the first minus sign; spectral trace identification and the zero-block sum are additional steps.
- **Measure and boxes:** Definition A.1.4.1, (A.1.4.1)–(2), p. 542, is the quotient by principal idèles with descended norm. Definition A.3.2.1, pp. 559–560, uses counting on \(F^\times\), \(dt/t\) on the norm factor, and the norm-one volume in (A.3.2.1). Definition 12.1.1.1, (12.1.1.1), p. 498, divides the integral over \(xU_n\) by \(\mu(U_n)\) and takes its finite limit. The opening of p. 499 uses the product boxes of the same sequence. Theorem 12.1.1.2(1), (12.1.1.2), p. 499, assumes genuine \(D'\) boxes and trace class on \(L^2(\lambda)\), \(\lambda=w\mu\) with continuous positive \(w\). It averages the kernel relative to \(\lambda\) with Haar, but integrates the resulting diagonal against \(\lambda\). This is not directly the Haar-relative subtraction and integral of p. 15.

## Checked partial proof

[`Theorems.IdeleClassDiagonalIntegral`](../../Proofs/Theorems/IdeleClassDiagonalIntegral.lean) imports the byte-unchanged [`Theorems.IdeleClassDiagonalAverage`](../../Proofs/Theorems/IdeleClassDiagonalAverage.lean). The new public endpoint is `Masullo.ideleClassDiagonalAverage_sub_integrable_integral_eq_neg`. It uses `NumberField.IdeleClassGroup (𝓞 K) K`, the actual norm, the original sequence of Borel shrinking sets \(U_n\), product boxes \(B_n(x)=(xU_n)\times(xU_n)\), the same normalized average with \(\mu\otimes\mu\), and the filter `atTop`. For class Haar the existing mass lemma gives \((\mu\otimes\mu)(B_n(x))=\mu(U_n)^2\). The analytic application uses positive finite box mass and locally integrable kernels; the implication itself also holds for the existing totalized averages. No change of Haar normalization or new weight is made.

Assume a supplied Haar-integrable representative \(d_{\mathrm{spec}}\) and that the spectral box averages of the given kernel \(k\) converge to \(d_{\mathrm{spec}}(x)\) for \(\mu\)-a.e. center \(x\). On that same conull set use the [accepted pointwise transfer](idele-class-diagonal-average.md), `ideleClassDiagonalAverage_sub_tendsto_iff`: the support gap makes the regular term identically zero on every sufficiently small box at that center. Thus the geometric boxes for the *actual difference* \((y,z)\mapsto\varphi(y/z)-k(y,z)\) converge to \(d_{\mathrm{geom}}(x)=-d_{\mathrm{spec}}(x)\). The theorem returns this explicit representative with its a.e. recovery, its \(L^1(\mu)\) integrability by negation, and the first integral equality for that same representative by `integral_neg`. If the latter diagonal is assigned other values off the set of regular centers, it agrees a.e. by uniqueness of limits. No limit is interchanged with an integral, and integrability is not inferred from a totalized integral equality. Haar invariance is not needed in the implication, so the endpoint permits every Borel measure on the actual quotient and applies in particular to the source's class Haar. Character, width and degree enter only in supplying the spectral hypothesis; none has been changed to make that hypothesis hold.

## Residual and retry

No identification of \(k\) with the Haar kernel of the actual half-twisted degree-zero quotient convolution is checked. Supply a trace-class proof on that actual fixed-isotype, positive-width quotient and a trace-ideal convergent regularized expansion (or another kernel identification) of its orthogonal lift \(S B Q=P A(\varphi)\). The [operator-lift handoff](rational-radial-hilbert-operator-lift.md) explains why lifting the outputs does not restore missing transpose-convolved input rows or justify switching to \(A(\varphi)P\). The [regular Haar kernel](idele-class-convolution-kernel.md) and [pointwise L² action](idele-class-convolution-kernel-l2.md) do not supply this spectral identification. Theorem 10.3.2.1, pp. 453–455, assumes \(s>1\); (10.4.2.20), pp. 463–464, cites that theorem and concerns convolution **after** projection. Theorem 12.1.1.3, pp. 502–503, takes \(s\ge3\) and uses the singleton-base kernels of (10.4.3.26)–(27), p. 470. None supplies the p. 15 degree-zero spectral input directly.

Obtain a.e. diagonal recovery and absolute Haar integrability on the same genuine shrinking boxes, with the Haar density \(k_H(x,y)=w(y)k_\lambda(x,y)\) if starting with a relative kernel \(k_\lambda\) on \(L^2(\lambda)\). For example, a summable rank-one expansion in the equivalent unweighted \(L^2(\mu)\) and a uniform \(L^2\) bound on the maximal averages of absolute values can control its diagonal tails and the continuous weight ratio on shrinking boxes. Product-\(L^2\) convergence alone is not enough on the product-null diagonal. See the [spectral audit](../obligations/trace-spectral.md) for the \(\mathbb Q(i)\) obstruction to the printed global boxes and the conditional Haar diagonal argument. Then identify the spectral Haar integral with the trace of the correct lift and prove exhaustion by the *interior* zero blocks with the printed full multiplicities and shift (account separately for possible edge zeros). Neither the higher-degree results nor the [toy Poisson correction](../walk/toy-poisson-normalization.md) and [toy support vanishing](../walk/toy-trace-support-vanishing.md) give that operator trace or zero exhaustion.

## Reproduce the writer checks

With Lean 4.36.0, `lake build --wfail +Theorems.IdeleClassDiagonalIntegral +Theorems.IdeleClassWeil` passed (8141 jobs). In a fresh file importing both modules together, `#check @Masullo.ideleClassDiagonalAverage_sub_integrable_integral_eq_neg` and `#print axioms Masullo.ideleClassDiagonalAverage_sub_integrable_integral_eq_neg` passed under `lake env lean -D warningAsError=true`. The elaborated binders and conclusion are as described above; the only transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Run the following separate ordinary-import client with `lake env lean -D warningAsError=true`. It passed using the existing counting-quotient Haar with log-Lebesgue norm factor, obtains integrability of the supplied spectral representative from an actual `Lp ℂ 1 μ` input, and uses all three outputs to get geometric `MemLp`, geometric recovery, and integrated cancellation. It neither chooses a mock operator nor verifies the spectral input. The normalization is the same on both sides; this does not compute the volume in (A.3.2.1).

```lean
import Theorems.IdeleClassDiagonalIntegral
import Theorems.IdeleClassWeil

noncomputable section

open Filter Masullo MeasureTheory NumberField Set
open scoped Masullo Topology

variable {K : Type*} [Field K] [NumberField K]
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

-- Actual counting quotient Haar; the spectral kernel and convergence remain inputs.
example (ν : Measure I₁) [ν.IsHaarMeasure] (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ a, ideleIdealClassNormOne (r a) = a) (hfin : ν (ideleFundamentalDomain v r) < ⊤)
    {φ : C → ℂ} {ε : ℝ} (hε : 0 < ε) (hφ : tsupport φ ⊆ {g | 1 + ε < ideleClassNorm g})
    (U : ℕ → Set C) (hopen : ∀ n, IsOpen (U n))
    (hshrink : ∀ V ∈ 𝓝 (1 : C), ∀ᶠ n in atTop, U n ⊆ V) (k : C × C → ℂ) :
    let μ := ideleClassQuotientMeasure ν v r
    ∀ s : Lp ℂ 1 μ,
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ ideleClassDiagonalAverage μ (U n) k x) atTop (𝓝 (s x))) →
      let g : C → ℂ := fun x ↦ -s x
      MemLp g 1 μ ∧
        (∀ᵐ x ∂μ, Tendsto
          (fun n ↦ ideleClassDiagonalAverage μ (U n) (fun p ↦ φ (p.1 / p.2) - k p) x)
          atTop (𝓝 (g x))) ∧
        (∫ x, g x + s x ∂μ) = 0 := by
  intro μ s hlim g
  let : μ.IsHaarMeasure := ideleClassQuotientMeasure_isHaarMeasure ν v r hr hfin
  have hs : Integrable (fun x ↦ s x) μ := L1.integrable_coeFn s
  obtain ⟨hg, hgeom, heq⟩ := ideleClassDiagonalAverage_sub_integrable_integral_eq_neg μ
    hε hφ U (fun n ↦ (hopen n).measurableSet) hshrink k (fun x ↦ s x) hs hlim
  refine ⟨memLp_one_iff_integrable.mpr hg, hgeom, ?_⟩
  rw [integral_add hg hs, heq, neg_add_cancel]
```
