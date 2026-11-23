# Class-Haar diagonal cancellation on shrinking boxes

Chapter 01, proof key `442a63c93f8ac5ece067f21dfcfd2252280ad1152203bb3468becfd7b63668e3`, revision `eadac3a1be18b2b4dfe52afdf55a37433b193175a4cc27e69ba1ea382738fe59`. [Receipt](442a63c93f8ac5ece067f21dfcfd2252280ad1152203bb3468becfd7b63668e3-eadac3a1be18b2b4dfe52afdf55a37433b193175a4cc27e69ba1ea382738fe59.json). Writer base `c1d9906c831ff0c9380c9bacd83d5b66bcd67c51`; owning session `01a2066e-25af-7f25-bd24-9cd236059eeb` records final candidate checks and disposition separately.

## Printed claim and conventions

Verified the local 6,756,996-byte PDF of Masullo, *The Music of the Primes*, against the [edition pin](../sources/masullo/README.md): SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. Read rendered page rasters with OCR and focused pixel crops, using extraction for navigation and notation. Printed page = one-based PDF ordinal at the following locators.

- **§1.2.1, pp. 13–15.** In (1)(a,b), the base is symmetric of positive width, and the compact test has a strict gap above norm one (support in the region above \(1+\epsilon\) for some \(\epsilon>0\)). The sequence uses the half twist and a fixed norm-one isotype; (2) takes degree \(s=0\). On p. 14, the finite-rank expansion uses the action of the transpose on the input jets, but the following “Since \(\delta\)” paragraph before (1.2.1.1) displays bare rows. The p. 15 lift paragraph projects lifted **output vectors** to the orthogonal complement of the closed theta isotype. Item (3) uses the regular class-Haar convolution kernel \(\varphi(xy^{-1})\) and states its diagonal vanishing. **Item (4), the assigned passage**, defines \(k_{\rm geom,I,\varphi}(x,y)=\varphi(xy^{-1})-k_{\rm spec,I,\varphi}(x,y)\) and asserts smoothability along the diagonal by the maximal and differentiation theorems, citing nuclearity of \(A_{\rm spec,I}(\varphi)\). The ensuing trace formula is a separate claim.
- **Class group and averaging.** Definition A.1.4.1, (A.1.4.1)–(A.1.4.2), p. 542, uses the actual quotient by principal idèles and the descended positive norm. Definition A.3.2.1, (A.3.2.1), pp. 559–560, uses the counting quotient and the norm-factor measure \(dt/t\). Definition 12.1.1.1, (12.1.1.1), p. 498, divides the Haar integral on each translate \(xU_n\) by \(\mu(U_n)\) and uses its finite limit on regular points. It recalls the positive finite masses, nesting and containment of a tail in each unit neighborhood of a \(D'\)-sequence. The top of p. 499 explicitly uses \(U_n\times U_n\) for kernels. Smoothability here means existence of such a finite limit on the indicated diagonal, not smoothness of a representative.
- **Conditional diagonal theorem and density.** Theorem 12.1.1.2(1), (12.1.1.2), p. 499, starts with a second-countable locally compact Hausdorff abelian group, Haar \(\mu\), \(D'\) boxes, continuous positive \(w\), and a trace-class \(T\) on \(L^2(w\mu)\). The averaging is with Haar, but its Hilbert–Schmidt kernel \(k_\lambda\) is **relative to \(\lambda=w\mu\)**, and the asserted diagonal integrability and trace are relative to \(\lambda\). On p. 500 the multiplication isometry to unweighted \(L^2\) transforms the kernel by \(\sqrt{w(x)}\sqrt{w(y)}\); p. 501 uses the strong maximal inequality for (1) and separately invokes Corollary A.5.4.3 for the multiplier assertion (12.1.1.13). Neither the relative kernel nor its measure can be substituted directly into the subtraction on p. 15. For the introductory weight, compare p. 14's (1.2.1.1) with Proposition 9.2.2.11 and (9.2.2.41)–(42), p. 417, for the reciprocal weight on input densities.
- **No transfer at degree zero.** Theorem 10.3.2.1, pp. 453–455, assumes \(s>1\) in the quotient nuclearity result. Theorem 10.4.2.8, pp. 463–464, prints \(s\ge0\) and \(\alpha\ge0\), but its (10.4.2.20) is a cutoff trace for convolution after projection with a quotient trace from Theorem 10.3.2.1. Even with the uniform lifted-vector bound (10.4.2.24), this invocation does not supply the needed trace-class proof and Haar representative at \(s=0\); p. 464 ends the proof with footnote 8, “Return here and complete proof.” Theorem 12.1.1.3(1), pp. 502–503, prints \(s\ge3\) and uses the kernels of Definition 10.4.3.2, (10.4.3.26)–(27), p. 470, in the singleton-base subsection §10.4.3.1. Neither a lowered degree nor a transfer from the singleton base to a positive-width interval is checked here.

## Lean result

[`Theorems.IdeleClassDiagonalAverage`](../../Proofs/Theorems/IdeleClassDiagonalAverage.lean) defines the box \(B_n(x)=(xU_n)\times(xU_n)\) and its average using the product of the **same** measure with itself. For class Haar, translation invariance and the product formula give mass \(\mu(U_n)^2\). No separate Haar scaling is computed. The proof uses only the Borel and shrinking parts of the \(D'\) hypotheses, not the doubling estimate, and works for any Borel measure in the cancellation and limit statements. At the analytic application, positive finite box mass and integrability on the box make the expressions actual normalized integrals; the Lean statements in isolation are about totalized integrals and division.

At each center \(x\), the set of \((u,v)\) with \(N(xu)<(1+\epsilon)N(xv)\) is open and contains \((1,1)\), since \(N(x)>0\). Take a product neighborhood inside it and use shrinking for both factors at once. The [accepted support result](idele-class-convolution-kernel.md) gives \(\varphi(y/z)=0\) **on the entire translated box** for all sufficiently large \(n\). Hence the average of the difference equals the negative average of \(k\), by congruence on the restricted measure and compatibility with negation, without distributing integration over a possibly nonintegrable subtraction. `Masullo.ideleClassDiagonalAverage_sub_eventually_eq_neg` checks this equality for all centers and arbitrary complex \(k\); `Masullo.ideleClassDiagonalAverage_sub_tendsto_iff` checks the equivalence of the two specified finite limits with opposite signs. Notably, this does not yield the existence of either limit from product-almost-everywhere regularity. It neither names a spectral kernel nor assumes an operator conclusion as a hypothesis.

## Remaining analytic inputs

First identify the actual degree-zero weighted isotype and its quotient convolution \(B\), prove it trace class, and identify the lift \(S B Q=P A\) by the **Haar** kernel built from regularized transpose rows. The accepted [operator lift](rational-radial-hilbert-operator-lift.md) and [bare-kernel finding](1bca11d346543ed7f4c4056797b6d63ec3d8969cef608d37d711ca9fa2b248f0-d951d8290be403b35931c65f86b9a325379b6b724d20ed4f81dd09018025aa9f.json) explain why bare rows and \(A P\) cannot simply be substituted. In particular, bounds on individual vectors or on Mellin coefficients alone are not a trace-class estimate for the completed convolution. The accepted toy Poisson and support notes give scalar identities, not trace-ideal control.

Next choose genuine \(D'\) boxes (or prove the necessary stronger-than-product differentiation for the actual boxes). The [spectral audit](../obligations/trace-spectral.md) gives a \(\mathbb Q(i)\) angular obstruction to using the global boxes of Lemma A.5.2.17(1), p. 577, as general trace-diagonal boxes: they need not shrink. This is not a refutation of the general diagonal theorem for genuine \(D'\) boxes or a counterexample to the specific spectral assertion of item (4).

A sufficient diagonal argument, **not formalized here**, starts from the unweighted kernel \(k_U=\sqrt{w(x)w(y)}k_\lambda\). From a rank-one expansion \(\sum_j f_j(y)\overline{g_j(z)}\) with \(\sum_j\|f_j\|_2\|g_j\|_2<\infty\), one needs one-factor differentiation and a uniform \(L^2\) bound for \(M h=\sup_{n\ge n_0} A_n|h|\) on the chosen sequence, with \(A_n\) the one-factor averages. Tonelli and Cauchy–Schwarz then make \(\sum_j (M f_j)(M g_j)\) integrable, bounding the diagonal averages of absolute rank-one tails uniformly in \(n\). Finite sums differentiate at almost every center by the one-factor theorem and Fubini; uniform tail control permits passage to the full kernel. The Haar density for \(T\) itself is \(k_H=w(y)k_\lambda=\sqrt{w(y)/w(x)}\,k_U\), with \(x\) output and \(y\) input. The weight ratio tends uniformly to 1 on the shrinking boxes at each fixed center by positivity and continuity; the bound on the absolute averages controls the error. Product \(L^2\) convergence alone would not give any of this on a product-null diagonal. In particular the *limsup* in (A.5.3.16), p. 582, is not the tail supremum in this sufficient estimate, and the continuity argument in (A.5.4.16)–(17), p. 585, drops the normalized absolute-average factor. Neither is used as an imported diagonal proof.

## Reproduce the writer checks

Run `lake build --wfail +Theorems.IdeleClassDiagonalAverage +Theorems.IdeleClassWeil +Lemmas.IdeleFiniteStageMeasure` (8139 jobs, Lean 4.36.0). In a fresh scratch file importing the first two modules together, run `#check @Name` and `#print axioms Name` for every fully qualified receipt declaration, using `lake env lean -D warningAsError=true`. Each of the five reports lists exactly `propext`, `Classical.choice`, `Quot.sound`.

The ordinary-import client below also passed `lake env lean -D warningAsError=true`. It proves a nonzero test limit by applying the mass formula and limit transfer, using the existing counting quotient with log-Lebesgue factor, not assuming the spectral-side limit as a premise. It is not a model of the manuscript's spectral operator. The open relatively compact neighborhoods make the box mass positive and finite. The test kernel is constant, so is integrable there; on the small boxes the difference is also constant by the proved cancellation. No numeric adelic volume is needed.

```lean
import Theorems.IdeleClassDiagonalAverage
import Theorems.IdeleClassWeil
import Lemmas.IdeleFiniteStageMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Bases

noncomputable section

open Masullo MeasureTheory NumberField Set Filter Topology
open scoped ENNReal Masullo Pointwise Topology

variable {K : Type*} [Field K] [NumberField K]
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "I₁" => ideleNormOne (K := K)

variable [MeasurableSpace (IdeleClassGroup (𝓞 K) K)] [BorelSpace (IdeleClassGroup (𝓞 K) K)]
  [MeasurableSpace (ideleNormOne (K := K))] [BorelSpace (ideleNormOne (K := K))]
  [MeasurableSpace (ideleClassNormOne (K := K))] [BorelSpace (ideleClassNormOne (K := K))]

-- Actual counting quotient Haar, arbitrary center, open relatively compact
-- shrinking boxes, and a nonzero locally integrable test kernel (not a
-- claim that the manuscript's spectral kernel is constant).
example (ν : Measure I₁) [ν.IsHaarMeasure] (v : InfinitePlace K) (r : ClassGroup (𝓞 K) → I₁)
    (hr : ∀ a, ideleIdealClassNormOne (r a) = a) (hfin : ν (ideleFundamentalDomain v r) < ⊤)
    {φ : C → ℂ} {ε : ℝ} (hε : 0 < ε) (hφ : tsupport φ ⊆ {g | 1 + ε < ideleClassNorm g})
    (U : ℕ → Set C) (hopen : ∀ n, IsOpen (U n)) (hone : ∀ n, 1 ∈ U n)
    (hcompact : ∀ n, IsCompact (closure (U n)))
    (hshrink : ∀ V ∈ 𝓝 (1 : C), ∀ᶠ n in atTop, U n ⊆ V) (x : C) :
    let μ := ideleClassQuotientMeasure ν v r
    Tendsto (fun n ↦ ideleClassDiagonalAverage μ (U n) (fun p ↦ φ (p.1 / p.2) - 3) x)
      atTop (𝓝 (-3 : ℂ)) := by
  intro μ
  let : μ.IsHaarMeasure := ideleClassQuotientMeasure_isHaarMeasure ν v r hr hfin
  let : SecondCountableTopology I := secondCountable_ideleGroup K
  let : SecondCountableTopology C :=
    (QuotientGroup.isOpenQuotientMap_mk : IsOpenQuotientMap
      (QuotientGroup.mk : I → C)).secondCountableTopology
  have hconst (n : ℕ) : ideleClassDiagonalAverage μ (U n) (fun _ ↦ (3 : ℂ)) x = 3 := by
    have hUpos := (hopen n).measure_pos μ ⟨1, hone n⟩
    have hUlt : μ (U n) < ⊤ :=
      (measure_mono subset_closure).trans_lt ((hcompact n).measure_lt_top (μ := μ))
    have hB : (μ.prod μ) (ideleClassDiagonalBox x (U n)) = μ (U n) ^ 2 :=
      ideleClassDiagonalBox_measure μ x (U n)
    have hmass : 0 < (μ.prod μ).real (ideleClassDiagonalBox x (U n)) := by
      rw [measureReal_def, hB, pow_two, ENNReal.toReal_mul]
      exact mul_pos (ENNReal.toReal_pos hUpos.ne' hUlt.ne) (ENNReal.toReal_pos hUpos.ne' hUlt.ne)
    have hcast : ((μ.prod μ).real (ideleClassDiagonalBox x (U n)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hmass.ne'
    rw [ideleClassDiagonalAverage, setIntegral_const, Complex.real_smul, mul_comm, mul_div_cancel_right₀ _ hcast]
  have hs : Tendsto (fun n ↦ ideleClassDiagonalAverage μ (U n) (fun _ ↦ (3 : ℂ)) x)
      atTop (𝓝 3) := tendsto_const_nhds.congr (fun n ↦ (hconst n).symm)
  exact (ideleClassDiagonalAverage_sub_tendsto_iff μ hε hφ U
    (fun n ↦ (hopen n).measurableSet) hshrink (fun _ ↦ 3) x 3).mpr hs

```
